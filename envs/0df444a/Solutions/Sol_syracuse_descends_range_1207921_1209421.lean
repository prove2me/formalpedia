-- Prove2me | solution 1 for syracuse_descends_range_1207921_1209421
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:48.243261+00:00
-- url     : https://prove2.me/submissions/84e4f57b-e4f7-4c0c-8fc3-9bc23aaba509

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


theorem B1359877 : Blo 1207921 1359877 := bbase (se 4 (by rfl) ⟨127488, by rfl⟩ : syracuseStep 1359877 = 254977) (by norm_num)
theorem B2719781 : Blo 1207921 2719781 := bbase (se 4 (by rfl) ⟨254979, by rfl⟩ : syracuseStep 2719781 = 509959) (by norm_num)
theorem B1359913 : Blo 1207921 1359913 := bbase (se 2 (by rfl) ⟨509967, by rfl⟩ : syracuseStep 1359913 = 1019935) (by norm_num)
theorem B2326573 : Blo 1207921 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B2293829 : Blo 1207921 2293829 := bbase (se 4 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 2293829 = 430093) (by norm_num)
theorem B1359949 : Blo 1207921 1359949 := bbase (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) (by norm_num)
theorem B2719853 : Blo 1207921 2719853 := bbase (se 3 (by rfl) ⟨509972, by rfl⟩ : syracuseStep 2719853 = 1019945) (by norm_num)
theorem B2039917 : Blo 1207921 2039917 := bbase (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) (by norm_num)
theorem B1359985 : Blo 1207921 1359985 := bbase (se 2 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 1359985 = 1019989) (by norm_num)
theorem B3440789 : Blo 1207921 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B1360021 : Blo 1207921 1360021 := bbase (se 6 (by rfl) ⟨31875, by rfl⟩ : syracuseStep 1360021 = 63751) (by norm_num)
theorem B2580653 : Blo 1207921 2580653 := bbase (se 3 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 2580653 = 967745) (by norm_num)
theorem B2719925 : Blo 1207921 2719925 := bbase (se 5 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 2719925 = 254993) (by norm_num)
theorem B1360057 : Blo 1207921 1360057 := bbase (se 2 (by rfl) ⟨510021, by rfl⟩ : syracuseStep 1360057 = 1020043) (by norm_num)
theorem B2040005 : Blo 1207921 2040005 := bbase (se 4 (by rfl) ⟨191250, by rfl⟩ : syracuseStep 2040005 = 382501) (by norm_num)
theorem B1360093 : Blo 1207921 1360093 := bbase (se 3 (by rfl) ⟨255017, by rfl⟩ : syracuseStep 1360093 = 510035) (by norm_num)
theorem B4587749 : Blo 1207921 4587749 := bbase (se 4 (by rfl) ⟨430101, by rfl⟩ : syracuseStep 4587749 = 860203) (by norm_num)
theorem B4079861 : Blo 1207921 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B4653301 : Blo 1207921 4653301 := bbase (se 5 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 4653301 = 436247) (by norm_num)
theorem B2719997 : Blo 1207921 2719997 := bbase (se 3 (by rfl) ⟨509999, by rfl⟩ : syracuseStep 2719997 = 1019999) (by norm_num)
theorem B1360129 : Blo 1207921 1360129 := bbase (se 2 (by rfl) ⟨510048, by rfl⟩ : syracuseStep 1360129 = 1020097) (by norm_num)
theorem B1360165 : Blo 1207921 1360165 := bbase (se 4 (by rfl) ⟨127515, by rfl⟩ : syracuseStep 1360165 = 255031) (by norm_num)
theorem B2580797 : Blo 1207921 2580797 := bbase (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) (by norm_num)
theorem B2720069 : Blo 1207921 2720069 := bbase (se 4 (by rfl) ⟨255006, by rfl⟩ : syracuseStep 2720069 = 510013) (by norm_num)
theorem B2040133 : Blo 1207921 2040133 := bbase (se 4 (by rfl) ⟨191262, by rfl⟩ : syracuseStep 2040133 = 382525) (by norm_num)
theorem B1360201 : Blo 1207921 1360201 := bbase (se 2 (by rfl) ⟨510075, by rfl⟩ : syracuseStep 1360201 = 1020151) (by norm_num)
theorem B5808485 : Blo 1207921 5808485 := bbase (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) (by norm_num)
theorem B1360237 : Blo 1207921 1360237 := bbase (se 3 (by rfl) ⟨255044, by rfl⟩ : syracuseStep 1360237 = 510089) (by norm_num)
theorem B2720141 : Blo 1207921 2720141 := bbase (se 3 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 2720141 = 1020053) (by norm_num)
theorem B1360273 : Blo 1207921 1360273 := bbase (se 2 (by rfl) ⟨510102, by rfl⟩ : syracuseStep 1360273 = 1020205) (by norm_num)
theorem B2040221 : Blo 1207921 2040221 := bbase (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) (by norm_num)
theorem B1360309 : Blo 1207921 1360309 := bbase (se 5 (by rfl) ⟨63764, by rfl⟩ : syracuseStep 1360309 = 127529) (by norm_num)
theorem B2720213 : Blo 1207921 2720213 := bbase (se 7 (by rfl) ⟨31877, by rfl⟩ : syracuseStep 2720213 = 63755) (by norm_num)
theorem B1360345 : Blo 1207921 1360345 := bbase (se 2 (by rfl) ⟨510129, by rfl⟩ : syracuseStep 1360345 = 1020259) (by norm_num)
theorem B1360381 : Blo 1207921 1360381 := bbase (se 3 (by rfl) ⟨255071, by rfl⟩ : syracuseStep 1360381 = 510143) (by norm_num)
theorem B2720285 : Blo 1207921 2720285 := bbase (se 3 (by rfl) ⟨510053, by rfl⟩ : syracuseStep 2720285 = 1020107) (by norm_num)
theorem B2040349 : Blo 1207921 2040349 := bbase (se 3 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 2040349 = 765131) (by norm_num)
theorem B1360417 : Blo 1207921 1360417 := bbase (se 2 (by rfl) ⟨510156, by rfl⟩ : syracuseStep 1360417 = 1020313) (by norm_num)
theorem B1360453 : Blo 1207921 1360453 := bbase (se 4 (by rfl) ⟨127542, by rfl⟩ : syracuseStep 1360453 = 255085) (by norm_num)
theorem B2720357 : Blo 1207921 2720357 := bbase (se 4 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 2720357 = 510067) (by norm_num)
theorem B1360489 : Blo 1207921 1360489 := bbase (se 2 (by rfl) ⟨510183, by rfl⟩ : syracuseStep 1360489 = 1020367) (by norm_num)
theorem B2040437 : Blo 1207921 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B1360525 : Blo 1207921 1360525 := bbase (se 3 (by rfl) ⟨255098, by rfl⟩ : syracuseStep 1360525 = 510197) (by norm_num)
theorem B4080293 : Blo 1207921 4080293 := bbase (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) (by norm_num)
theorem B2720429 : Blo 1207921 2720429 := bbase (se 3 (by rfl) ⟨510080, by rfl⟩ : syracuseStep 2720429 = 1020161) (by norm_num)
theorem B1360561 : Blo 1207921 1360561 := bbase (se 2 (by rfl) ⟨510210, by rfl⟩ : syracuseStep 1360561 = 1020421) (by norm_num)
theorem B1360597 : Blo 1207921 1360597 := bbase (se 7 (by rfl) ⟨15944, by rfl⟩ : syracuseStep 1360597 = 31889) (by norm_num)
theorem B2720501 : Blo 1207921 2720501 := bbase (se 5 (by rfl) ⟨127523, by rfl⟩ : syracuseStep 2720501 = 255047) (by norm_num)
theorem B2040565 : Blo 1207921 2040565 := bbase (se 5 (by rfl) ⟨95651, by rfl⟩ : syracuseStep 2040565 = 191303) (by norm_num)
theorem B6120197 : Blo 1207921 6120197 := bbase (se 4 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 6120197 = 1147537) (by norm_num)
theorem B2450189 : Blo 1207921 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B1721101 : Blo 1207921 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B5161765 : Blo 1207921 5161765 := bbase (se 4 (by rfl) ⟨483915, by rfl⟩ : syracuseStep 5161765 = 967831) (by norm_num)
theorem B2294581 : Blo 1207921 2294581 := bbase (se 5 (by rfl) ⟨107558, by rfl⟩ : syracuseStep 2294581 = 215117) (by norm_num)
theorem B2720573 : Blo 1207921 2720573 := bbase (se 3 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 2720573 = 1020215) (by norm_num)
theorem B2040653 : Blo 1207921 2040653 := bbase (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) (by norm_num)
theorem B3441541 : Blo 1207921 3441541 := bbase (se 4 (by rfl) ⟨322644, by rfl⟩ : syracuseStep 3441541 = 645289) (by norm_num)
theorem B2720645 : Blo 1207921 2720645 := bbase (se 4 (by rfl) ⟨255060, by rfl⟩ : syracuseStep 2720645 = 510121) (by norm_num)
theorem B1655701 : Blo 1207921 1655701 := bbase (se 6 (by rfl) ⟨38805, by rfl⟩ : syracuseStep 1655701 = 77611) (by norm_num)
theorem B6046645 : Blo 1207921 6046645 := bbase (se 5 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 6046645 = 566873) (by norm_num)
theorem B2294725 : Blo 1207921 2294725 := bbase (se 4 (by rfl) ⟨215130, by rfl⟩ : syracuseStep 2294725 = 430261) (by norm_num)
theorem B2720717 : Blo 1207921 2720717 := bbase (se 3 (by rfl) ⟨510134, by rfl⟩ : syracuseStep 2720717 = 1020269) (by norm_num)
theorem B2040781 : Blo 1207921 2040781 := bbase (se 3 (by rfl) ⟨382646, by rfl⟩ : syracuseStep 2040781 = 765293) (by norm_num)
theorem B9798677 : Blo 1207921 9798677 := bbase (se 6 (by rfl) ⟨229656, by rfl⟩ : syracuseStep 9798677 = 459313) (by norm_num)
theorem B2720789 : Blo 1207921 2720789 := bbase (se 6 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 2720789 = 127537) (by norm_num)
theorem B2581541 : Blo 1207921 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B2040869 : Blo 1207921 2040869 := bbase (se 4 (by rfl) ⟨191331, by rfl⟩ : syracuseStep 2040869 = 382663) (by norm_num)
theorem B4080725 : Blo 1207921 4080725 := bbase (se 8 (by rfl) ⟨23910, by rfl⟩ : syracuseStep 4080725 = 47821) (by norm_num)
theorem B2720861 : Blo 1207921 2720861 := bbase (se 3 (by rfl) ⟨510161, by rfl⟩ : syracuseStep 2720861 = 1020323) (by norm_num)
theorem B2294885 : Blo 1207921 2294885 := bbase (se 4 (by rfl) ⟨215145, by rfl⟩ : syracuseStep 2294885 = 430291) (by norm_num)
theorem B3310709 : Blo 1207921 3310709 := bbase (se 5 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 3310709 = 310379) (by norm_num)
theorem B2720933 : Blo 1207921 2720933 := bbase (se 4 (by rfl) ⟨255087, by rfl⟩ : syracuseStep 2720933 = 510175) (by norm_num)
theorem B1451209 : Blo 1207921 1451209 := bbase (se 2 (by rfl) ⟨544203, by rfl⟩ : syracuseStep 1451209 = 1088407) (by norm_num)
theorem B1451237 : Blo 1207921 1451237 := bbase (se 4 (by rfl) ⟨136053, by rfl⟩ : syracuseStep 1451237 = 272107) (by norm_num)
theorem B2721005 : Blo 1207921 2721005 := bbase (se 3 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 2721005 = 1020377) (by norm_num)
theorem B2295029 : Blo 1207921 2295029 := bbase (se 5 (by rfl) ⟨107579, by rfl⟩ : syracuseStep 2295029 = 215159) (by norm_num)
theorem B2721077 : Blo 1207921 2721077 := bbase (se 5 (by rfl) ⟨127550, by rfl⟩ : syracuseStep 2721077 = 255101) (by norm_num)
theorem B1451353 : Blo 1207921 1451353 := bbase (se 2 (by rfl) ⟨544257, by rfl⟩ : syracuseStep 1451353 = 1088515) (by norm_num)
theorem B1721693 : Blo 1207921 1721693 := bbase (se 3 (by rfl) ⟨322817, by rfl⟩ : syracuseStep 1721693 = 645635) (by norm_num)
theorem B2721149 : Blo 1207921 2721149 := bbase (se 3 (by rfl) ⟨510215, by rfl⟩ : syracuseStep 2721149 = 1020431) (by norm_num)
theorem B4588933 : Blo 1207921 4588933 := bbase (se 4 (by rfl) ⟨430212, by rfl⟩ : syracuseStep 4588933 = 860425) (by norm_num)
theorem B1811885 : Blo 1207921 1811885 := bbase (se 3 (by rfl) ⟨339728, by rfl⟩ : syracuseStep 1811885 = 679457) (by norm_num)
theorem B1721773 : Blo 1207921 1721773 := bbase (se 3 (by rfl) ⟨322832, by rfl⟩ : syracuseStep 1721773 = 645665) (by norm_num)
theorem B1451449 : Blo 1207921 1451449 := bbase (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) (by norm_num)
theorem B1811909 : Blo 1207921 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B1811933 : Blo 1207921 1811933 := bbase (se 3 (by rfl) ⟨339737, by rfl⟩ : syracuseStep 1811933 = 679475) (by norm_num)
theorem B2450909 : Blo 1207921 2450909 := bbase (se 3 (by rfl) ⟨459545, by rfl⟩ : syracuseStep 2450909 = 919091) (by norm_num)
theorem B1811957 : Blo 1207921 1811957 := bbase (se 5 (by rfl) ⟨84935, by rfl⟩ : syracuseStep 1811957 = 169871) (by norm_num)
theorem B4081157 : Blo 1207921 4081157 := bbase (se 4 (by rfl) ⟨382608, by rfl⟩ : syracuseStep 4081157 = 765217) (by norm_num)
theorem B1811981 : Blo 1207921 1811981 := bbase (se 3 (by rfl) ⟨339746, by rfl⟩ : syracuseStep 1811981 = 679493) (by norm_num)
theorem B2295317 : Blo 1207921 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B1812005 : Blo 1207921 1812005 := bbase (se 4 (by rfl) ⟨169875, by rfl⟩ : syracuseStep 1812005 = 339751) (by norm_num)
theorem B1721893 : Blo 1207921 1721893 := bbase (se 4 (by rfl) ⟨161427, by rfl⟩ : syracuseStep 1721893 = 322855) (by norm_num)
theorem B1812029 : Blo 1207921 1812029 := bbase (se 3 (by rfl) ⟨339755, by rfl⟩ : syracuseStep 1812029 = 679511) (by norm_num)
theorem B1812053 : Blo 1207921 1812053 := bbase (se 8 (by rfl) ⟨10617, by rfl⟩ : syracuseStep 1812053 = 21235) (by norm_num)
theorem B1812077 : Blo 1207921 1812077 := bbase (se 3 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 1812077 = 679529) (by norm_num)
theorem B1812101 : Blo 1207921 1812101 := bbase (se 4 (by rfl) ⟨169884, by rfl⟩ : syracuseStep 1812101 = 339769) (by norm_num)
theorem B1721989 : Blo 1207921 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B1812125 : Blo 1207921 1812125 := bbase (se 3 (by rfl) ⟨339773, by rfl⟩ : syracuseStep 1812125 = 679547) (by norm_num)
theorem B2295469 : Blo 1207921 2295469 := bbase (se 3 (by rfl) ⟨430400, by rfl⟩ : syracuseStep 2295469 = 860801) (by norm_num)
theorem B1812149 : Blo 1207921 1812149 := bbase (se 5 (by rfl) ⟨84944, by rfl⟩ : syracuseStep 1812149 = 169889) (by norm_num)
theorem B4589237 : Blo 1207921 4589237 := bbase (se 5 (by rfl) ⟨215120, by rfl⟩ : syracuseStep 4589237 = 430241) (by norm_num)
theorem B1812173 : Blo 1207921 1812173 := bbase (se 3 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 1812173 = 679565) (by norm_num)
theorem B1812197 : Blo 1207921 1812197 := bbase (se 4 (by rfl) ⟨169893, by rfl⟩ : syracuseStep 1812197 = 339787) (by norm_num)
theorem B1812221 : Blo 1207921 1812221 := bbase (se 3 (by rfl) ⟨339791, by rfl⟩ : syracuseStep 1812221 = 679583) (by norm_num)
theorem B1812245 : Blo 1207921 1812245 := bbase (se 6 (by rfl) ⟨42474, by rfl⟩ : syracuseStep 1812245 = 84949) (by norm_num)
theorem B10323733 : Blo 1207921 10323733 := bbase (se 6 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 10323733 = 483925) (by norm_num)
theorem B2582293 : Blo 1207921 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B1812269 : Blo 1207921 1812269 := bbase (se 3 (by rfl) ⟨339800, by rfl⟩ : syracuseStep 1812269 = 679601) (by norm_num)
theorem B1812293 : Blo 1207921 1812293 := bbase (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) (by norm_num)
theorem B1812317 : Blo 1207921 1812317 := bbase (se 3 (by rfl) ⟨339809, by rfl⟩ : syracuseStep 1812317 = 679619) (by norm_num)
theorem B1812341 : Blo 1207921 1812341 := bbase (se 5 (by rfl) ⟨84953, by rfl⟩ : syracuseStep 1812341 = 169907) (by norm_num)
theorem B1812365 : Blo 1207921 1812365 := bbase (se 3 (by rfl) ⟨339818, by rfl⟩ : syracuseStep 1812365 = 679637) (by norm_num)
theorem B1451929 : Blo 1207921 1451929 := bbase (se 2 (by rfl) ⟨544473, by rfl⟩ : syracuseStep 1451929 = 1088947) (by norm_num)
theorem B1812389 : Blo 1207921 1812389 := bbase (se 4 (by rfl) ⟨169911, by rfl⟩ : syracuseStep 1812389 = 339823) (by norm_num)
theorem B2582437 : Blo 1207921 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B4081589 : Blo 1207921 4081589 := bbase (se 5 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 4081589 = 382649) (by norm_num)
theorem B1812413 : Blo 1207921 1812413 := bbase (se 3 (by rfl) ⟨339827, by rfl⟩ : syracuseStep 1812413 = 679655) (by norm_num)
theorem B1812437 : Blo 1207921 1812437 := bbase (se 7 (by rfl) ⟨21239, by rfl⟩ : syracuseStep 1812437 = 42479) (by norm_num)
theorem B2295773 : Blo 1207921 2295773 := bbase (se 3 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 2295773 = 860915) (by norm_num)
theorem B1812461 : Blo 1207921 1812461 := bbase (se 3 (by rfl) ⟨339836, by rfl⟩ : syracuseStep 1812461 = 679673) (by norm_num)
theorem B1812485 : Blo 1207921 1812485 := bbase (se 4 (by rfl) ⟨169920, by rfl⟩ : syracuseStep 1812485 = 339841) (by norm_num)
theorem B6121493 : Blo 1207921 6121493 := bbase (se 6 (by rfl) ⟨143472, by rfl⟩ : syracuseStep 6121493 = 286945) (by norm_num)
theorem B1812509 : Blo 1207921 1812509 := bbase (se 3 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 1812509 = 679691) (by norm_num)
theorem B3057709 : Blo 1207921 3057709 := bbase (se 3 (by rfl) ⟨573320, by rfl⟩ : syracuseStep 3057709 = 1146641) (by norm_num)
theorem B1812533 : Blo 1207921 1812533 := bbase (se 5 (by rfl) ⟨84962, by rfl⟩ : syracuseStep 1812533 = 169925) (by norm_num)
theorem B1812557 : Blo 1207921 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B2484317 : Blo 1207921 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B1812581 : Blo 1207921 1812581 := bbase (se 4 (by rfl) ⟨169929, by rfl⟩ : syracuseStep 1812581 = 339859) (by norm_num)
theorem B1812605 : Blo 1207921 1812605 := bbase (se 3 (by rfl) ⟨339863, by rfl⟩ : syracuseStep 1812605 = 679727) (by norm_num)
theorem B1812629 : Blo 1207921 1812629 := bbase (se 6 (by rfl) ⟨42483, by rfl⟩ : syracuseStep 1812629 = 84967) (by norm_num)
theorem B3057821 : Blo 1207921 3057821 := bbase (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) (by norm_num)
theorem B1812653 : Blo 1207921 1812653 := bbase (se 3 (by rfl) ⟨339872, by rfl⟩ : syracuseStep 1812653 = 679745) (by norm_num)
theorem B1812677 : Blo 1207921 1812677 := bbase (se 4 (by rfl) ⟨169938, by rfl⟩ : syracuseStep 1812677 = 339877) (by norm_num)
theorem B1812701 : Blo 1207921 1812701 := bbase (se 3 (by rfl) ⟨339881, by rfl⟩ : syracuseStep 1812701 = 679763) (by norm_num)
theorem B1812725 : Blo 1207921 1812725 := bbase (se 5 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 1812725 = 169943) (by norm_num)
theorem B1812749 : Blo 1207921 1812749 := bbase (se 3 (by rfl) ⟨339890, by rfl⟩ : syracuseStep 1812749 = 679781) (by norm_num)
theorem B2582813 : Blo 1207921 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B1812773 : Blo 1207921 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B1812797 : Blo 1207921 1812797 := bbase (se 3 (by rfl) ⟨339899, by rfl⟩ : syracuseStep 1812797 = 679799) (by norm_num)
theorem B1812821 : Blo 1207921 1812821 := bbase (se 10 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 1812821 = 5311) (by norm_num)
theorem B3058013 : Blo 1207921 3058013 := bbase (se 3 (by rfl) ⟨573377, by rfl⟩ : syracuseStep 3058013 = 1146755) (by norm_num)
theorem B1812845 : Blo 1207921 1812845 := bbase (se 3 (by rfl) ⟨339908, by rfl⟩ : syracuseStep 1812845 = 679817) (by norm_num)
theorem B1378669 : Blo 1207921 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B2902397 : Blo 1207921 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B1812869 : Blo 1207921 1812869 := bbase (se 4 (by rfl) ⟨169956, by rfl⟩ : syracuseStep 1812869 = 339913) (by norm_num)
theorem B4778389 : Blo 1207921 4778389 := bbase (se 6 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 4778389 = 223987) (by norm_num)
theorem B1812893 : Blo 1207921 1812893 := bbase (se 3 (by rfl) ⟨339917, by rfl⟩ : syracuseStep 1812893 = 679835) (by norm_num)
theorem B1378729 : Blo 1207921 1378729 := bbase (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) (by norm_num)
theorem B1812917 : Blo 1207921 1812917 := bbase (se 5 (by rfl) ⟨84980, by rfl⟩ : syracuseStep 1812917 = 169961) (by norm_num)
theorem B1812941 : Blo 1207921 1812941 := bbase (se 3 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 1812941 = 679853) (by norm_num)
theorem B5302741 : Blo 1207921 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B1935829 : Blo 1207921 1935829 := bbase (se 7 (by rfl) ⟨22685, by rfl⟩ : syracuseStep 1935829 = 45371) (by norm_num)
theorem B1812965 : Blo 1207921 1812965 := bbase (se 4 (by rfl) ⟨169965, by rfl⟩ : syracuseStep 1812965 = 339931) (by norm_num)
theorem B1812989 : Blo 1207921 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B1813013 : Blo 1207921 1813013 := bbase (se 6 (by rfl) ⟨42492, by rfl⟩ : syracuseStep 1813013 = 84985) (by norm_num)
theorem B1813037 : Blo 1207921 1813037 := bbase (se 3 (by rfl) ⟨339944, by rfl⟩ : syracuseStep 1813037 = 679889) (by norm_num)
theorem B1813061 : Blo 1207921 1813061 := bbase (se 4 (by rfl) ⟨169974, by rfl⟩ : syracuseStep 1813061 = 339949) (by norm_num)
theorem B7744085 : Blo 1207921 7744085 := bbase (se 8 (by rfl) ⟨45375, by rfl⟩ : syracuseStep 7744085 = 90751) (by norm_num)
theorem B1813085 : Blo 1207921 1813085 := bbase (se 3 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 1813085 = 679907) (by norm_num)
theorem B1813109 : Blo 1207921 1813109 := bbase (se 5 (by rfl) ⟨84989, by rfl⟩ : syracuseStep 1813109 = 169979) (by norm_num)
theorem B1813133 : Blo 1207921 1813133 := bbase (se 3 (by rfl) ⟨339962, by rfl⟩ : syracuseStep 1813133 = 679925) (by norm_num)
theorem B1813157 : Blo 1207921 1813157 := bbase (se 4 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 1813157 = 339967) (by norm_num)
theorem B3058357 : Blo 1207921 3058357 := bbase (se 5 (by rfl) ⟨143360, by rfl⟩ : syracuseStep 3058357 = 286721) (by norm_num)
theorem B1813181 : Blo 1207921 1813181 := bbase (se 3 (by rfl) ⟨339971, by rfl⟩ : syracuseStep 1813181 = 679943) (by norm_num)
theorem B1813205 : Blo 1207921 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B1813229 : Blo 1207921 1813229 := bbase (se 3 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 1813229 = 679961) (by norm_num)
theorem B1813253 : Blo 1207921 1813253 := bbase (se 4 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 1813253 = 339985) (by norm_num)
theorem B1813277 : Blo 1207921 1813277 := bbase (se 3 (by rfl) ⟨339989, by rfl⟩ : syracuseStep 1813277 = 679979) (by norm_num)
theorem B3058469 : Blo 1207921 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B1813301 : Blo 1207921 1813301 := bbase (se 5 (by rfl) ⟨84998, by rfl⟩ : syracuseStep 1813301 = 169997) (by norm_num)
theorem B1813325 : Blo 1207921 1813325 := bbase (se 3 (by rfl) ⟨339998, by rfl⟩ : syracuseStep 1813325 = 679997) (by norm_num)
theorem B1813349 : Blo 1207921 1813349 := bbase (se 4 (by rfl) ⟨170001, by rfl⟩ : syracuseStep 1813349 = 340003) (by norm_num)
theorem B1813373 : Blo 1207921 1813373 := bbase (se 3 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 1813373 = 680015) (by norm_num)
theorem B1813397 : Blo 1207921 1813397 := bbase (se 6 (by rfl) ⟨42501, by rfl⟩ : syracuseStep 1813397 = 85003) (by norm_num)
theorem B1813421 : Blo 1207921 1813421 := bbase (se 3 (by rfl) ⟨340016, by rfl⟩ : syracuseStep 1813421 = 680033) (by norm_num)
theorem B1813445 : Blo 1207921 1813445 := bbase (se 4 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 1813445 = 340021) (by norm_num)
theorem B1813469 : Blo 1207921 1813469 := bbase (se 3 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 1813469 = 680051) (by norm_num)
theorem B3058661 : Blo 1207921 3058661 := bbase (se 4 (by rfl) ⟨286749, by rfl⟩ : syracuseStep 3058661 = 573499) (by norm_num)
theorem B1813493 : Blo 1207921 1813493 := bbase (se 5 (by rfl) ⟨85007, by rfl⟩ : syracuseStep 1813493 = 170015) (by norm_num)
theorem B1813517 : Blo 1207921 1813517 := bbase (se 3 (by rfl) ⟨340034, by rfl⟩ : syracuseStep 1813517 = 680069) (by norm_num)
theorem B15494165 : Blo 1207921 15494165 := bbase (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) (by norm_num)
theorem B1813541 : Blo 1207921 1813541 := bbase (se 4 (by rfl) ⟨170019, by rfl⟩ : syracuseStep 1813541 = 340039) (by norm_num)
theorem B1813565 : Blo 1207921 1813565 := bbase (se 3 (by rfl) ⟨340043, by rfl⟩ : syracuseStep 1813565 = 680087) (by norm_num)
theorem B1813589 : Blo 1207921 1813589 := bbase (se 8 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 1813589 = 21253) (by norm_num)
theorem B1813613 : Blo 1207921 1813613 := bbase (se 3 (by rfl) ⟨340052, by rfl⟩ : syracuseStep 1813613 = 680105) (by norm_num)
theorem B7851125 : Blo 1207921 7851125 := bbase (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) (by norm_num)
theorem B1813637 : Blo 1207921 1813637 := bbase (se 4 (by rfl) ⟨170028, by rfl⟩ : syracuseStep 1813637 = 340057) (by norm_num)
theorem B1813661 : Blo 1207921 1813661 := bbase (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) (by norm_num)
theorem B1813685 : Blo 1207921 1813685 := bbase (se 5 (by rfl) ⟨85016, by rfl⟩ : syracuseStep 1813685 = 170033) (by norm_num)
theorem B2985157 : Blo 1207921 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B1813709 : Blo 1207921 1813709 := bbase (se 3 (by rfl) ⟨340070, by rfl⟩ : syracuseStep 1813709 = 680141) (by norm_num)
theorem B1813733 : Blo 1207921 1813733 := bbase (se 4 (by rfl) ⟨170037, by rfl⟩ : syracuseStep 1813733 = 340075) (by norm_num)
theorem B2067709 : Blo 1207921 2067709 := bbase (se 3 (by rfl) ⟨387695, by rfl⟩ : syracuseStep 2067709 = 775391) (by norm_num)
theorem B1813757 : Blo 1207921 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B1813781 : Blo 1207921 1813781 := bbase (se 6 (by rfl) ⟨42510, by rfl⟩ : syracuseStep 1813781 = 85021) (by norm_num)
theorem B1813805 : Blo 1207921 1813805 := bbase (se 3 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 1813805 = 680177) (by norm_num)
theorem B3059005 : Blo 1207921 3059005 := bbase (se 3 (by rfl) ⟨573563, by rfl⟩ : syracuseStep 3059005 = 1147127) (by norm_num)
theorem B1813829 : Blo 1207921 1813829 := bbase (se 4 (by rfl) ⟨170046, by rfl⟩ : syracuseStep 1813829 = 340093) (by norm_num)
theorem B1813853 : Blo 1207921 1813853 := bbase (se 3 (by rfl) ⟨340097, by rfl⟩ : syracuseStep 1813853 = 680195) (by norm_num)
theorem B1813877 : Blo 1207921 1813877 := bbase (se 5 (by rfl) ⟨85025, by rfl⟩ : syracuseStep 1813877 = 170051) (by norm_num)
theorem B3100045 : Blo 1207921 3100045 := bbase (se 3 (by rfl) ⟨581258, by rfl⟩ : syracuseStep 3100045 = 1162517) (by norm_num)
theorem B1813901 : Blo 1207921 1813901 := bbase (se 3 (by rfl) ⟨340106, by rfl⟩ : syracuseStep 1813901 = 680213) (by norm_num)
theorem B1813925 : Blo 1207921 1813925 := bbase (se 4 (by rfl) ⟨170055, by rfl⟩ : syracuseStep 1813925 = 340111) (by norm_num)
theorem B3059117 : Blo 1207921 3059117 := bbase (se 3 (by rfl) ⟨573584, by rfl⟩ : syracuseStep 3059117 = 1147169) (by norm_num)
theorem B1813949 : Blo 1207921 1813949 := bbase (se 3 (by rfl) ⟨340115, by rfl⟩ : syracuseStep 1813949 = 680231) (by norm_num)
theorem B1813973 : Blo 1207921 1813973 := bbase (se 7 (by rfl) ⟨21257, by rfl⟩ : syracuseStep 1813973 = 42515) (by norm_num)
theorem B1813997 : Blo 1207921 1813997 := bbase (se 3 (by rfl) ⟨340124, by rfl⟩ : syracuseStep 1813997 = 680249) (by norm_num)
theorem B1814021 : Blo 1207921 1814021 := bbase (se 4 (by rfl) ⟨170064, by rfl⟩ : syracuseStep 1814021 = 340129) (by norm_num)
theorem B1814045 : Blo 1207921 1814045 := bbase (se 3 (by rfl) ⟨340133, by rfl⟩ : syracuseStep 1814045 = 680267) (by norm_num)
theorem B1814069 : Blo 1207921 1814069 := bbase (se 5 (by rfl) ⟨85034, by rfl⟩ : syracuseStep 1814069 = 170069) (by norm_num)
theorem B1961533 : Blo 1207921 1961533 := bbase (se 3 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 1961533 = 735575) (by norm_num)
theorem B1814093 : Blo 1207921 1814093 := bbase (se 3 (by rfl) ⟨340142, by rfl⟩ : syracuseStep 1814093 = 680285) (by norm_num)
theorem B2756197 : Blo 1207921 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B1814117 : Blo 1207921 1814117 := bbase (se 4 (by rfl) ⟨170073, by rfl⟩ : syracuseStep 1814117 = 340147) (by norm_num)
theorem B3059309 : Blo 1207921 3059309 := bbase (se 3 (by rfl) ⟨573620, by rfl⟩ : syracuseStep 3059309 = 1147241) (by norm_num)
theorem B10325717 : Blo 1207921 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B4591349 : Blo 1207921 4591349 := bbase (se 5 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 4591349 = 430439) (by norm_num)
theorem B1937213 : Blo 1207921 1937213 := bbase (se 3 (by rfl) ⟨363227, by rfl⟩ : syracuseStep 1937213 = 726455) (by norm_num)
theorem B1290053 : Blo 1207921 1290053 := bbase (se 4 (by rfl) ⟨120942, by rfl⟩ : syracuseStep 1290053 = 241885) (by norm_num)
theorem B1290125 : Blo 1207921 1290125 := bbase (se 3 (by rfl) ⟨241898, by rfl⟩ : syracuseStep 1290125 = 483797) (by norm_num)
theorem B6885269 : Blo 1207921 6885269 := bbase (se 6 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 6885269 = 322747) (by norm_num)
theorem B3059653 : Blo 1207921 3059653 := bbase (se 4 (by rfl) ⟨286842, by rfl⟩ : syracuseStep 3059653 = 573685) (by norm_num)
theorem B5230565 : Blo 1207921 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B4591637 : Blo 1207921 4591637 := bbase (se 6 (by rfl) ⟨107616, by rfl⟩ : syracuseStep 4591637 = 215233) (by norm_num)
theorem B3059765 : Blo 1207921 3059765 := bbase (se 5 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 3059765 = 286853) (by norm_num)
theorem B1290313 : Blo 1207921 1290313 := bbase (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) (by norm_num)
theorem B3723365 : Blo 1207921 3723365 := bbase (se 4 (by rfl) ⟨349065, by rfl⟩ : syracuseStep 3723365 = 698131) (by norm_num)
theorem B1962085 : Blo 1207921 1962085 := bbase (se 4 (by rfl) ⟨183945, by rfl⟩ : syracuseStep 1962085 = 367891) (by norm_num)
theorem B1863805 : Blo 1207921 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B2068661 : Blo 1207921 2068661 := bbase (se 5 (by rfl) ⟨96968, by rfl⟩ : syracuseStep 2068661 = 193937) (by norm_num)
theorem B3059957 : Blo 1207921 3059957 := bbase (se 5 (by rfl) ⟨143435, by rfl⟩ : syracuseStep 3059957 = 286871) (by norm_num)
theorem B1290497 : Blo 1207921 1290497 := bbase (se 2 (by rfl) ⟨483936, by rfl⟩ : syracuseStep 1290497 = 967873) (by norm_num)
theorem B1225001 : Blo 1207921 1225001 := bbase (se 2 (by rfl) ⟨459375, by rfl⟩ : syracuseStep 1225001 = 918751) (by norm_num)
theorem B2756909 : Blo 1207921 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B1225049 : Blo 1207921 1225049 := bbase (se 2 (by rfl) ⟨459393, by rfl⟩ : syracuseStep 1225049 = 918787) (by norm_num)
theorem B3871093 : Blo 1207921 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B2945429 : Blo 1207921 2945429 := bbase (se 6 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 2945429 = 138067) (by norm_num)
theorem B2421181 : Blo 1207921 2421181 := bbase (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) (by norm_num)
theorem B2904589 : Blo 1207921 2904589 := bbase (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) (by norm_num)
theorem B3060301 : Blo 1207921 3060301 := bbase (se 3 (by rfl) ⟨573806, by rfl⟩ : syracuseStep 3060301 = 1147613) (by norm_num)
theorem B16536149 : Blo 1207921 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B1225301 : Blo 1207921 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1397405 : Blo 1207921 1397405 := bbase (se 3 (by rfl) ⟨262013, by rfl⟩ : syracuseStep 1397405 = 524027) (by norm_num)
theorem B3060413 : Blo 1207921 3060413 := bbase (se 3 (by rfl) ⟨573827, by rfl⟩ : syracuseStep 3060413 = 1147655) (by norm_num)
theorem B3060605 : Blo 1207921 3060605 := bbase (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) (by norm_num)
theorem B9180053 : Blo 1207921 9180053 := bbase (se 6 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 9180053 = 430315) (by norm_num)
theorem B1528789 : Blo 1207921 1528789 := bbase (se 7 (by rfl) ⟨17915, by rfl⟩ : syracuseStep 1528789 = 35831) (by norm_num)
theorem B6116309 : Blo 1207921 6116309 := bbase (se 7 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 6116309 = 143351) (by norm_num)
theorem B1291249 : Blo 1207921 1291249 := bbase (se 2 (by rfl) ⟨484218, by rfl⟩ : syracuseStep 1291249 = 968437) (by norm_num)
theorem B1528885 : Blo 1207921 1528885 := bbase (se 5 (by rfl) ⟨71666, by rfl⟩ : syracuseStep 1528885 = 143333) (by norm_num)
theorem B1291321 : Blo 1207921 1291321 := bbase (se 2 (by rfl) ⟨484245, by rfl⟩ : syracuseStep 1291321 = 968491) (by norm_num)
theorem B1242305 : Blo 1207921 1242305 := bbase (se 2 (by rfl) ⟨465864, by rfl⟩ : syracuseStep 1242305 = 931729) (by norm_num)
theorem B13767893 : Blo 1207921 13767893 := bbase (se 7 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 13767893 = 322685) (by norm_num)
theorem B3060949 : Blo 1207921 3060949 := bbase (se 7 (by rfl) ⟨35870, by rfl⟩ : syracuseStep 3060949 = 71741) (by norm_num)
theorem B1529057 : Blo 1207921 1529057 := bbase (se 2 (by rfl) ⟨573396, by rfl⟩ : syracuseStep 1529057 = 1146793) (by norm_num)
theorem B1291501 : Blo 1207921 1291501 := bbase (se 3 (by rfl) ⟨242156, by rfl⟩ : syracuseStep 1291501 = 484313) (by norm_num)
theorem B1529113 : Blo 1207921 1529113 := bbase (se 2 (by rfl) ⟨573417, by rfl⟩ : syracuseStep 1529113 = 1146835) (by norm_num)
theorem B4076837 : Blo 1207921 4076837 := bbase (se 4 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 4076837 = 764407) (by norm_num)
theorem B1914149 : Blo 1207921 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B3061061 : Blo 1207921 3061061 := bbase (se 4 (by rfl) ⟨286974, by rfl⟩ : syracuseStep 3061061 = 573949) (by norm_num)
theorem B1471817 : Blo 1207921 1471817 := bbase (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) (by norm_num)
theorem B7853429 : Blo 1207921 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B1529209 : Blo 1207921 1529209 := bbase (se 2 (by rfl) ⟨573453, by rfl⟩ : syracuseStep 1529209 = 1146907) (by norm_num)
theorem B3061253 : Blo 1207921 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B1529381 : Blo 1207921 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B1963565 : Blo 1207921 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1529437 : Blo 1207921 1529437 := bbase (se 3 (by rfl) ⟨286769, by rfl⟩ : syracuseStep 1529437 = 573539) (by norm_num)
theorem B5805701 : Blo 1207921 5805701 := bbase (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) (by norm_num)
theorem B1529533 : Blo 1207921 1529533 := bbase (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) (by norm_num)
theorem B4077269 : Blo 1207921 4077269 := bbase (se 7 (by rfl) ⟨47780, by rfl⟩ : syracuseStep 4077269 = 95561) (by norm_num)
theorem B11622197 : Blo 1207921 11622197 := bbase (se 5 (by rfl) ⟨544790, by rfl⟩ : syracuseStep 11622197 = 1089581) (by norm_num)
theorem B3585877 : Blo 1207921 3585877 := bbase (se 9 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 3585877 = 21011) (by norm_num)
theorem B1529705 : Blo 1207921 1529705 := bbase (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) (by norm_num)
theorem B2176885 : Blo 1207921 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B1529761 : Blo 1207921 1529761 := bbase (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) (by norm_num)
theorem B1529857 : Blo 1207921 1529857 := bbase (se 2 (by rfl) ⟨573696, by rfl⟩ : syracuseStep 1529857 = 1147393) (by norm_num)
theorem B4077701 : Blo 1207921 4077701 := bbase (se 4 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 4077701 = 764569) (by norm_num)
theorem B2717837 : Blo 1207921 2717837 := bbase (se 3 (by rfl) ⟨509594, by rfl⟩ : syracuseStep 2717837 = 1019189) (by norm_num)
theorem B1530029 : Blo 1207921 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B2717909 : Blo 1207921 2717909 := bbase (se 7 (by rfl) ⟨31850, by rfl⟩ : syracuseStep 2717909 = 63701) (by norm_num)
theorem B6117605 : Blo 1207921 6117605 := bbase (se 4 (by rfl) ⟨573525, by rfl⟩ : syracuseStep 6117605 = 1147051) (by norm_num)
theorem B1530085 : Blo 1207921 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B2717981 : Blo 1207921 2717981 := bbase (se 3 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 2717981 = 1019243) (by norm_num)
theorem B2177317 : Blo 1207921 2177317 := bbase (se 4 (by rfl) ⟨204123, by rfl⟩ : syracuseStep 2177317 = 408247) (by norm_num)
theorem B1530181 : Blo 1207921 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B2718053 : Blo 1207921 2718053 := bbase (se 4 (by rfl) ⟨254817, by rfl⟩ : syracuseStep 2718053 = 509635) (by norm_num)
theorem B5233061 : Blo 1207921 5233061 := bbase (se 4 (by rfl) ⟨490599, by rfl⟩ : syracuseStep 5233061 = 981199) (by norm_num)
theorem B2718125 : Blo 1207921 2718125 := bbase (se 3 (by rfl) ⟨509648, by rfl⟩ : syracuseStep 2718125 = 1019297) (by norm_num)
theorem B1530353 : Blo 1207921 1530353 := bbase (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) (by norm_num)
theorem B2718197 : Blo 1207921 2718197 := bbase (se 5 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 2718197 = 254831) (by norm_num)
theorem B1530409 : Blo 1207921 1530409 := bbase (se 2 (by rfl) ⟨573903, by rfl⟩ : syracuseStep 1530409 = 1147807) (by norm_num)
theorem B4078133 : Blo 1207921 4078133 := bbase (se 5 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 4078133 = 382325) (by norm_num)
theorem B2718269 : Blo 1207921 2718269 := bbase (se 3 (by rfl) ⟨509675, by rfl⟩ : syracuseStep 2718269 = 1019351) (by norm_num)
theorem B4356709 : Blo 1207921 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B2038405 : Blo 1207921 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B2718341 : Blo 1207921 2718341 := bbase (se 4 (by rfl) ⟨254844, by rfl⟩ : syracuseStep 2718341 = 509689) (by norm_num)
theorem B1530505 : Blo 1207921 1530505 := bbase (se 2 (by rfl) ⟨573939, by rfl⟩ : syracuseStep 1530505 = 1147879) (by norm_num)
theorem B3676853 : Blo 1207921 3676853 := bbase (se 5 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 3676853 = 344705) (by norm_num)
theorem B2718413 : Blo 1207921 2718413 := bbase (se 3 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 2718413 = 1019405) (by norm_num)
theorem B2038493 : Blo 1207921 2038493 := bbase (se 3 (by rfl) ⟨382217, by rfl⟩ : syracuseStep 2038493 = 764435) (by norm_num)
theorem B2718485 : Blo 1207921 2718485 := bbase (se 6 (by rfl) ⟨63714, by rfl⟩ : syracuseStep 2718485 = 127429) (by norm_num)
theorem B2177837 : Blo 1207921 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B2038621 : Blo 1207921 2038621 := bbase (se 3 (by rfl) ⟨382241, by rfl⟩ : syracuseStep 2038621 = 764483) (by norm_num)
theorem B2718557 : Blo 1207921 2718557 := bbase (se 3 (by rfl) ⟨509729, by rfl⟩ : syracuseStep 2718557 = 1019459) (by norm_num)
theorem B3726229 : Blo 1207921 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B2718629 : Blo 1207921 2718629 := bbase (se 4 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 2718629 = 509743) (by norm_num)
theorem B2038709 : Blo 1207921 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B4078565 : Blo 1207921 4078565 := bbase (se 4 (by rfl) ⟨382365, by rfl⟩ : syracuseStep 4078565 = 764731) (by norm_num)
theorem B2718701 : Blo 1207921 2718701 := bbase (se 3 (by rfl) ⟨509756, by rfl⟩ : syracuseStep 2718701 = 1019513) (by norm_num)
theorem B2038837 : Blo 1207921 2038837 := bbase (se 5 (by rfl) ⟨95570, by rfl⟩ : syracuseStep 2038837 = 191141) (by norm_num)
theorem B2718773 : Blo 1207921 2718773 := bbase (se 5 (by rfl) ⟨127442, by rfl⟩ : syracuseStep 2718773 = 254885) (by norm_num)
theorem B4136021 : Blo 1207921 4136021 := bbase (se 8 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 4136021 = 48469) (by norm_num)
theorem B1358941 : Blo 1207921 1358941 := bbase (se 3 (by rfl) ⟨254801, by rfl⟩ : syracuseStep 1358941 = 509603) (by norm_num)
theorem B2718845 : Blo 1207921 2718845 := bbase (se 3 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 2718845 = 1019567) (by norm_num)
theorem B1358977 : Blo 1207921 1358977 := bbase (se 2 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 1358977 = 1019233) (by norm_num)
theorem B2038925 : Blo 1207921 2038925 := bbase (se 3 (by rfl) ⟨382298, by rfl⟩ : syracuseStep 2038925 = 764597) (by norm_num)
theorem B1359013 : Blo 1207921 1359013 := bbase (se 4 (by rfl) ⟨127407, by rfl⟩ : syracuseStep 1359013 = 254815) (by norm_num)
theorem B2718917 : Blo 1207921 2718917 := bbase (se 4 (by rfl) ⟨254898, by rfl⟩ : syracuseStep 2718917 = 509797) (by norm_num)
theorem B1359049 : Blo 1207921 1359049 := bbase (se 2 (by rfl) ⟨509643, by rfl⟩ : syracuseStep 1359049 = 1019287) (by norm_num)
theorem B1359085 : Blo 1207921 1359085 := bbase (se 3 (by rfl) ⟨254828, by rfl⟩ : syracuseStep 1359085 = 509657) (by norm_num)
theorem B12401909 : Blo 1207921 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B2039053 : Blo 1207921 2039053 := bbase (se 3 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 2039053 = 764645) (by norm_num)
theorem B2718989 : Blo 1207921 2718989 := bbase (se 3 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 2718989 = 1019621) (by norm_num)
theorem B1359121 : Blo 1207921 1359121 := bbase (se 2 (by rfl) ⟨509670, by rfl⟩ : syracuseStep 1359121 = 1019341) (by norm_num)
theorem B1359157 : Blo 1207921 1359157 := bbase (se 5 (by rfl) ⟨63710, by rfl⟩ : syracuseStep 1359157 = 127421) (by norm_num)
theorem B2719061 : Blo 1207921 2719061 := bbase (se 11 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 2719061 = 3983) (by norm_num)
theorem B1359193 : Blo 1207921 1359193 := bbase (se 2 (by rfl) ⟨509697, by rfl⟩ : syracuseStep 1359193 = 1019395) (by norm_num)
theorem B2039141 : Blo 1207921 2039141 := bbase (se 4 (by rfl) ⟨191169, by rfl⟩ : syracuseStep 2039141 = 382339) (by norm_num)
theorem B1359229 : Blo 1207921 1359229 := bbase (se 3 (by rfl) ⟨254855, by rfl⟩ : syracuseStep 1359229 = 509711) (by norm_num)
theorem B4078997 : Blo 1207921 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B3267989 : Blo 1207921 3267989 := bbase (se 6 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 3267989 = 153187) (by norm_num)
theorem B2719133 : Blo 1207921 2719133 := bbase (se 3 (by rfl) ⟨509837, by rfl⟩ : syracuseStep 2719133 = 1019675) (by norm_num)
theorem B1359265 : Blo 1207921 1359265 := bbase (se 2 (by rfl) ⟨509724, by rfl⟩ : syracuseStep 1359265 = 1019449) (by norm_num)
theorem B1359301 : Blo 1207921 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B2039269 : Blo 1207921 2039269 := bbase (se 4 (by rfl) ⟨191181, by rfl⟩ : syracuseStep 2039269 = 382363) (by norm_num)
theorem B2719205 : Blo 1207921 2719205 := bbase (se 4 (by rfl) ⟨254925, by rfl⟩ : syracuseStep 2719205 = 509851) (by norm_num)
theorem B1359337 : Blo 1207921 1359337 := bbase (se 2 (by rfl) ⟨509751, by rfl⟩ : syracuseStep 1359337 = 1019503) (by norm_num)
theorem B6118901 : Blo 1207921 6118901 := bbase (se 5 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 6118901 = 573647) (by norm_num)
theorem B1359373 : Blo 1207921 1359373 := bbase (se 3 (by rfl) ⟨254882, by rfl⟩ : syracuseStep 1359373 = 509765) (by norm_num)
theorem B2719277 : Blo 1207921 2719277 := bbase (se 3 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 2719277 = 1019729) (by norm_num)
theorem B1359409 : Blo 1207921 1359409 := bbase (se 2 (by rfl) ⟨509778, by rfl⟩ : syracuseStep 1359409 = 1019557) (by norm_num)
theorem B2039357 : Blo 1207921 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B5103173 : Blo 1207921 5103173 := bbase (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) (by norm_num)
theorem B1359445 : Blo 1207921 1359445 := bbase (se 8 (by rfl) ⟨7965, by rfl⟩ : syracuseStep 1359445 = 15931) (by norm_num)
theorem B2719349 : Blo 1207921 2719349 := bbase (se 5 (by rfl) ⟨127469, by rfl⟩ : syracuseStep 2719349 = 254939) (by norm_num)
theorem B1359481 : Blo 1207921 1359481 := bbase (se 2 (by rfl) ⟨509805, by rfl⟩ : syracuseStep 1359481 = 1019611) (by norm_num)
theorem B2293373 : Blo 1207921 2293373 := bbase (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) (by norm_num)
theorem B2449045 : Blo 1207921 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B1359517 : Blo 1207921 1359517 := bbase (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) (by norm_num)
theorem B2039485 : Blo 1207921 2039485 := bbase (se 3 (by rfl) ⟨382403, by rfl⟩ : syracuseStep 2039485 = 764807) (by norm_num)
theorem B2719421 : Blo 1207921 2719421 := bbase (se 3 (by rfl) ⟨509891, by rfl⟩ : syracuseStep 2719421 = 1019783) (by norm_num)
theorem B1359553 : Blo 1207921 1359553 := bbase (se 2 (by rfl) ⟨509832, by rfl⟩ : syracuseStep 1359553 = 1019665) (by norm_num)
theorem B1359589 : Blo 1207921 1359589 := bbase (se 4 (by rfl) ⟨127461, by rfl⟩ : syracuseStep 1359589 = 254923) (by norm_num)
theorem B3440357 : Blo 1207921 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B2719493 : Blo 1207921 2719493 := bbase (se 4 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 2719493 = 509905) (by norm_num)
theorem B1359625 : Blo 1207921 1359625 := bbase (se 2 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 1359625 = 1019719) (by norm_num)
theorem B2293525 : Blo 1207921 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B2039573 : Blo 1207921 2039573 := bbase (se 6 (by rfl) ⟨47802, by rfl⟩ : syracuseStep 2039573 = 95605) (by norm_num)
theorem B1359661 : Blo 1207921 1359661 := bbase (se 3 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 1359661 = 509873) (by norm_num)
theorem B5160773 : Blo 1207921 5160773 := bbase (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) (by norm_num)
theorem B4079429 : Blo 1207921 4079429 := bbase (se 4 (by rfl) ⟨382446, by rfl⟩ : syracuseStep 4079429 = 764893) (by norm_num)
theorem B3268421 : Blo 1207921 3268421 := bbase (se 4 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 3268421 = 612829) (by norm_num)
theorem B2719565 : Blo 1207921 2719565 := bbase (se 3 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 2719565 = 1019837) (by norm_num)
theorem B1359697 : Blo 1207921 1359697 := bbase (se 2 (by rfl) ⟨509886, by rfl⟩ : syracuseStep 1359697 = 1019773) (by norm_num)
theorem B1359733 : Blo 1207921 1359733 := bbase (se 5 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 1359733 = 127475) (by norm_num)
theorem B2039701 : Blo 1207921 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B2719637 : Blo 1207921 2719637 := bbase (se 6 (by rfl) ⟨63741, by rfl⟩ : syracuseStep 2719637 = 127483) (by norm_num)
theorem B1359769 : Blo 1207921 1359769 := bbase (se 2 (by rfl) ⟨509913, by rfl⟩ : syracuseStep 1359769 = 1019827) (by norm_num)
theorem B1359805 : Blo 1207921 1359805 := bbase (se 3 (by rfl) ⟨254963, by rfl⟩ : syracuseStep 1359805 = 509927) (by norm_num)
theorem B4587461 : Blo 1207921 4587461 := bbase (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) (by norm_num)
theorem B2719709 : Blo 1207921 2719709 := bbase (se 3 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 2719709 = 1019891) (by norm_num)
theorem B1359841 : Blo 1207921 1359841 := bbase (se 2 (by rfl) ⟨509940, by rfl⟩ : syracuseStep 1359841 = 1019881) (by norm_num)
theorem B2039789 : Blo 1207921 2039789 := bbase (se 3 (by rfl) ⟨382460, by rfl⟩ : syracuseStep 2039789 = 764921) (by norm_num)
theorem B1343473 : Blo 1207921 1343473 := bbase (se 2 (by rfl) ⟨503802, by rfl⟩ : syracuseStep 1343473 = 1007605) (by norm_num)
theorem B2039809 : Blo 1207921 2039809 := bstep (se 2 (by rfl) ⟨764928, by rfl⟩ : syracuseStep 2039809 = 1529857) B1529857
theorem B2039843 : Blo 1207921 2039843 := bstep (se 1 (by rfl) ⟨1529882, by rfl⟩ : syracuseStep 2039843 = 3059765) B3059765
theorem B2293859 : Blo 1207921 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B1720435 : Blo 1207921 1720435 := bstep (se 1 (by rfl) ⟨1290326, by rfl⟩ : syracuseStep 1720435 = 2580653) B2580653
theorem B1360003 : Blo 1207921 1360003 := bstep (se 1 (by rfl) ⟨1020002, by rfl⟩ : syracuseStep 1360003 = 2040005) B2040005
theorem B2719889 : Blo 1207921 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B2719907 : Blo 1207921 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B2039971 : Blo 1207921 2039971 := bstep (se 1 (by rfl) ⟨1529978, by rfl⟩ : syracuseStep 2039971 = 3059957) B3059957
theorem B1720531 : Blo 1207921 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B9928973 : Blo 1207921 9928973 := bstep (se 3 (by rfl) ⟨1861682, by rfl⟩ : syracuseStep 9928973 = 3723365) B3723365
theorem B1360147 : Blo 1207921 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B2040113 : Blo 1207921 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B6881669 : Blo 1207921 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B1360291 : Blo 1207921 1360291 := bstep (se 1 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 1360291 = 2040437) B2040437
theorem B2720177 : Blo 1207921 2720177 := bstep (se 2 (by rfl) ⟨1020066, by rfl⟩ : syracuseStep 2720177 = 2040133) B2040133
theorem B2040241 : Blo 1207921 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B2720195 : Blo 1207921 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B4080077 : Blo 1207921 4080077 := bstep (se 3 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 4080077 = 1530029) B1530029
theorem B2040275 : Blo 1207921 2040275 := bstep (se 1 (by rfl) ⟨1530206, by rfl⟩ : syracuseStep 2040275 = 3060413) B3060413
theorem B5161457 : Blo 1207921 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B4080131 : Blo 1207921 4080131 := bstep (se 1 (by rfl) ⟨3060098, by rfl⟩ : syracuseStep 4080131 = 6120197) B6120197
theorem B1360435 : Blo 1207921 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B2040403 : Blo 1207921 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B6120035 : Blo 1207921 6120035 := bstep (se 1 (by rfl) ⟨4590026, by rfl⟩ : syracuseStep 6120035 = 9180053) B9180053
theorem B7070321 : Blo 1207921 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B2581105 : Blo 1207921 2581105 := bstep (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) B1935829
theorem B3441325 : Blo 1207921 3441325 := bstep (se 3 (by rfl) ⟨645248, by rfl⟩ : syracuseStep 3441325 = 1290497) B1290497
theorem B1721027 : Blo 1207921 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B1360579 : Blo 1207921 1360579 := bstep (se 1 (by rfl) ⟨1020434, by rfl⟩ : syracuseStep 1360579 = 2040869) B2040869
theorem B9183941 : Blo 1207921 9183941 := bstep (se 4 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 9183941 = 1721989) B1721989
theorem B2720465 : Blo 1207921 2720465 := bstep (se 2 (by rfl) ⟨1020174, by rfl⟩ : syracuseStep 2720465 = 2040349) B2040349
theorem B2040545 : Blo 1207921 2040545 := bstep (se 2 (by rfl) ⟨765204, by rfl⟩ : syracuseStep 2040545 = 1530409) B1530409
theorem B2720483 : Blo 1207921 2720483 := bstep (se 1 (by rfl) ⟨2040362, by rfl⟩ : syracuseStep 2720483 = 4080725) B4080725
theorem B5104397 : Blo 1207921 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B4080401 : Blo 1207921 4080401 := bstep (se 2 (by rfl) ⟨1530150, by rfl⟩ : syracuseStep 4080401 = 3060301) B3060301
theorem B2040673 : Blo 1207921 2040673 := bstep (se 2 (by rfl) ⟨765252, by rfl⟩ : syracuseStep 2040673 = 1530505) B1530505
theorem B3924845 : Blo 1207921 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B2040707 : Blo 1207921 2040707 := bstep (se 1 (by rfl) ⟨1530530, by rfl⟩ : syracuseStep 2040707 = 3061061) B3061061
theorem B5235619 : Blo 1207921 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B13067189 : Blo 1207921 13067189 := bstep (se 5 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 13067189 = 1225049) B1225049
theorem B2720753 : Blo 1207921 2720753 := bstep (se 2 (by rfl) ⟨1020282, by rfl⟩ : syracuseStep 2720753 = 2040565) B2040565
theorem B2720771 : Blo 1207921 2720771 := bstep (se 1 (by rfl) ⟨2040578, by rfl⟩ : syracuseStep 2720771 = 4081157) B4081157
theorem B2040835 : Blo 1207921 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B2294801 : Blo 1207921 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B6882353 : Blo 1207921 6882353 := bstep (se 2 (by rfl) ⟨2580882, by rfl⟩ : syracuseStep 6882353 = 5161765) B5161765
theorem B4588721 : Blo 1207921 4588721 := bstep (se 2 (by rfl) ⟨1720770, by rfl⟩ : syracuseStep 4588721 = 3441541) B3441541
theorem B8062193 : Blo 1207921 8062193 := bstep (se 2 (by rfl) ⟨3023322, by rfl⟩ : syracuseStep 8062193 = 6046645) B6046645
theorem B2721041 : Blo 1207921 2721041 := bstep (se 2 (by rfl) ⟨1020390, by rfl⟩ : syracuseStep 2721041 = 2040781) B2040781
theorem B2721059 : Blo 1207921 2721059 := bstep (se 1 (by rfl) ⟨2040794, by rfl⟩ : syracuseStep 2721059 = 4081589) B4081589
theorem B4080941 : Blo 1207921 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B1721665 : Blo 1207921 1721665 := bstep (se 2 (by rfl) ⟨645624, by rfl⟩ : syracuseStep 1721665 = 1291249) B1291249
theorem B4080995 : Blo 1207921 4080995 := bstep (se 1 (by rfl) ⟨3060746, by rfl⟩ : syracuseStep 4080995 = 6121493) B6121493
theorem B6120845 : Blo 1207921 6120845 := bstep (se 3 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 6120845 = 2295317) B2295317
theorem B1811891 : Blo 1207921 1811891 := bstep (se 1 (by rfl) ⟨1358918, by rfl⟩ : syracuseStep 1811891 = 2717837) B2717837
theorem B1811921 : Blo 1207921 1811921 := bstep (se 2 (by rfl) ⟨679470, by rfl⟩ : syracuseStep 1811921 = 1358941) B1358941
theorem B1811939 : Blo 1207921 1811939 := bstep (se 1 (by rfl) ⟨1358954, by rfl⟩ : syracuseStep 1811939 = 2717909) B2717909
theorem B1811969 : Blo 1207921 1811969 := bstep (se 2 (by rfl) ⟨679488, by rfl⟩ : syracuseStep 1811969 = 1358977) B1358977
theorem B13608461 : Blo 1207921 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B1811987 : Blo 1207921 1811987 := bstep (se 1 (by rfl) ⟨1358990, by rfl⟩ : syracuseStep 1811987 = 2717981) B2717981
theorem B1812017 : Blo 1207921 1812017 := bstep (se 2 (by rfl) ⟨679506, by rfl⟩ : syracuseStep 1812017 = 1359013) B1359013
theorem B1812035 : Blo 1207921 1812035 := bstep (se 1 (by rfl) ⟨1359026, by rfl⟩ : syracuseStep 1812035 = 2718053) B2718053
theorem B1934945 : Blo 1207921 1934945 := bstep (se 2 (by rfl) ⟨725604, by rfl⟩ : syracuseStep 1934945 = 1451209) B1451209
theorem B1812065 : Blo 1207921 1812065 := bstep (se 2 (by rfl) ⟨679524, by rfl⟩ : syracuseStep 1812065 = 1359049) B1359049
theorem B4081265 : Blo 1207921 4081265 := bstep (se 2 (by rfl) ⟨1530474, by rfl⟩ : syracuseStep 4081265 = 3060949) B3060949
theorem B1812083 : Blo 1207921 1812083 := bstep (se 1 (by rfl) ⟨1359062, by rfl⟩ : syracuseStep 1812083 = 2718125) B2718125
theorem B1812113 : Blo 1207921 1812113 := bstep (se 2 (by rfl) ⟨679542, by rfl⟩ : syracuseStep 1812113 = 1359085) B1359085
theorem B1722001 : Blo 1207921 1722001 := bstep (se 2 (by rfl) ⟨645750, by rfl⟩ : syracuseStep 1722001 = 1291501) B1291501
theorem B1812131 : Blo 1207921 1812131 := bstep (se 1 (by rfl) ⟨1359098, by rfl⟩ : syracuseStep 1812131 = 2718197) B2718197
theorem B1812161 : Blo 1207921 1812161 := bstep (se 2 (by rfl) ⟨679560, by rfl⟩ : syracuseStep 1812161 = 1359121) B1359121
theorem B1812179 : Blo 1207921 1812179 := bstep (se 1 (by rfl) ⟨1359134, by rfl⟩ : syracuseStep 1812179 = 2718269) B2718269
theorem B5162723 : Blo 1207921 5162723 := bstep (se 1 (by rfl) ⟨3872042, by rfl⟩ : syracuseStep 5162723 = 7744085) B7744085
theorem B1812209 : Blo 1207921 1812209 := bstep (se 2 (by rfl) ⟨679578, by rfl⟩ : syracuseStep 1812209 = 1359157) B1359157
theorem B1812227 : Blo 1207921 1812227 := bstep (se 1 (by rfl) ⟨1359170, by rfl⟩ : syracuseStep 1812227 = 2718341) B2718341
theorem B1935137 : Blo 1207921 1935137 := bstep (se 2 (by rfl) ⟨725676, by rfl⟩ : syracuseStep 1935137 = 1451353) B1451353
theorem B1812257 : Blo 1207921 1812257 := bstep (se 2 (by rfl) ⟨679596, by rfl⟩ : syracuseStep 1812257 = 1359193) B1359193
theorem B2451235 : Blo 1207921 2451235 := bstep (se 1 (by rfl) ⟨1838426, by rfl⟩ : syracuseStep 2451235 = 3676853) B3676853
theorem B1812275 : Blo 1207921 1812275 := bstep (se 1 (by rfl) ⟨1359206, by rfl⟩ : syracuseStep 1812275 = 2718413) B2718413
theorem B1812305 : Blo 1207921 1812305 := bstep (se 2 (by rfl) ⟨679614, by rfl⟩ : syracuseStep 1812305 = 1359229) B1359229
theorem B1812323 : Blo 1207921 1812323 := bstep (se 1 (by rfl) ⟨1359242, by rfl⟩ : syracuseStep 1812323 = 2718485) B2718485
theorem B1451891 : Blo 1207921 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B1812353 : Blo 1207921 1812353 := bstep (se 2 (by rfl) ⟨679632, by rfl⟩ : syracuseStep 1812353 = 1359265) B1359265
theorem B2295697 : Blo 1207921 2295697 := bstep (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) B1721773
theorem B1812371 : Blo 1207921 1812371 := bstep (se 1 (by rfl) ⟨1359278, by rfl⟩ : syracuseStep 1812371 = 2718557) B2718557
theorem B1935265 : Blo 1207921 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B1812401 : Blo 1207921 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B1812419 : Blo 1207921 1812419 := bstep (se 1 (by rfl) ⟨1359314, by rfl⟩ : syracuseStep 1812419 = 2718629) B2718629
theorem B11610053 : Blo 1207921 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B1812449 : Blo 1207921 1812449 := bstep (se 2 (by rfl) ⟨679668, by rfl⟩ : syracuseStep 1812449 = 1359337) B1359337
theorem B1812467 : Blo 1207921 1812467 := bstep (se 1 (by rfl) ⟨1359350, by rfl⟩ : syracuseStep 1812467 = 2718701) B2718701
theorem B1812497 : Blo 1207921 1812497 := bstep (se 2 (by rfl) ⟨679686, by rfl⟩ : syracuseStep 1812497 = 1359373) B1359373
theorem B1812515 : Blo 1207921 1812515 := bstep (se 1 (by rfl) ⟨1359386, by rfl⟩ : syracuseStep 1812515 = 2718773) B2718773
theorem B2295857 : Blo 1207921 2295857 := bstep (se 2 (by rfl) ⟨860946, by rfl⟩ : syracuseStep 2295857 = 1721893) B1721893
theorem B1812545 : Blo 1207921 1812545 := bstep (se 2 (by rfl) ⟨679704, by rfl⟩ : syracuseStep 1812545 = 1359409) B1359409
theorem B2615377 : Blo 1207921 2615377 := bstep (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) B1961533
theorem B1812563 : Blo 1207921 1812563 := bstep (se 1 (by rfl) ⟨1359422, by rfl⟩ : syracuseStep 1812563 = 2718845) B2718845
theorem B1812593 : Blo 1207921 1812593 := bstep (se 2 (by rfl) ⟨679722, by rfl⟩ : syracuseStep 1812593 = 1359445) B1359445
theorem B1812611 : Blo 1207921 1812611 := bstep (se 1 (by rfl) ⟨1359458, by rfl⟩ : syracuseStep 1812611 = 2718917) B2718917
theorem B1812641 : Blo 1207921 1812641 := bstep (se 2 (by rfl) ⟨679740, by rfl⟩ : syracuseStep 1812641 = 1359481) B1359481
theorem B8267939 : Blo 1207921 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B1812659 : Blo 1207921 1812659 := bstep (se 1 (by rfl) ⟨1359494, by rfl⟩ : syracuseStep 1812659 = 2718989) B2718989
theorem B1812689 : Blo 1207921 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B1812707 : Blo 1207921 1812707 := bstep (se 1 (by rfl) ⟨1359530, by rfl⟩ : syracuseStep 1812707 = 2719061) B2719061
theorem B1812737 : Blo 1207921 1812737 := bstep (se 2 (by rfl) ⟨679776, by rfl⟩ : syracuseStep 1812737 = 1359553) B1359553
theorem B1812755 : Blo 1207921 1812755 := bstep (se 1 (by rfl) ⟨1359566, by rfl⟩ : syracuseStep 1812755 = 2719133) B2719133
theorem B1812785 : Blo 1207921 1812785 := bstep (se 2 (by rfl) ⟨679794, by rfl⟩ : syracuseStep 1812785 = 1359589) B1359589
theorem B1812803 : Blo 1207921 1812803 := bstep (se 1 (by rfl) ⟨1359602, by rfl⟩ : syracuseStep 1812803 = 2719205) B2719205
theorem B12912965 : Blo 1207921 12912965 := bstep (se 4 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 12912965 = 2421181) B2421181
theorem B1812833 : Blo 1207921 1812833 := bstep (se 2 (by rfl) ⟨679812, by rfl⟩ : syracuseStep 1812833 = 1359625) B1359625
theorem B3058033 : Blo 1207921 3058033 := bstep (se 2 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 3058033 = 2293525) B2293525
theorem B13764977 : Blo 1207921 13764977 := bstep (se 2 (by rfl) ⟨5161866, by rfl⟩ : syracuseStep 13764977 = 10323733) B10323733
theorem B1812851 : Blo 1207921 1812851 := bstep (se 1 (by rfl) ⟨1359638, by rfl⟩ : syracuseStep 1812851 = 2719277) B2719277
theorem B3443057 : Blo 1207921 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B1812881 : Blo 1207921 1812881 := bstep (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) B1359661
theorem B1812899 : Blo 1207921 1812899 := bstep (se 1 (by rfl) ⟨1359674, by rfl⟩ : syracuseStep 1812899 = 2719349) B2719349
theorem B1812929 : Blo 1207921 1812929 := bstep (se 2 (by rfl) ⟨679848, by rfl⟩ : syracuseStep 1812929 = 1359697) B1359697
theorem B1812947 : Blo 1207921 1812947 := bstep (se 1 (by rfl) ⟨1359710, by rfl⟩ : syracuseStep 1812947 = 2719421) B2719421
theorem B6883811 : Blo 1207921 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B1812977 : Blo 1207921 1812977 := bstep (se 2 (by rfl) ⟨679866, by rfl⟩ : syracuseStep 1812977 = 1359733) B1359733
theorem B1812995 : Blo 1207921 1812995 := bstep (se 1 (by rfl) ⟨1359746, by rfl⟩ : syracuseStep 1812995 = 2719493) B2719493
theorem B1935905 : Blo 1207921 1935905 := bstep (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) B1451929
theorem B1813025 : Blo 1207921 1813025 := bstep (se 2 (by rfl) ⟨679884, by rfl⟩ : syracuseStep 1813025 = 1359769) B1359769
theorem B3443249 : Blo 1207921 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B1813043 : Blo 1207921 1813043 := bstep (se 1 (by rfl) ⟨1359782, by rfl⟩ : syracuseStep 1813043 = 2719565) B2719565
theorem B1813073 : Blo 1207921 1813073 := bstep (se 2 (by rfl) ⟨679902, by rfl⟩ : syracuseStep 1813073 = 1359805) B1359805
theorem B1813091 : Blo 1207921 1813091 := bstep (se 1 (by rfl) ⟨1359818, by rfl⟩ : syracuseStep 1813091 = 2719637) B2719637
theorem B4590179 : Blo 1207921 4590179 := bstep (se 1 (by rfl) ⟨3442634, by rfl⟩ : syracuseStep 4590179 = 6885269) B6885269
theorem B1813121 : Blo 1207921 1813121 := bstep (se 2 (by rfl) ⟨679920, by rfl⟩ : syracuseStep 1813121 = 1359841) B1359841
theorem B3058307 : Blo 1207921 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B1813139 : Blo 1207921 1813139 := bstep (se 1 (by rfl) ⟨1359854, by rfl⟩ : syracuseStep 1813139 = 2719709) B2719709
theorem B1813169 : Blo 1207921 1813169 := bstep (se 2 (by rfl) ⟨679938, by rfl⟩ : syracuseStep 1813169 = 1359877) B1359877
theorem B1813187 : Blo 1207921 1813187 := bstep (se 1 (by rfl) ⟨1359890, by rfl⟩ : syracuseStep 1813187 = 2719781) B2719781
theorem B1813217 : Blo 1207921 1813217 := bstep (se 2 (by rfl) ⟨679956, by rfl⟩ : syracuseStep 1813217 = 1359913) B1359913
theorem B1813235 : Blo 1207921 1813235 := bstep (se 1 (by rfl) ⟨1359926, by rfl⟩ : syracuseStep 1813235 = 2719853) B2719853
theorem B1813265 : Blo 1207921 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B1813283 : Blo 1207921 1813283 := bstep (se 1 (by rfl) ⟨1359962, by rfl⟩ : syracuseStep 1813283 = 2719925) B2719925
theorem B1379107 : Blo 1207921 1379107 := bstep (se 1 (by rfl) ⟨1034330, by rfl⟩ : syracuseStep 1379107 = 2068661) B2068661
theorem B2616113 : Blo 1207921 2616113 := bstep (se 2 (by rfl) ⟨981042, by rfl⟩ : syracuseStep 2616113 = 1962085) B1962085
theorem B1813313 : Blo 1207921 1813313 := bstep (se 2 (by rfl) ⟨679992, by rfl⟩ : syracuseStep 1813313 = 1359985) B1359985
theorem B3058499 : Blo 1207921 3058499 := bstep (se 1 (by rfl) ⟨2293874, by rfl⟩ : syracuseStep 3058499 = 4587749) B4587749
theorem B1813331 : Blo 1207921 1813331 := bstep (se 1 (by rfl) ⟨1359998, by rfl⟩ : syracuseStep 1813331 = 2719997) B2719997
theorem B2485073 : Blo 1207921 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B1813361 : Blo 1207921 1813361 := bstep (se 2 (by rfl) ⟨680010, by rfl⟩ : syracuseStep 1813361 = 1360021) B1360021
theorem B1837939 : Blo 1207921 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B1813379 : Blo 1207921 1813379 := bstep (se 1 (by rfl) ⟨1360034, by rfl⟩ : syracuseStep 1813379 = 2720069) B2720069
theorem B1813409 : Blo 1207921 1813409 := bstep (se 2 (by rfl) ⟨680028, by rfl⟩ : syracuseStep 1813409 = 1360057) B1360057
theorem B1813427 : Blo 1207921 1813427 := bstep (se 1 (by rfl) ⟨1360070, by rfl⟩ : syracuseStep 1813427 = 2720141) B2720141
theorem B1813457 : Blo 1207921 1813457 := bstep (se 2 (by rfl) ⟨680046, by rfl⟩ : syracuseStep 1813457 = 1360093) B1360093
theorem B1813475 : Blo 1207921 1813475 := bstep (se 1 (by rfl) ⟨1360106, by rfl⟩ : syracuseStep 1813475 = 2720213) B2720213
theorem B6204401 : Blo 1207921 6204401 := bstep (se 2 (by rfl) ⟨2326650, by rfl⟩ : syracuseStep 6204401 = 4653301) B4653301
theorem B1813505 : Blo 1207921 1813505 := bstep (se 2 (by rfl) ⟨680064, by rfl⟩ : syracuseStep 1813505 = 1360129) B1360129
theorem B1813523 : Blo 1207921 1813523 := bstep (se 1 (by rfl) ⟨1360142, by rfl⟩ : syracuseStep 1813523 = 2720285) B2720285
theorem B2903089 : Blo 1207921 2903089 := bstep (se 2 (by rfl) ⟨1088658, by rfl⟩ : syracuseStep 2903089 = 2177317) B2177317
theorem B1813553 : Blo 1207921 1813553 := bstep (se 2 (by rfl) ⟨680082, by rfl⟩ : syracuseStep 1813553 = 1360165) B1360165
theorem B1813571 : Blo 1207921 1813571 := bstep (se 1 (by rfl) ⟨1360178, by rfl⟩ : syracuseStep 1813571 = 2720357) B2720357
theorem B1813601 : Blo 1207921 1813601 := bstep (se 2 (by rfl) ⟨680100, by rfl⟩ : syracuseStep 1813601 = 1360201) B1360201
theorem B1813619 : Blo 1207921 1813619 := bstep (se 1 (by rfl) ⟨1360214, by rfl⟩ : syracuseStep 1813619 = 2720429) B2720429
theorem B1838225 : Blo 1207921 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B1813649 : Blo 1207921 1813649 := bstep (se 2 (by rfl) ⟨680118, by rfl⟩ : syracuseStep 1813649 = 1360237) B1360237
theorem B1813667 : Blo 1207921 1813667 := bstep (se 1 (by rfl) ⟨1360250, by rfl⟩ : syracuseStep 1813667 = 2720501) B2720501
theorem B1633459 : Blo 1207921 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1813697 : Blo 1207921 1813697 := bstep (se 2 (by rfl) ⟨680136, by rfl⟩ : syracuseStep 1813697 = 1360273) B1360273
theorem B14699717 : Blo 1207921 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B23235781 : Blo 1207921 23235781 := bstep (se 4 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 23235781 = 4356709) B4356709
theorem B1813715 : Blo 1207921 1813715 := bstep (se 1 (by rfl) ⟨1360286, by rfl⟩ : syracuseStep 1813715 = 2720573) B2720573
theorem B1838305 : Blo 1207921 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B1813745 : Blo 1207921 1813745 := bstep (se 2 (by rfl) ⟨680154, by rfl⟩ : syracuseStep 1813745 = 1360309) B1360309
theorem B1813763 : Blo 1207921 1813763 := bstep (se 1 (by rfl) ⟨1360322, by rfl⟩ : syracuseStep 1813763 = 2720645) B2720645
theorem B3869965 : Blo 1207921 3869965 := bstep (se 3 (by rfl) ⟨725618, by rfl⟩ : syracuseStep 3869965 = 1451237) B1451237
theorem B1813793 : Blo 1207921 1813793 := bstep (se 2 (by rfl) ⟨680172, by rfl⟩ : syracuseStep 1813793 = 1360345) B1360345
theorem B1813811 : Blo 1207921 1813811 := bstep (se 1 (by rfl) ⟨1360358, by rfl⟩ : syracuseStep 1813811 = 2720717) B2720717
theorem B1813841 : Blo 1207921 1813841 := bstep (se 2 (by rfl) ⟨680190, by rfl⟩ : syracuseStep 1813841 = 1360381) B1360381
theorem B6532451 : Blo 1207921 6532451 := bstep (se 1 (by rfl) ⟨4899338, by rfl⟩ : syracuseStep 6532451 = 9798677) B9798677
theorem B1813859 : Blo 1207921 1813859 := bstep (se 1 (by rfl) ⟨1360394, by rfl⟩ : syracuseStep 1813859 = 2720789) B2720789
theorem B1813889 : Blo 1207921 1813889 := bstep (se 2 (by rfl) ⟨680208, by rfl⟩ : syracuseStep 1813889 = 1360417) B1360417
theorem B1813907 : Blo 1207921 1813907 := bstep (se 1 (by rfl) ⟨1360430, by rfl⟩ : syracuseStep 1813907 = 2720861) B2720861
theorem B1813937 : Blo 1207921 1813937 := bstep (se 2 (by rfl) ⟨680226, by rfl⟩ : syracuseStep 1813937 = 1360453) B1360453
theorem B1813955 : Blo 1207921 1813955 := bstep (se 1 (by rfl) ⟨1360466, by rfl⟩ : syracuseStep 1813955 = 2720933) B2720933
theorem B1813985 : Blo 1207921 1813985 := bstep (se 2 (by rfl) ⟨680244, by rfl⟩ : syracuseStep 1813985 = 1360489) B1360489
theorem B9178595 : Blo 1207921 9178595 := bstep (se 1 (by rfl) ⟨6883946, by rfl⟩ : syracuseStep 9178595 = 13767893) B13767893
theorem B1814003 : Blo 1207921 1814003 := bstep (se 1 (by rfl) ⟨1360502, by rfl⟩ : syracuseStep 1814003 = 2721005) B2721005
theorem B1814033 : Blo 1207921 1814033 := bstep (se 2 (by rfl) ⟨680262, by rfl⟩ : syracuseStep 1814033 = 1360525) B1360525
theorem B1814051 : Blo 1207921 1814051 := bstep (se 1 (by rfl) ⟨1360538, by rfl⟩ : syracuseStep 1814051 = 2721077) B2721077
theorem B1814081 : Blo 1207921 1814081 := bstep (se 2 (by rfl) ⟨680280, by rfl⟩ : syracuseStep 1814081 = 1360561) B1360561
theorem B4591181 : Blo 1207921 4591181 := bstep (se 3 (by rfl) ⟨860846, by rfl⟩ : syracuseStep 4591181 = 1721693) B1721693
theorem B1814099 : Blo 1207921 1814099 := bstep (se 1 (by rfl) ⟨1360574, by rfl⟩ : syracuseStep 1814099 = 2721149) B2721149
theorem B1814129 : Blo 1207921 1814129 := bstep (se 2 (by rfl) ⟨680298, by rfl⟩ : syracuseStep 1814129 = 1360597) B1360597
theorem B1207923 : Blo 1207921 1207923 := bstep (se 1 (by rfl) ⟨905942, by rfl⟩ : syracuseStep 1207923 = 1811885) B1811885
theorem B1207939 : Blo 1207921 1207939 := bstep (se 1 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 1207939 = 1811909) B1811909
theorem B1207955 : Blo 1207921 1207955 := bstep (se 1 (by rfl) ⟨905966, by rfl⟩ : syracuseStep 1207955 = 1811933) B1811933
theorem B1633939 : Blo 1207921 1633939 := bstep (se 1 (by rfl) ⟨1225454, by rfl⟩ : syracuseStep 1633939 = 2450909) B2450909
theorem B1207971 : Blo 1207921 1207971 := bstep (se 1 (by rfl) ⟨905978, by rfl⟩ : syracuseStep 1207971 = 1811957) B1811957
theorem B1207987 : Blo 1207921 1207987 := bstep (se 1 (by rfl) ⟨905990, by rfl⟩ : syracuseStep 1207987 = 1811981) B1811981
theorem B1208003 : Blo 1207921 1208003 := bstep (se 1 (by rfl) ⟨906002, by rfl⟩ : syracuseStep 1208003 = 1812005) B1812005
theorem B1208019 : Blo 1207921 1208019 := bstep (se 1 (by rfl) ⟨906014, by rfl⟩ : syracuseStep 1208019 = 1812029) B1812029
theorem B1208035 : Blo 1207921 1208035 := bstep (se 1 (by rfl) ⟨906026, by rfl⟩ : syracuseStep 1208035 = 1812053) B1812053
theorem B3059441 : Blo 1207921 3059441 := bstep (se 2 (by rfl) ⟨1147290, by rfl⟩ : syracuseStep 3059441 = 2294581) B2294581
theorem B1208051 : Blo 1207921 1208051 := bstep (se 1 (by rfl) ⟨906038, by rfl⟩ : syracuseStep 1208051 = 1812077) B1812077
theorem B1208067 : Blo 1207921 1208067 := bstep (se 1 (by rfl) ⟨906050, by rfl⟩ : syracuseStep 1208067 = 1812101) B1812101
theorem B3870467 : Blo 1207921 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B1208083 : Blo 1207921 1208083 := bstep (se 1 (by rfl) ⟨906062, by rfl⟩ : syracuseStep 1208083 = 1812125) B1812125
theorem B1208099 : Blo 1207921 1208099 := bstep (se 1 (by rfl) ⟨906074, by rfl⟩ : syracuseStep 1208099 = 1812149) B1812149
theorem B3059491 : Blo 1207921 3059491 := bstep (se 1 (by rfl) ⟨2294618, by rfl⟩ : syracuseStep 3059491 = 4589237) B4589237
theorem B1208115 : Blo 1207921 1208115 := bstep (se 1 (by rfl) ⟨906086, by rfl⟩ : syracuseStep 1208115 = 1812173) B1812173
theorem B1208131 : Blo 1207921 1208131 := bstep (se 1 (by rfl) ⟨906098, by rfl⟩ : syracuseStep 1208131 = 1812197) B1812197
theorem B1208147 : Blo 1207921 1208147 := bstep (se 1 (by rfl) ⟨906110, by rfl⟩ : syracuseStep 1208147 = 1812221) B1812221
theorem B1208163 : Blo 1207921 1208163 := bstep (se 1 (by rfl) ⟨906122, by rfl⟩ : syracuseStep 1208163 = 1812245) B1812245
theorem B4968305 : Blo 1207921 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B1208179 : Blo 1207921 1208179 := bstep (se 1 (by rfl) ⟨906134, by rfl⟩ : syracuseStep 1208179 = 1812269) B1812269
theorem B1208195 : Blo 1207921 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B1208211 : Blo 1207921 1208211 := bstep (se 1 (by rfl) ⟨906158, by rfl⟩ : syracuseStep 1208211 = 1812317) B1812317
theorem B1208227 : Blo 1207921 1208227 := bstep (se 1 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 1208227 = 1812341) B1812341
theorem B3059633 : Blo 1207921 3059633 := bstep (se 2 (by rfl) ⟨1147362, by rfl⟩ : syracuseStep 3059633 = 2294725) B2294725
theorem B1208243 : Blo 1207921 1208243 := bstep (se 1 (by rfl) ⟨906182, by rfl⟩ : syracuseStep 1208243 = 1812365) B1812365
theorem B1208259 : Blo 1207921 1208259 := bstep (se 1 (by rfl) ⟨906194, by rfl⟩ : syracuseStep 1208259 = 1812389) B1812389
theorem B1208275 : Blo 1207921 1208275 := bstep (se 1 (by rfl) ⟨906206, by rfl⟩ : syracuseStep 1208275 = 1812413) B1812413
theorem B1208291 : Blo 1207921 1208291 := bstep (se 1 (by rfl) ⟨906218, by rfl⟩ : syracuseStep 1208291 = 1812437) B1812437
theorem B1208307 : Blo 1207921 1208307 := bstep (se 1 (by rfl) ⟨906230, by rfl⟩ : syracuseStep 1208307 = 1812461) B1812461
theorem B1208323 : Blo 1207921 1208323 := bstep (se 1 (by rfl) ⟨906242, by rfl⟩ : syracuseStep 1208323 = 1812485) B1812485
theorem B1208339 : Blo 1207921 1208339 := bstep (se 1 (by rfl) ⟨906254, by rfl⟩ : syracuseStep 1208339 = 1812509) B1812509
theorem B1208355 : Blo 1207921 1208355 := bstep (se 1 (by rfl) ⟨906266, by rfl⟩ : syracuseStep 1208355 = 1812533) B1812533
theorem B1208371 : Blo 1207921 1208371 := bstep (se 1 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 1208371 = 1812557) B1812557
theorem B1208387 : Blo 1207921 1208387 := bstep (se 1 (by rfl) ⟨906290, by rfl⟩ : syracuseStep 1208387 = 1812581) B1812581
theorem B1208403 : Blo 1207921 1208403 := bstep (se 1 (by rfl) ⟨906302, by rfl⟩ : syracuseStep 1208403 = 1812605) B1812605
theorem B1208419 : Blo 1207921 1208419 := bstep (se 1 (by rfl) ⟨906314, by rfl⟩ : syracuseStep 1208419 = 1812629) B1812629
theorem B1208435 : Blo 1207921 1208435 := bstep (se 1 (by rfl) ⟨906326, by rfl⟩ : syracuseStep 1208435 = 1812653) B1812653
theorem B1208451 : Blo 1207921 1208451 := bstep (se 1 (by rfl) ⟨906338, by rfl⟩ : syracuseStep 1208451 = 1812677) B1812677
theorem B1208467 : Blo 1207921 1208467 := bstep (se 1 (by rfl) ⟨906350, by rfl⟩ : syracuseStep 1208467 = 1812701) B1812701
theorem B1208483 : Blo 1207921 1208483 := bstep (se 1 (by rfl) ⟨906362, by rfl⟩ : syracuseStep 1208483 = 1812725) B1812725
theorem B1208499 : Blo 1207921 1208499 := bstep (se 1 (by rfl) ⟨906374, by rfl⟩ : syracuseStep 1208499 = 1812749) B1812749
theorem B1208515 : Blo 1207921 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B1208531 : Blo 1207921 1208531 := bstep (se 1 (by rfl) ⟨906398, by rfl⟩ : syracuseStep 1208531 = 1812797) B1812797
theorem B1208547 : Blo 1207921 1208547 := bstep (se 1 (by rfl) ⟨906410, by rfl⟩ : syracuseStep 1208547 = 1812821) B1812821
theorem B1208563 : Blo 1207921 1208563 := bstep (se 1 (by rfl) ⟨906422, by rfl⟩ : syracuseStep 1208563 = 1812845) B1812845
theorem B1208579 : Blo 1207921 1208579 := bstep (se 1 (by rfl) ⟨906434, by rfl⟩ : syracuseStep 1208579 = 1812869) B1812869
theorem B1208595 : Blo 1207921 1208595 := bstep (se 1 (by rfl) ⟨906446, by rfl⟩ : syracuseStep 1208595 = 1812893) B1812893
theorem B1208611 : Blo 1207921 1208611 := bstep (se 1 (by rfl) ⟨906458, by rfl⟩ : syracuseStep 1208611 = 1812917) B1812917
theorem B1208627 : Blo 1207921 1208627 := bstep (se 1 (by rfl) ⟨906470, by rfl⟩ : syracuseStep 1208627 = 1812941) B1812941
theorem B1208643 : Blo 1207921 1208643 := bstep (se 1 (by rfl) ⟨906482, by rfl⟩ : syracuseStep 1208643 = 1812965) B1812965
theorem B6115661 : Blo 1207921 6115661 := bstep (se 3 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 6115661 = 2293373) B2293373
theorem B2756945 : Blo 1207921 2756945 := bstep (se 2 (by rfl) ⟨1033854, by rfl⟩ : syracuseStep 2756945 = 2067709) B2067709
theorem B1208659 : Blo 1207921 1208659 := bstep (se 1 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 1208659 = 1812989) B1812989
theorem B1208675 : Blo 1207921 1208675 := bstep (se 1 (by rfl) ⟨906506, by rfl⟩ : syracuseStep 1208675 = 1813013) B1813013
theorem B1208691 : Blo 1207921 1208691 := bstep (se 1 (by rfl) ⟨906518, by rfl⟩ : syracuseStep 1208691 = 1813037) B1813037
theorem B1208707 : Blo 1207921 1208707 := bstep (se 1 (by rfl) ⟨906530, by rfl⟩ : syracuseStep 1208707 = 1813061) B1813061
theorem B1208723 : Blo 1207921 1208723 := bstep (se 1 (by rfl) ⟨906542, by rfl⟩ : syracuseStep 1208723 = 1813085) B1813085
theorem B1208739 : Blo 1207921 1208739 := bstep (se 1 (by rfl) ⟨906554, by rfl⟩ : syracuseStep 1208739 = 1813109) B1813109
theorem B1208755 : Blo 1207921 1208755 := bstep (se 1 (by rfl) ⟨906566, by rfl⟩ : syracuseStep 1208755 = 1813133) B1813133
theorem B1208771 : Blo 1207921 1208771 := bstep (se 1 (by rfl) ⟨906578, by rfl⟩ : syracuseStep 1208771 = 1813157) B1813157
theorem B19124677 : Blo 1207921 19124677 := bstep (se 4 (by rfl) ⟨1792938, by rfl⟩ : syracuseStep 19124677 = 3585877) B3585877
theorem B1208787 : Blo 1207921 1208787 := bstep (se 1 (by rfl) ⟨906590, by rfl⟩ : syracuseStep 1208787 = 1813181) B1813181
theorem B1208803 : Blo 1207921 1208803 := bstep (se 1 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 1208803 = 1813205) B1813205
theorem B1208819 : Blo 1207921 1208819 := bstep (se 1 (by rfl) ⟨906614, by rfl⟩ : syracuseStep 1208819 = 1813229) B1813229
theorem B1208835 : Blo 1207921 1208835 := bstep (se 1 (by rfl) ⟨906626, by rfl⟩ : syracuseStep 1208835 = 1813253) B1813253
theorem B4133393 : Blo 1207921 4133393 := bstep (se 2 (by rfl) ⟨1550022, by rfl⟩ : syracuseStep 4133393 = 3100045) B3100045
theorem B1208851 : Blo 1207921 1208851 := bstep (se 1 (by rfl) ⟨906638, by rfl⟩ : syracuseStep 1208851 = 1813277) B1813277
theorem B1208867 : Blo 1207921 1208867 := bstep (se 1 (by rfl) ⟨906650, by rfl⟩ : syracuseStep 1208867 = 1813301) B1813301
theorem B1208883 : Blo 1207921 1208883 := bstep (se 1 (by rfl) ⟨906662, by rfl⟩ : syracuseStep 1208883 = 1813325) B1813325
theorem B1208899 : Blo 1207921 1208899 := bstep (se 1 (by rfl) ⟨906674, by rfl⟩ : syracuseStep 1208899 = 1813349) B1813349
theorem B1208915 : Blo 1207921 1208915 := bstep (se 1 (by rfl) ⟨906686, by rfl⟩ : syracuseStep 1208915 = 1813373) B1813373
theorem B1208931 : Blo 1207921 1208931 := bstep (se 1 (by rfl) ⟨906698, by rfl⟩ : syracuseStep 1208931 = 1813397) B1813397
theorem B1208947 : Blo 1207921 1208947 := bstep (se 1 (by rfl) ⟨906710, by rfl⟩ : syracuseStep 1208947 = 1813421) B1813421
theorem B1208963 : Blo 1207921 1208963 := bstep (se 1 (by rfl) ⟨906722, by rfl⟩ : syracuseStep 1208963 = 1813445) B1813445
theorem B1208979 : Blo 1207921 1208979 := bstep (se 1 (by rfl) ⟨906734, by rfl⟩ : syracuseStep 1208979 = 1813469) B1813469
theorem B1208995 : Blo 1207921 1208995 := bstep (se 1 (by rfl) ⟨906746, by rfl⟩ : syracuseStep 1208995 = 1813493) B1813493
theorem B1209011 : Blo 1207921 1209011 := bstep (se 1 (by rfl) ⟨906758, by rfl⟩ : syracuseStep 1209011 = 1813517) B1813517
theorem B13251253 : Blo 1207921 13251253 := bstep (se 5 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 13251253 = 1242305) B1242305
theorem B1209027 : Blo 1207921 1209027 := bstep (se 1 (by rfl) ⟨906770, by rfl⟩ : syracuseStep 1209027 = 1813541) B1813541
theorem B1209043 : Blo 1207921 1209043 := bstep (se 1 (by rfl) ⟨906782, by rfl⟩ : syracuseStep 1209043 = 1813565) B1813565
theorem B2757347 : Blo 1207921 2757347 := bstep (se 1 (by rfl) ⟨2068010, by rfl⟩ : syracuseStep 2757347 = 4136021) B4136021
theorem B1209059 : Blo 1207921 1209059 := bstep (se 1 (by rfl) ⟨906794, by rfl⟩ : syracuseStep 1209059 = 1813589) B1813589
theorem B1209075 : Blo 1207921 1209075 := bstep (se 1 (by rfl) ⟨906806, by rfl⟩ : syracuseStep 1209075 = 1813613) B1813613
theorem B1209091 : Blo 1207921 1209091 := bstep (se 1 (by rfl) ⟨906818, by rfl⟩ : syracuseStep 1209091 = 1813637) B1813637
theorem B1209107 : Blo 1207921 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B1209123 : Blo 1207921 1209123 := bstep (se 1 (by rfl) ⟨906842, by rfl⟩ : syracuseStep 1209123 = 1813685) B1813685
theorem B1209139 : Blo 1207921 1209139 := bstep (se 1 (by rfl) ⟨906854, by rfl⟩ : syracuseStep 1209139 = 1813709) B1813709
theorem B1209155 : Blo 1207921 1209155 := bstep (se 1 (by rfl) ⟨906866, by rfl⟩ : syracuseStep 1209155 = 1813733) B1813733
theorem B1209171 : Blo 1207921 1209171 := bstep (se 1 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 1209171 = 1813757) B1813757
theorem B1209187 : Blo 1207921 1209187 := bstep (se 1 (by rfl) ⟨906890, by rfl⟩ : syracuseStep 1209187 = 1813781) B1813781
theorem B3265393 : Blo 1207921 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B1209203 : Blo 1207921 1209203 := bstep (se 1 (by rfl) ⟨906902, by rfl⟩ : syracuseStep 1209203 = 1813805) B1813805
theorem B1209219 : Blo 1207921 1209219 := bstep (se 1 (by rfl) ⟨906914, by rfl⟩ : syracuseStep 1209219 = 1813829) B1813829
theorem B3060625 : Blo 1207921 3060625 := bstep (se 2 (by rfl) ⟨1147734, by rfl⟩ : syracuseStep 3060625 = 2295469) B2295469
theorem B1209235 : Blo 1207921 1209235 := bstep (se 1 (by rfl) ⟨906926, by rfl⟩ : syracuseStep 1209235 = 1813853) B1813853
theorem B1209251 : Blo 1207921 1209251 := bstep (se 1 (by rfl) ⟨906938, by rfl⟩ : syracuseStep 1209251 = 1813877) B1813877
theorem B1209267 : Blo 1207921 1209267 := bstep (se 1 (by rfl) ⟨906950, by rfl⟩ : syracuseStep 1209267 = 1813901) B1813901
theorem B1209283 : Blo 1207921 1209283 := bstep (se 1 (by rfl) ⟨906962, by rfl⟩ : syracuseStep 1209283 = 1813925) B1813925
theorem B1209299 : Blo 1207921 1209299 := bstep (se 1 (by rfl) ⟨906974, by rfl⟩ : syracuseStep 1209299 = 1813949) B1813949
theorem B1209315 : Blo 1207921 1209315 := bstep (se 1 (by rfl) ⟨906986, by rfl⟩ : syracuseStep 1209315 = 1813973) B1813973
theorem B1209331 : Blo 1207921 1209331 := bstep (se 1 (by rfl) ⟨906998, by rfl⟩ : syracuseStep 1209331 = 1813997) B1813997
theorem B1209347 : Blo 1207921 1209347 := bstep (se 1 (by rfl) ⟨907010, by rfl⟩ : syracuseStep 1209347 = 1814021) B1814021
theorem B1209363 : Blo 1207921 1209363 := bstep (se 1 (by rfl) ⟨907022, by rfl⟩ : syracuseStep 1209363 = 1814045) B1814045
theorem B1209379 : Blo 1207921 1209379 := bstep (se 1 (by rfl) ⟨907034, by rfl⟩ : syracuseStep 1209379 = 1814069) B1814069
theorem B1209395 : Blo 1207921 1209395 := bstep (se 1 (by rfl) ⟨907046, by rfl⟩ : syracuseStep 1209395 = 1814093) B1814093
theorem B1209411 : Blo 1207921 1209411 := bstep (se 1 (by rfl) ⟨907058, by rfl⟩ : syracuseStep 1209411 = 1814117) B1814117
theorem B3060899 : Blo 1207921 3060899 := bstep (se 1 (by rfl) ⟨2295674, by rfl⟩ : syracuseStep 3060899 = 4591349) B4591349
theorem B1291475 : Blo 1207921 1291475 := bstep (se 1 (by rfl) ⟨968606, by rfl⟩ : syracuseStep 1291475 = 1937213) B1937213
theorem B7165189 : Blo 1207921 7165189 := bstep (se 4 (by rfl) ⟨671736, by rfl⟩ : syracuseStep 7165189 = 1343473) B1343473
theorem B3487043 : Blo 1207921 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B3061091 : Blo 1207921 3061091 := bstep (se 1 (by rfl) ⟨2295818, by rfl⟩ : syracuseStep 3061091 = 4591637) B4591637
theorem B1529219 : Blo 1207921 1529219 := bstep (se 1 (by rfl) ⟨1146914, by rfl⟩ : syracuseStep 1529219 = 2293829) B2293829
theorem B4076945 : Blo 1207921 4076945 := bstep (se 2 (by rfl) ⟨1528854, by rfl⟩ : syracuseStep 4076945 = 3057709) B3057709
theorem B3102097 : Blo 1207921 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B3872323 : Blo 1207921 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B6624845 : Blo 1207921 6624845 := bstep (se 3 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 6624845 = 2484317) B2484317
theorem B1963619 : Blo 1207921 1963619 := bstep (se 1 (by rfl) ⟨1472714, by rfl⟩ : syracuseStep 1963619 = 2945429) B2945429
theorem B6887045 : Blo 1207921 6887045 := bstep (se 4 (by rfl) ⟨645660, by rfl⟩ : syracuseStep 6887045 = 1291321) B1291321
theorem B8828557 : Blo 1207921 8828557 := bstep (se 3 (by rfl) ⟨1655354, by rfl⟩ : syracuseStep 8828557 = 3310709) B3310709
theorem B20936333 : Blo 1207921 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B11024099 : Blo 1207921 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B6371185 : Blo 1207921 6371185 := bstep (se 2 (by rfl) ⟨2389194, by rfl⟩ : syracuseStep 6371185 = 4778389) B4778389
theorem B4077485 : Blo 1207921 4077485 := bstep (se 3 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 4077485 = 1529057) B1529057
theorem B4077539 : Blo 1207921 4077539 := bstep (se 1 (by rfl) ⟨3058154, by rfl⟩ : syracuseStep 4077539 = 6116309) B6116309
theorem B3872785 : Blo 1207921 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1529923 : Blo 1207921 1529923 := bstep (se 1 (by rfl) ⟨1147442, by rfl⟩ : syracuseStep 1529923 = 2294885) B2294885
theorem B6887501 : Blo 1207921 6887501 := bstep (se 3 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 6887501 = 2582813) B2582813
theorem B3266669 : Blo 1207921 3266669 := bstep (se 3 (by rfl) ⟨612500, by rfl⟩ : syracuseStep 3266669 = 1225001) B1225001
theorem B1530019 : Blo 1207921 1530019 := bstep (se 1 (by rfl) ⟨1147514, by rfl⟩ : syracuseStep 1530019 = 2295029) B2295029
theorem B2717873 : Blo 1207921 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B2717891 : Blo 1207921 2717891 := bstep (se 1 (by rfl) ⟨2038418, by rfl⟩ : syracuseStep 2717891 = 4076837) B4076837
theorem B4077809 : Blo 1207921 4077809 := bstep (se 2 (by rfl) ⟨1529178, by rfl⟩ : syracuseStep 4077809 = 3058357) B3058357
theorem B7739725 : Blo 1207921 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B1309043 : Blo 1207921 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B2718161 : Blo 1207921 2718161 := bstep (se 2 (by rfl) ⟨1019310, by rfl⟩ : syracuseStep 2718161 = 2038621) B2038621
theorem B2718179 : Blo 1207921 2718179 := bstep (se 1 (by rfl) ⟨2038634, by rfl⟩ : syracuseStep 2718179 = 4077269) B4077269
theorem B7748131 : Blo 1207921 7748131 := bstep (se 1 (by rfl) ⟨5811098, by rfl⟩ : syracuseStep 7748131 = 11622197) B11622197
theorem B2038385 : Blo 1207921 2038385 := bstep (se 2 (by rfl) ⟨764394, by rfl⟩ : syracuseStep 2038385 = 1528789) B1528789
theorem B1530515 : Blo 1207921 1530515 := bstep (se 1 (by rfl) ⟨1147886, by rfl⟩ : syracuseStep 1530515 = 2295773) B2295773
theorem B2038513 : Blo 1207921 2038513 := bstep (se 2 (by rfl) ⟨764442, by rfl⟩ : syracuseStep 2038513 = 1528885) B1528885
theorem B2718449 : Blo 1207921 2718449 := bstep (se 2 (by rfl) ⟨1019418, by rfl⟩ : syracuseStep 2718449 = 2038837) B2038837
theorem B2718467 : Blo 1207921 2718467 := bstep (se 1 (by rfl) ⟨2038850, by rfl⟩ : syracuseStep 2718467 = 4077701) B4077701
theorem B4078349 : Blo 1207921 4078349 := bstep (se 3 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 4078349 = 1529381) B1529381
theorem B2038547 : Blo 1207921 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B4078403 : Blo 1207921 4078403 := bstep (se 1 (by rfl) ⟨3058802, by rfl⟩ : syracuseStep 4078403 = 6117605) B6117605
theorem B3267469 : Blo 1207921 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B2038675 : Blo 1207921 2038675 := bstep (se 1 (by rfl) ⟨1529006, by rfl⟩ : syracuseStep 2038675 = 3058013) B3058013
theorem B3980209 : Blo 1207921 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B3488707 : Blo 1207921 3488707 := bstep (se 1 (by rfl) ⟨2616530, by rfl⟩ : syracuseStep 3488707 = 5233061) B5233061
theorem B2718737 : Blo 1207921 2718737 := bstep (se 2 (by rfl) ⟨1019526, by rfl⟩ : syracuseStep 2718737 = 2039053) B2039053
theorem B2038817 : Blo 1207921 2038817 := bstep (se 2 (by rfl) ⟨764556, by rfl⟩ : syracuseStep 2038817 = 1529113) B1529113
theorem B2718755 : Blo 1207921 2718755 := bstep (se 1 (by rfl) ⟨2039066, by rfl⟩ : syracuseStep 2718755 = 4078133) B4078133
theorem B3726413 : Blo 1207921 3726413 := bstep (se 3 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 3726413 = 1397405) B1397405
theorem B4078673 : Blo 1207921 4078673 := bstep (se 2 (by rfl) ⟨1529502, by rfl⟩ : syracuseStep 4078673 = 3059005) B3059005
theorem B1358995 : Blo 1207921 1358995 := bstep (se 1 (by rfl) ⟨1019246, by rfl⟩ : syracuseStep 1358995 = 2038493) B2038493
theorem B2038945 : Blo 1207921 2038945 := bstep (se 2 (by rfl) ⟨764604, by rfl⟩ : syracuseStep 2038945 = 1529209) B1529209
theorem B6118577 : Blo 1207921 6118577 := bstep (se 2 (by rfl) ⟨2294466, by rfl⟩ : syracuseStep 6118577 = 4588933) B4588933
theorem B2038979 : Blo 1207921 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B1359139 : Blo 1207921 1359139 := bstep (se 1 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 1359139 = 2038709) B2038709
theorem B2719025 : Blo 1207921 2719025 := bstep (se 2 (by rfl) ⟨1019634, by rfl⟩ : syracuseStep 2719025 = 2039269) B2039269
theorem B2039107 : Blo 1207921 2039107 := bstep (se 1 (by rfl) ⟨1529330, by rfl⟩ : syracuseStep 2039107 = 3058661) B3058661
theorem B2719043 : Blo 1207921 2719043 := bstep (se 1 (by rfl) ⟨2039282, by rfl⟩ : syracuseStep 2719043 = 4078565) B4078565
theorem B10329443 : Blo 1207921 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B1359283 : Blo 1207921 1359283 := bstep (se 1 (by rfl) ⟨1019462, by rfl⟩ : syracuseStep 1359283 = 2038925) B2038925
theorem B8830405 : Blo 1207921 8830405 := bstep (se 4 (by rfl) ⟨827850, by rfl⟩ : syracuseStep 8830405 = 1655701) B1655701
theorem B2039249 : Blo 1207921 2039249 := bstep (se 2 (by rfl) ⟨764718, by rfl⟩ : syracuseStep 2039249 = 1529437) B1529437
theorem B3440141 : Blo 1207921 3440141 := bstep (se 3 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 3440141 = 1290053) B1290053
theorem B13762061 : Blo 1207921 13762061 := bstep (se 3 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 13762061 = 5160773) B5160773
theorem B1359427 : Blo 1207921 1359427 := bstep (se 1 (by rfl) ⟨1019570, by rfl⟩ : syracuseStep 1359427 = 2039141) B2039141
theorem B2039377 : Blo 1207921 2039377 := bstep (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) B1529533
theorem B2719313 : Blo 1207921 2719313 := bstep (se 2 (by rfl) ⟨1019742, by rfl⟩ : syracuseStep 2719313 = 2039485) B2039485
theorem B2719331 : Blo 1207921 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B2178659 : Blo 1207921 2178659 := bstep (se 1 (by rfl) ⟨1633994, by rfl⟩ : syracuseStep 2178659 = 3267989) B3267989
theorem B4079213 : Blo 1207921 4079213 := bstep (se 3 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 4079213 = 1529705) B1529705
theorem B2039411 : Blo 1207921 2039411 := bstep (se 1 (by rfl) ⟨1529558, by rfl⟩ : syracuseStep 2039411 = 3059117) B3059117
theorem B4079267 : Blo 1207921 4079267 := bstep (se 1 (by rfl) ⟨3059450, by rfl⟩ : syracuseStep 4079267 = 6118901) B6118901
theorem B3440333 : Blo 1207921 3440333 := bstep (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) B1290125
theorem B1359571 : Blo 1207921 1359571 := bstep (se 1 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 1359571 = 2039357) B2039357
theorem B2039539 : Blo 1207921 2039539 := bstep (se 1 (by rfl) ⟨1529654, by rfl⟩ : syracuseStep 2039539 = 3059309) B3059309
theorem B2293571 : Blo 1207921 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B1359715 : Blo 1207921 1359715 := bstep (se 1 (by rfl) ⟨1019786, by rfl⟩ : syracuseStep 1359715 = 2039573) B2039573
theorem B2719601 : Blo 1207921 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B2039681 : Blo 1207921 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B2719619 : Blo 1207921 2719619 := bstep (se 1 (by rfl) ⟨2039714, by rfl⟩ : syracuseStep 2719619 = 4079429) B4079429
theorem B2178947 : Blo 1207921 2178947 := bstep (se 1 (by rfl) ⟨1634210, by rfl⟩ : syracuseStep 2178947 = 3268421) B3268421
theorem B4079537 : Blo 1207921 4079537 := bstep (se 2 (by rfl) ⟨1529826, by rfl⟩ : syracuseStep 4079537 = 3059653) B3059653
theorem B1359859 : Blo 1207921 1359859 := bstep (se 1 (by rfl) ⟨1019894, by rfl⟩ : syracuseStep 1359859 = 2039789) B2039789
theorem B2719745 : Blo 1207921 2719745 := bstep (se 2 (by rfl) ⟨1019904, by rfl⟩ : syracuseStep 2719745 = 2039809) B2039809
theorem B1359895 : Blo 1207921 1359895 := bstep (se 1 (by rfl) ⟨1019921, by rfl⟩ : syracuseStep 1359895 = 2039843) B2039843
theorem B2039897 : Blo 1207921 2039897 := bstep (se 2 (by rfl) ⟨764961, by rfl⟩ : syracuseStep 2039897 = 1529923) B1529923
theorem B2293913 : Blo 1207921 2293913 := bstep (se 2 (by rfl) ⟨860217, by rfl⟩ : syracuseStep 2293913 = 1720435) B1720435
theorem B6619315 : Blo 1207921 6619315 := bstep (se 1 (by rfl) ⟨4964486, by rfl⟩ : syracuseStep 6619315 = 9928973) B9928973
theorem B1360075 : Blo 1207921 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B2719961 : Blo 1207921 2719961 := bstep (se 2 (by rfl) ⟨1019985, by rfl⟩ : syracuseStep 2719961 = 2039971) B2039971
theorem B2040025 : Blo 1207921 2040025 := bstep (se 2 (by rfl) ⟨765009, by rfl⟩ : syracuseStep 2040025 = 1530019) B1530019
theorem B4587779 : Blo 1207921 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B2720051 : Blo 1207921 2720051 := bstep (se 1 (by rfl) ⟨2040038, by rfl⟩ : syracuseStep 2720051 = 4080077) B4080077
theorem B1360183 : Blo 1207921 1360183 := bstep (se 1 (by rfl) ⟨1020137, by rfl⟩ : syracuseStep 1360183 = 2040275) B2040275
theorem B3440971 : Blo 1207921 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B2720087 : Blo 1207921 2720087 := bstep (se 1 (by rfl) ⟨2040065, by rfl⟩ : syracuseStep 2720087 = 4080131) B4080131
theorem B4080023 : Blo 1207921 4080023 := bstep (se 1 (by rfl) ⟨3060017, by rfl⟩ : syracuseStep 4080023 = 6120035) B6120035
theorem B1360363 : Blo 1207921 1360363 := bstep (se 1 (by rfl) ⟨1020272, by rfl⟩ : syracuseStep 1360363 = 2040545) B2040545
theorem B2720267 : Blo 1207921 2720267 := bstep (se 1 (by rfl) ⟨2040200, by rfl⟩ : syracuseStep 2720267 = 4080401) B4080401
theorem B2720321 : Blo 1207921 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B1360471 : Blo 1207921 1360471 := bstep (se 1 (by rfl) ⟨1020353, by rfl⟩ : syracuseStep 1360471 = 2040707) B2040707
theorem B4588235 : Blo 1207921 4588235 := bstep (se 1 (by rfl) ⟨3441176, by rfl⟩ : syracuseStep 4588235 = 6882353) B6882353
theorem B10330841 : Blo 1207921 10330841 := bstep (se 2 (by rfl) ⟨3874065, by rfl⟩ : syracuseStep 10330841 = 7748131) B7748131
theorem B2040599 : Blo 1207921 2040599 := bstep (se 1 (by rfl) ⟨1530449, by rfl⟩ : syracuseStep 2040599 = 3060899) B3060899
theorem B2720537 : Blo 1207921 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B3441473 : Blo 1207921 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B2720627 : Blo 1207921 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B4588433 : Blo 1207921 4588433 := bstep (se 2 (by rfl) ⟨1720662, by rfl⟩ : syracuseStep 4588433 = 3441325) B3441325
theorem B2720663 : Blo 1207921 2720663 := bstep (se 1 (by rfl) ⟨2040497, by rfl⟩ : syracuseStep 2720663 = 4080995) B4080995
theorem B2040727 : Blo 1207921 2040727 := bstep (se 1 (by rfl) ⟨1530545, by rfl⟩ : syracuseStep 2040727 = 3061091) B3061091
theorem B4080563 : Blo 1207921 4080563 := bstep (se 1 (by rfl) ⟨3060422, by rfl⟩ : syracuseStep 4080563 = 6120845) B6120845
theorem B3490781 : Blo 1207921 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B4416563 : Blo 1207921 4416563 := bstep (se 1 (by rfl) ⟨3312422, by rfl⟩ : syracuseStep 4416563 = 6624845) B6624845
theorem B2720843 : Blo 1207921 2720843 := bstep (se 1 (by rfl) ⟨2040632, by rfl⟩ : syracuseStep 2720843 = 4081265) B4081265
theorem B9176165 : Blo 1207921 9176165 := bstep (se 4 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 9176165 = 1720531) B1720531
theorem B2720897 : Blo 1207921 2720897 := bstep (se 2 (by rfl) ⟨1020336, by rfl⟩ : syracuseStep 2720897 = 2040673) B2040673
theorem B7349399 : Blo 1207921 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B3441815 : Blo 1207921 3441815 := bstep (se 1 (by rfl) ⟨2581361, by rfl⟩ : syracuseStep 3441815 = 5162723) B5162723
theorem B2450585 : Blo 1207921 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B4080833 : Blo 1207921 4080833 := bstep (se 2 (by rfl) ⟨1530312, by rfl⟩ : syracuseStep 4080833 = 3060625) B3060625
theorem B6980825 : Blo 1207921 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2721113 : Blo 1207921 2721113 := bstep (se 2 (by rfl) ⟨1020417, by rfl⟩ : syracuseStep 2721113 = 2040835) B2040835
theorem B1811915 : Blo 1207921 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B1811927 : Blo 1207921 1811927 := bstep (se 1 (by rfl) ⟨1358945, by rfl⟩ : syracuseStep 1811927 = 2717891) B2717891
theorem B1811993 : Blo 1207921 1811993 := bstep (se 2 (by rfl) ⟨679497, by rfl⟩ : syracuseStep 1811993 = 1358995) B1358995
theorem B9176651 : Blo 1207921 9176651 := bstep (se 1 (by rfl) ⟨6882488, by rfl⟩ : syracuseStep 9176651 = 13764977) B13764977
theorem B2295371 : Blo 1207921 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B2451073 : Blo 1207921 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B1812107 : Blo 1207921 1812107 := bstep (se 1 (by rfl) ⟨1359080, by rfl⟩ : syracuseStep 1812107 = 2718161) B2718161
theorem B1812119 : Blo 1207921 1812119 := bstep (se 1 (by rfl) ⟨1359089, by rfl⟩ : syracuseStep 1812119 = 2718179) B2718179
theorem B4589207 : Blo 1207921 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B1812185 : Blo 1207921 1812185 := bstep (se 2 (by rfl) ⟨679569, by rfl⟩ : syracuseStep 1812185 = 1359139) B1359139
theorem B4081373 : Blo 1207921 4081373 := bstep (se 3 (by rfl) ⟨765257, by rfl⟩ : syracuseStep 4081373 = 1530515) B1530515
theorem B2295553 : Blo 1207921 2295553 := bstep (se 2 (by rfl) ⟨860832, by rfl⟩ : syracuseStep 2295553 = 1721665) B1721665
theorem B1812299 : Blo 1207921 1812299 := bstep (se 1 (by rfl) ⟨1359224, by rfl⟩ : syracuseStep 1812299 = 2718449) B2718449
theorem B1812311 : Blo 1207921 1812311 := bstep (se 1 (by rfl) ⟨1359233, by rfl⟩ : syracuseStep 1812311 = 2718467) B2718467
theorem B4589405 : Blo 1207921 4589405 := bstep (se 3 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 4589405 = 1721027) B1721027
theorem B1812377 : Blo 1207921 1812377 := bstep (se 2 (by rfl) ⟨679641, by rfl⟩ : syracuseStep 1812377 = 1359283) B1359283
theorem B11773873 : Blo 1207921 11773873 := bstep (se 2 (by rfl) ⟨4415202, by rfl⟩ : syracuseStep 11773873 = 8830405) B8830405
theorem B1812491 : Blo 1207921 1812491 := bstep (se 1 (by rfl) ⟨1359368, by rfl⟩ : syracuseStep 1812491 = 2718737) B2718737
theorem B1812503 : Blo 1207921 1812503 := bstep (se 1 (by rfl) ⟨1359377, by rfl⟩ : syracuseStep 1812503 = 2718755) B2718755
theorem B2484275 : Blo 1207921 2484275 := bstep (se 1 (by rfl) ⟨1863206, by rfl⟩ : syracuseStep 2484275 = 3726413) B3726413
theorem B1812569 : Blo 1207921 1812569 := bstep (se 2 (by rfl) ⟨679713, by rfl⟩ : syracuseStep 1812569 = 1359427) B1359427
theorem B5163097 : Blo 1207921 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B9799811 : Blo 1207921 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B2296001 : Blo 1207921 2296001 := bstep (se 2 (by rfl) ⟨861000, by rfl⟩ : syracuseStep 2296001 = 1722001) B1722001
theorem B1812683 : Blo 1207921 1812683 := bstep (se 1 (by rfl) ⟨1359512, by rfl⟩ : syracuseStep 1812683 = 2719025) B2719025
theorem B1812695 : Blo 1207921 1812695 := bstep (se 1 (by rfl) ⟨1359521, by rfl⟩ : syracuseStep 1812695 = 2719043) B2719043
theorem B1812761 : Blo 1207921 1812761 := bstep (se 2 (by rfl) ⟨679785, by rfl⟩ : syracuseStep 1812761 = 1359571) B1359571
theorem B5810525 : Blo 1207921 5810525 := bstep (se 3 (by rfl) ⟨1089473, by rfl⟩ : syracuseStep 5810525 = 2178947) B2178947
theorem B1812875 : Blo 1207921 1812875 := bstep (se 1 (by rfl) ⟨1359656, by rfl⟩ : syracuseStep 1812875 = 2719313) B2719313
theorem B1812887 : Blo 1207921 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B1452439 : Blo 1207921 1452439 := bstep (se 1 (by rfl) ⟨1089329, by rfl⟩ : syracuseStep 1452439 = 2178659) B2178659
theorem B1812953 : Blo 1207921 1812953 := bstep (se 2 (by rfl) ⟨679857, by rfl⟩ : syracuseStep 1812953 = 1359715) B1359715
theorem B1813067 : Blo 1207921 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B3312203 : Blo 1207921 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B1813079 : Blo 1207921 1813079 := bstep (se 1 (by rfl) ⟨1359809, by rfl⟩ : syracuseStep 1813079 = 2719619) B2719619
theorem B1813145 : Blo 1207921 1813145 := bstep (se 2 (by rfl) ⟨679929, by rfl⟩ : syracuseStep 1813145 = 1359859) B1359859
theorem B5163713 : Blo 1207921 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B1813259 : Blo 1207921 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B1813271 : Blo 1207921 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1813337 : Blo 1207921 1813337 := bstep (se 2 (by rfl) ⟨680001, by rfl⟩ : syracuseStep 1813337 = 1360003) B1360003
theorem B1837963 : Blo 1207921 1837963 := bstep (se 1 (by rfl) ⟨1378472, by rfl⟩ : syracuseStep 1837963 = 2756945) B2756945
theorem B1813451 : Blo 1207921 1813451 := bstep (se 1 (by rfl) ⟨1360088, by rfl⟩ : syracuseStep 1813451 = 2720177) B2720177
theorem B1813463 : Blo 1207921 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B2755595 : Blo 1207921 2755595 := bstep (se 1 (by rfl) ⟨2066696, by rfl⟩ : syracuseStep 2755595 = 4133393) B4133393
theorem B1813529 : Blo 1207921 1813529 := bstep (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) B1360147
theorem B4901933 : Blo 1207921 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B4713547 : Blo 1207921 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B6122627 : Blo 1207921 6122627 := bstep (se 1 (by rfl) ⟨4591970, by rfl⟩ : syracuseStep 6122627 = 9183941) B9183941
theorem B1813643 : Blo 1207921 1813643 := bstep (se 1 (by rfl) ⟨1360232, by rfl⟩ : syracuseStep 1813643 = 2720465) B2720465
theorem B1838231 : Blo 1207921 1838231 := bstep (se 1 (by rfl) ⟨1378673, by rfl⟩ : syracuseStep 1838231 = 2757347) B2757347
theorem B1813655 : Blo 1207921 1813655 := bstep (se 1 (by rfl) ⟨1360241, by rfl⟩ : syracuseStep 1813655 = 2720483) B2720483
theorem B3402931 : Blo 1207921 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B1813721 : Blo 1207921 1813721 := bstep (se 2 (by rfl) ⟨680145, by rfl⟩ : syracuseStep 1813721 = 1360291) B1360291
theorem B3443933 : Blo 1207921 3443933 := bstep (se 3 (by rfl) ⟨645737, by rfl⟩ : syracuseStep 3443933 = 1291475) B1291475
theorem B2616563 : Blo 1207921 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B8711459 : Blo 1207921 8711459 := bstep (se 1 (by rfl) ⟨6533594, by rfl⟩ : syracuseStep 8711459 = 13067189) B13067189
theorem B21499181 : Blo 1207921 21499181 := bstep (se 3 (by rfl) ⟨4031096, by rfl⟩ : syracuseStep 21499181 = 8062193) B8062193
theorem B1813835 : Blo 1207921 1813835 := bstep (se 1 (by rfl) ⟨1360376, by rfl⟩ : syracuseStep 1813835 = 2720753) B2720753
theorem B1813847 : Blo 1207921 1813847 := bstep (se 1 (by rfl) ⟨1360385, by rfl⟩ : syracuseStep 1813847 = 2720771) B2720771
theorem B1813913 : Blo 1207921 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B3059147 : Blo 1207921 3059147 := bstep (se 1 (by rfl) ⟨2294360, by rfl⟩ : syracuseStep 3059147 = 4588721) B4588721
theorem B1814027 : Blo 1207921 1814027 := bstep (se 1 (by rfl) ⟨1360520, by rfl⟩ : syracuseStep 1814027 = 2721041) B2721041
theorem B1814039 : Blo 1207921 1814039 := bstep (se 1 (by rfl) ⟨1360529, by rfl⟩ : syracuseStep 1814039 = 2721059) B2721059
theorem B1814105 : Blo 1207921 1814105 := bstep (se 2 (by rfl) ⟨680289, by rfl⟩ : syracuseStep 1814105 = 1360579) B1360579
theorem B1207927 : Blo 1207921 1207927 := bstep (se 1 (by rfl) ⟨905945, by rfl⟩ : syracuseStep 1207927 = 1811891) B1811891
theorem B1207947 : Blo 1207921 1207947 := bstep (se 1 (by rfl) ⟨905960, by rfl⟩ : syracuseStep 1207947 = 1811921) B1811921
theorem B1207959 : Blo 1207921 1207959 := bstep (se 1 (by rfl) ⟨905969, by rfl⟩ : syracuseStep 1207959 = 1811939) B1811939
theorem B1207979 : Blo 1207921 1207979 := bstep (se 1 (by rfl) ⟨905984, by rfl⟩ : syracuseStep 1207979 = 1811969) B1811969
theorem B9072307 : Blo 1207921 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B1207991 : Blo 1207921 1207991 := bstep (se 1 (by rfl) ⟨905993, by rfl⟩ : syracuseStep 1207991 = 1811987) B1811987
theorem B1208011 : Blo 1207921 1208011 := bstep (se 1 (by rfl) ⟨906008, by rfl⟩ : syracuseStep 1208011 = 1812017) B1812017
theorem B1208023 : Blo 1207921 1208023 := bstep (se 1 (by rfl) ⟨906017, by rfl⟩ : syracuseStep 1208023 = 1812035) B1812035
theorem B1838809 : Blo 1207921 1838809 := bstep (se 2 (by rfl) ⟨689553, by rfl⟩ : syracuseStep 1838809 = 1379107) B1379107
theorem B1289963 : Blo 1207921 1289963 := bstep (se 1 (by rfl) ⟨967472, by rfl⟩ : syracuseStep 1289963 = 1934945) B1934945
theorem B1208043 : Blo 1207921 1208043 := bstep (se 1 (by rfl) ⟨906032, by rfl⟩ : syracuseStep 1208043 = 1812065) B1812065
theorem B1208055 : Blo 1207921 1208055 := bstep (se 1 (by rfl) ⟨906041, by rfl⟩ : syracuseStep 1208055 = 1812083) B1812083
theorem B4591363 : Blo 1207921 4591363 := bstep (se 1 (by rfl) ⟨3443522, by rfl⟩ : syracuseStep 4591363 = 6887045) B6887045
theorem B1208075 : Blo 1207921 1208075 := bstep (se 1 (by rfl) ⟨906056, by rfl⟩ : syracuseStep 1208075 = 1812113) B1812113
theorem B282693397 : Blo 1207921 282693397 := bstep (se 6 (by rfl) ⟨6625626, by rfl⟩ : syracuseStep 282693397 = 13251253) B13251253
theorem B1208087 : Blo 1207921 1208087 := bstep (se 1 (by rfl) ⟨906065, by rfl⟩ : syracuseStep 1208087 = 1812131) B1812131
theorem B1208107 : Blo 1207921 1208107 := bstep (se 1 (by rfl) ⟨906080, by rfl⟩ : syracuseStep 1208107 = 1812161) B1812161
theorem B1208119 : Blo 1207921 1208119 := bstep (se 1 (by rfl) ⟨906089, by rfl⟩ : syracuseStep 1208119 = 1812179) B1812179
theorem B4353857 : Blo 1207921 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B1208139 : Blo 1207921 1208139 := bstep (se 1 (by rfl) ⟨906104, by rfl⟩ : syracuseStep 1208139 = 1812209) B1812209
theorem B1208151 : Blo 1207921 1208151 := bstep (se 1 (by rfl) ⟨906113, by rfl⟩ : syracuseStep 1208151 = 1812227) B1812227
theorem B1290091 : Blo 1207921 1290091 := bstep (se 1 (by rfl) ⟨967568, by rfl⟩ : syracuseStep 1290091 = 1935137) B1935137
theorem B1208171 : Blo 1207921 1208171 := bstep (se 1 (by rfl) ⟨906128, by rfl⟩ : syracuseStep 1208171 = 1812257) B1812257
theorem B1208183 : Blo 1207921 1208183 := bstep (se 1 (by rfl) ⟨906137, by rfl⟩ : syracuseStep 1208183 = 1812275) B1812275
theorem B1208203 : Blo 1207921 1208203 := bstep (se 1 (by rfl) ⟨906152, by rfl⟩ : syracuseStep 1208203 = 1812305) B1812305
theorem B1208215 : Blo 1207921 1208215 := bstep (se 1 (by rfl) ⟨906161, by rfl⟩ : syracuseStep 1208215 = 1812323) B1812323
theorem B1208235 : Blo 1207921 1208235 := bstep (se 1 (by rfl) ⟨906176, by rfl⟩ : syracuseStep 1208235 = 1812353) B1812353
theorem B1208247 : Blo 1207921 1208247 := bstep (se 1 (by rfl) ⟨906185, by rfl⟩ : syracuseStep 1208247 = 1812371) B1812371
theorem B1208267 : Blo 1207921 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B1208279 : Blo 1207921 1208279 := bstep (se 1 (by rfl) ⟨906209, by rfl⟩ : syracuseStep 1208279 = 1812419) B1812419
theorem B1208299 : Blo 1207921 1208299 := bstep (se 1 (by rfl) ⟨906224, by rfl⟩ : syracuseStep 1208299 = 1812449) B1812449
theorem B1208311 : Blo 1207921 1208311 := bstep (se 1 (by rfl) ⟨906233, by rfl⟩ : syracuseStep 1208311 = 1812467) B1812467
theorem B1208331 : Blo 1207921 1208331 := bstep (se 1 (by rfl) ⟨906248, by rfl⟩ : syracuseStep 1208331 = 1812497) B1812497
theorem B1208343 : Blo 1207921 1208343 := bstep (se 1 (by rfl) ⟨906257, by rfl⟩ : syracuseStep 1208343 = 1812515) B1812515
theorem B1208363 : Blo 1207921 1208363 := bstep (se 1 (by rfl) ⟨906272, by rfl⟩ : syracuseStep 1208363 = 1812545) B1812545
theorem B4591667 : Blo 1207921 4591667 := bstep (se 1 (by rfl) ⟨3443750, by rfl⟩ : syracuseStep 4591667 = 6887501) B6887501
theorem B1208375 : Blo 1207921 1208375 := bstep (se 1 (by rfl) ⟨906281, by rfl⟩ : syracuseStep 1208375 = 1812563) B1812563
theorem B3870785 : Blo 1207921 3870785 := bstep (se 2 (by rfl) ⟨1451544, by rfl⟩ : syracuseStep 3870785 = 2903089) B2903089
theorem B1208395 : Blo 1207921 1208395 := bstep (se 1 (by rfl) ⟨906296, by rfl⟩ : syracuseStep 1208395 = 1812593) B1812593
theorem B1208407 : Blo 1207921 1208407 := bstep (se 1 (by rfl) ⟨906305, by rfl⟩ : syracuseStep 1208407 = 1812611) B1812611
theorem B1208427 : Blo 1207921 1208427 := bstep (se 1 (by rfl) ⟨906320, by rfl⟩ : syracuseStep 1208427 = 1812641) B1812641
theorem B1208439 : Blo 1207921 1208439 := bstep (se 1 (by rfl) ⟨906329, by rfl⟩ : syracuseStep 1208439 = 1812659) B1812659
theorem B1208459 : Blo 1207921 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B1208471 : Blo 1207921 1208471 := bstep (se 1 (by rfl) ⟨906353, by rfl⟩ : syracuseStep 1208471 = 1812707) B1812707
theorem B1208491 : Blo 1207921 1208491 := bstep (se 1 (by rfl) ⟨906368, by rfl⟩ : syracuseStep 1208491 = 1812737) B1812737
theorem B1208503 : Blo 1207921 1208503 := bstep (se 1 (by rfl) ⟨906377, by rfl⟩ : syracuseStep 1208503 = 1812755) B1812755
theorem B1208523 : Blo 1207921 1208523 := bstep (se 1 (by rfl) ⟨906392, by rfl⟩ : syracuseStep 1208523 = 1812785) B1812785
theorem B1208535 : Blo 1207921 1208535 := bstep (se 1 (by rfl) ⟨906401, by rfl⟩ : syracuseStep 1208535 = 1812803) B1812803
theorem B1208555 : Blo 1207921 1208555 := bstep (se 1 (by rfl) ⟨906416, by rfl⟩ : syracuseStep 1208555 = 1812833) B1812833
theorem B1208567 : Blo 1207921 1208567 := bstep (se 1 (by rfl) ⟨906425, by rfl⟩ : syracuseStep 1208567 = 1812851) B1812851
theorem B1208587 : Blo 1207921 1208587 := bstep (se 1 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 1208587 = 1812881) B1812881
theorem B1208599 : Blo 1207921 1208599 := bstep (se 1 (by rfl) ⟨906449, by rfl⟩ : syracuseStep 1208599 = 1812899) B1812899
theorem B1208619 : Blo 1207921 1208619 := bstep (se 1 (by rfl) ⟨906464, by rfl⟩ : syracuseStep 1208619 = 1812929) B1812929
theorem B1208631 : Blo 1207921 1208631 := bstep (se 1 (by rfl) ⟨906473, by rfl⟩ : syracuseStep 1208631 = 1812947) B1812947
theorem B1208651 : Blo 1207921 1208651 := bstep (se 1 (by rfl) ⟨906488, by rfl⟩ : syracuseStep 1208651 = 1812977) B1812977
theorem B1208663 : Blo 1207921 1208663 := bstep (se 1 (by rfl) ⟨906497, by rfl⟩ : syracuseStep 1208663 = 1812995) B1812995
theorem B1208683 : Blo 1207921 1208683 := bstep (se 1 (by rfl) ⟨906512, by rfl⟩ : syracuseStep 1208683 = 1813025) B1813025
theorem B1208695 : Blo 1207921 1208695 := bstep (se 1 (by rfl) ⟨906521, by rfl⟩ : syracuseStep 1208695 = 1813043) B1813043
theorem B1208715 : Blo 1207921 1208715 := bstep (se 1 (by rfl) ⟨906536, by rfl⟩ : syracuseStep 1208715 = 1813073) B1813073
theorem B1208727 : Blo 1207921 1208727 := bstep (se 1 (by rfl) ⟨906545, by rfl⟩ : syracuseStep 1208727 = 1813091) B1813091
theorem B3060119 : Blo 1207921 3060119 := bstep (se 1 (by rfl) ⟨2295089, by rfl⟩ : syracuseStep 3060119 = 4590179) B4590179
theorem B1208747 : Blo 1207921 1208747 := bstep (se 1 (by rfl) ⟨906560, by rfl⟩ : syracuseStep 1208747 = 1813121) B1813121
theorem B1208759 : Blo 1207921 1208759 := bstep (se 1 (by rfl) ⟨906569, by rfl⟩ : syracuseStep 1208759 = 1813139) B1813139
theorem B1208779 : Blo 1207921 1208779 := bstep (se 1 (by rfl) ⟨906584, by rfl⟩ : syracuseStep 1208779 = 1813169) B1813169
theorem B1208791 : Blo 1207921 1208791 := bstep (se 1 (by rfl) ⟨906593, by rfl⟩ : syracuseStep 1208791 = 1813187) B1813187
theorem B1208811 : Blo 1207921 1208811 := bstep (se 1 (by rfl) ⟨906608, by rfl⟩ : syracuseStep 1208811 = 1813217) B1813217
theorem B1208823 : Blo 1207921 1208823 := bstep (se 1 (by rfl) ⟨906617, by rfl⟩ : syracuseStep 1208823 = 1813235) B1813235
theorem B1208843 : Blo 1207921 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B1208855 : Blo 1207921 1208855 := bstep (se 1 (by rfl) ⟨906641, by rfl⟩ : syracuseStep 1208855 = 1813283) B1813283
theorem B1208875 : Blo 1207921 1208875 := bstep (se 1 (by rfl) ⟨906656, by rfl⟩ : syracuseStep 1208875 = 1813313) B1813313
theorem B1208887 : Blo 1207921 1208887 := bstep (se 1 (by rfl) ⟨906665, by rfl⟩ : syracuseStep 1208887 = 1813331) B1813331
theorem B1208907 : Blo 1207921 1208907 := bstep (se 1 (by rfl) ⟨906680, by rfl⟩ : syracuseStep 1208907 = 1813361) B1813361
theorem B1208919 : Blo 1207921 1208919 := bstep (se 1 (by rfl) ⟨906689, by rfl⟩ : syracuseStep 1208919 = 1813379) B1813379
theorem B1208939 : Blo 1207921 1208939 := bstep (se 1 (by rfl) ⟨906704, by rfl⟩ : syracuseStep 1208939 = 1813409) B1813409
theorem B1208951 : Blo 1207921 1208951 := bstep (se 1 (by rfl) ⟨906713, by rfl⟩ : syracuseStep 1208951 = 1813427) B1813427
theorem B1208971 : Blo 1207921 1208971 := bstep (se 1 (by rfl) ⟨906728, by rfl⟩ : syracuseStep 1208971 = 1813457) B1813457
theorem B1208983 : Blo 1207921 1208983 := bstep (se 1 (by rfl) ⟨906737, by rfl⟩ : syracuseStep 1208983 = 1813475) B1813475
theorem B1209003 : Blo 1207921 1209003 := bstep (se 1 (by rfl) ⟨906752, by rfl⟩ : syracuseStep 1209003 = 1813505) B1813505
theorem B1209015 : Blo 1207921 1209015 := bstep (se 1 (by rfl) ⟨906761, by rfl⟩ : syracuseStep 1209015 = 1813523) B1813523
theorem B1209035 : Blo 1207921 1209035 := bstep (se 1 (by rfl) ⟨906776, by rfl⟩ : syracuseStep 1209035 = 1813553) B1813553
theorem B1209047 : Blo 1207921 1209047 := bstep (se 1 (by rfl) ⟨906785, by rfl⟩ : syracuseStep 1209047 = 1813571) B1813571
theorem B1209067 : Blo 1207921 1209067 := bstep (se 1 (by rfl) ⟨906800, by rfl⟩ : syracuseStep 1209067 = 1813601) B1813601
theorem B1209079 : Blo 1207921 1209079 := bstep (se 1 (by rfl) ⟨906809, by rfl⟩ : syracuseStep 1209079 = 1813619) B1813619
theorem B1209099 : Blo 1207921 1209099 := bstep (se 1 (by rfl) ⟨906824, by rfl⟩ : syracuseStep 1209099 = 1813649) B1813649
theorem B1209111 : Blo 1207921 1209111 := bstep (se 1 (by rfl) ⟨906833, by rfl⟩ : syracuseStep 1209111 = 1813667) B1813667
theorem B1209131 : Blo 1207921 1209131 := bstep (se 1 (by rfl) ⟨906848, by rfl⟩ : syracuseStep 1209131 = 1813697) B1813697
theorem B1209143 : Blo 1207921 1209143 := bstep (se 1 (by rfl) ⟨906857, by rfl⟩ : syracuseStep 1209143 = 1813715) B1813715
theorem B1209163 : Blo 1207921 1209163 := bstep (se 1 (by rfl) ⟨906872, by rfl⟩ : syracuseStep 1209163 = 1813745) B1813745
theorem B1209175 : Blo 1207921 1209175 := bstep (se 1 (by rfl) ⟨906881, by rfl⟩ : syracuseStep 1209175 = 1813763) B1813763
theorem B1209195 : Blo 1207921 1209195 := bstep (se 1 (by rfl) ⟨906896, by rfl⟩ : syracuseStep 1209195 = 1813793) B1813793
theorem B1209207 : Blo 1207921 1209207 := bstep (se 1 (by rfl) ⟨906905, by rfl⟩ : syracuseStep 1209207 = 1813811) B1813811
theorem B1209227 : Blo 1207921 1209227 := bstep (se 1 (by rfl) ⟨906920, by rfl⟩ : syracuseStep 1209227 = 1813841) B1813841
theorem B4354967 : Blo 1207921 4354967 := bstep (se 1 (by rfl) ⟨3266225, by rfl⟩ : syracuseStep 4354967 = 6532451) B6532451
theorem B6886295 : Blo 1207921 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B1209239 : Blo 1207921 1209239 := bstep (se 1 (by rfl) ⟨906929, by rfl⟩ : syracuseStep 1209239 = 1813859) B1813859
theorem B1209259 : Blo 1207921 1209259 := bstep (se 1 (by rfl) ⟨906944, by rfl⟩ : syracuseStep 1209259 = 1813889) B1813889
theorem B1209271 : Blo 1207921 1209271 := bstep (se 1 (by rfl) ⟨906953, by rfl⟩ : syracuseStep 1209271 = 1813907) B1813907
theorem B1209291 : Blo 1207921 1209291 := bstep (se 1 (by rfl) ⟨906968, by rfl⟩ : syracuseStep 1209291 = 1813937) B1813937
theorem B1209303 : Blo 1207921 1209303 := bstep (se 1 (by rfl) ⟨906977, by rfl⟩ : syracuseStep 1209303 = 1813955) B1813955
theorem B3871709 : Blo 1207921 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B1209323 : Blo 1207921 1209323 := bstep (se 1 (by rfl) ⟨906992, by rfl⟩ : syracuseStep 1209323 = 1813985) B1813985
theorem B1209335 : Blo 1207921 1209335 := bstep (se 1 (by rfl) ⟨907001, by rfl⟩ : syracuseStep 1209335 = 1814003) B1814003
theorem B1209355 : Blo 1207921 1209355 := bstep (se 1 (by rfl) ⟨907016, by rfl⟩ : syracuseStep 1209355 = 1814033) B1814033
theorem B1209367 : Blo 1207921 1209367 := bstep (se 1 (by rfl) ⟨907025, by rfl⟩ : syracuseStep 1209367 = 1814051) B1814051
theorem B1209387 : Blo 1207921 1209387 := bstep (se 1 (by rfl) ⟨907040, by rfl⟩ : syracuseStep 1209387 = 1814081) B1814081
theorem B3060787 : Blo 1207921 3060787 := bstep (se 1 (by rfl) ⟨2295590, by rfl⟩ : syracuseStep 3060787 = 4591181) B4591181
theorem B1209399 : Blo 1207921 1209399 := bstep (se 1 (by rfl) ⟨907049, by rfl⟩ : syracuseStep 1209399 = 1814099) B1814099
theorem B1209419 : Blo 1207921 1209419 := bstep (se 1 (by rfl) ⟨907064, by rfl⟩ : syracuseStep 1209419 = 1814129) B1814129
theorem B3060929 : Blo 1207921 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B1529047 : Blo 1207921 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B3487169 : Blo 1207921 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B4077107 : Blo 1207921 4077107 := bstep (se 1 (by rfl) ⟨3057830, by rfl⟩ : syracuseStep 4077107 = 6115661) B6115661
theorem B6116957 : Blo 1207921 6116957 := bstep (se 3 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 6116957 = 2293859) B2293859
theorem B20649653 : Blo 1207921 20649653 := bstep (se 5 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 20649653 = 1935905) B1935905
theorem B10319633 : Blo 1207921 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B4077377 : Blo 1207921 4077377 := bstep (se 2 (by rfl) ⟨1529016, by rfl⟩ : syracuseStep 4077377 = 3058033) B3058033
theorem B25499569 : Blo 1207921 25499569 := bstep (se 2 (by rfl) ⟨9562338, by rfl⟩ : syracuseStep 25499569 = 19124677) B19124677
theorem B1529867 : Blo 1207921 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B47085637 : Blo 1207921 47085637 := bstep (se 4 (by rfl) ⟨4414278, by rfl⟩ : syracuseStep 47085637 = 8828557) B8828557
theorem B8714341 : Blo 1207921 8714341 := bstep (se 4 (by rfl) ⟨816969, by rfl⟩ : syracuseStep 8714341 = 1633939) B1633939
theorem B2324695 : Blo 1207921 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B2717963 : Blo 1207921 2717963 := bstep (se 1 (by rfl) ⟨2038472, by rfl⟩ : syracuseStep 2717963 = 4076945) B4076945
theorem B2718017 : Blo 1207921 2718017 := bstep (se 2 (by rfl) ⟨1019256, by rfl⟩ : syracuseStep 2718017 = 2038513) B2038513
theorem B4077917 : Blo 1207921 4077917 := bstep (se 3 (by rfl) ⟨764609, by rfl⟩ : syracuseStep 4077917 = 1529219) B1529219
theorem B1309079 : Blo 1207921 1309079 := bstep (se 1 (by rfl) ⟨981809, by rfl⟩ : syracuseStep 1309079 = 1963619) B1963619
theorem B13957555 : Blo 1207921 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B4356625 : Blo 1207921 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B2718233 : Blo 1207921 2718233 := bstep (se 2 (by rfl) ⟨1019337, by rfl⟩ : syracuseStep 2718233 = 2038675) B2038675
theorem B5306945 : Blo 1207921 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B4651609 : Blo 1207921 4651609 := bstep (se 2 (by rfl) ⟨1744353, by rfl⟩ : syracuseStep 4651609 = 3488707) B3488707
theorem B2718323 : Blo 1207921 2718323 := bstep (se 1 (by rfl) ⟨2038742, by rfl⟩ : syracuseStep 2718323 = 4077485) B4077485
theorem B7740035 : Blo 1207921 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B2718359 : Blo 1207921 2718359 := bstep (se 1 (by rfl) ⟨2038769, by rfl⟩ : syracuseStep 2718359 = 4077539) B4077539
theorem B38214341 : Blo 1207921 38214341 := bstep (se 4 (by rfl) ⟨3582594, by rfl⟩ : syracuseStep 38214341 = 7165189) B7165189
theorem B1530571 : Blo 1207921 1530571 := bstep (se 1 (by rfl) ⟨1147928, by rfl⟩ : syracuseStep 1530571 = 2295857) B2295857
theorem B2177779 : Blo 1207921 2177779 := bstep (se 1 (by rfl) ⟨1633334, by rfl⟩ : syracuseStep 2177779 = 3266669) B3266669
theorem B5511959 : Blo 1207921 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B9181997 : Blo 1207921 9181997 := bstep (se 3 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 9181997 = 3443249) B3443249
theorem B2718539 : Blo 1207921 2718539 := bstep (se 1 (by rfl) ⟨2038904, by rfl⟩ : syracuseStep 2718539 = 4077809) B4077809
theorem B2718593 : Blo 1207921 2718593 := bstep (se 2 (by rfl) ⟨1019472, by rfl⟩ : syracuseStep 2718593 = 2038945) B2038945
theorem B8608643 : Blo 1207921 8608643 := bstep (se 1 (by rfl) ⟨6456482, by rfl⟩ : syracuseStep 8608643 = 12912965) B12912965
theorem B2177945 : Blo 1207921 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B30981041 : Blo 1207921 30981041 := bstep (se 2 (by rfl) ⟨11617890, by rfl⟩ : syracuseStep 30981041 = 23235781) B23235781
theorem B5159953 : Blo 1207921 5159953 := bstep (se 2 (by rfl) ⟨1934982, by rfl⟩ : syracuseStep 5159953 = 3869965) B3869965
theorem B1358923 : Blo 1207921 1358923 := bstep (se 1 (by rfl) ⟨1019192, by rfl⟩ : syracuseStep 1358923 = 2038385) B2038385
theorem B2038871 : Blo 1207921 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B2718809 : Blo 1207921 2718809 := bstep (se 2 (by rfl) ⟨1019553, by rfl⟩ : syracuseStep 2718809 = 2039107) B2039107
theorem B2718899 : Blo 1207921 2718899 := bstep (se 1 (by rfl) ⟨2039174, by rfl⟩ : syracuseStep 2718899 = 4078349) B4078349
theorem B1359031 : Blo 1207921 1359031 := bstep (se 1 (by rfl) ⟨1019273, by rfl⟩ : syracuseStep 1359031 = 2038547) B2038547
theorem B4136129 : Blo 1207921 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B1744075 : Blo 1207921 1744075 := bstep (se 1 (by rfl) ⟨1308056, by rfl⟩ : syracuseStep 1744075 = 2616113) B2616113
theorem B9174221 : Blo 1207921 9174221 := bstep (se 3 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 9174221 = 3440333) B3440333
theorem B2038999 : Blo 1207921 2038999 := bstep (se 1 (by rfl) ⟨1529249, by rfl⟩ : syracuseStep 2038999 = 3058499) B3058499
theorem B2718935 : Blo 1207921 2718935 := bstep (se 1 (by rfl) ⟨2039201, by rfl⟩ : syracuseStep 2718935 = 4078403) B4078403
theorem B4136267 : Blo 1207921 4136267 := bstep (se 1 (by rfl) ⟨3102200, by rfl⟩ : syracuseStep 4136267 = 6204401) B6204401
theorem B1359211 : Blo 1207921 1359211 := bstep (se 1 (by rfl) ⟨1019408, by rfl⟩ : syracuseStep 1359211 = 2038817) B2038817
theorem B2719115 : Blo 1207921 2719115 := bstep (se 1 (by rfl) ⟨2039336, by rfl⟩ : syracuseStep 2719115 = 4078673) B4078673
theorem B2719169 : Blo 1207921 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B4079051 : Blo 1207921 4079051 := bstep (se 1 (by rfl) ⟨3059288, by rfl⟩ : syracuseStep 4079051 = 6118577) B6118577
theorem B1359319 : Blo 1207921 1359319 := bstep (se 1 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 1359319 = 2038979) B2038979
theorem B6626861 : Blo 1207921 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1359499 : Blo 1207921 1359499 := bstep (se 1 (by rfl) ⟨1019624, by rfl⟩ : syracuseStep 1359499 = 2039249) B2039249
theorem B6119063 : Blo 1207921 6119063 := bstep (se 1 (by rfl) ⟨4589297, by rfl⟩ : syracuseStep 6119063 = 9178595) B9178595
theorem B2719385 : Blo 1207921 2719385 := bstep (se 2 (by rfl) ⟨1019769, by rfl⟩ : syracuseStep 2719385 = 2039539) B2039539
theorem B2293427 : Blo 1207921 2293427 := bstep (se 1 (by rfl) ⟨1720070, by rfl⟩ : syracuseStep 2293427 = 3440141) B3440141
theorem B9174707 : Blo 1207921 9174707 := bstep (se 1 (by rfl) ⟨6881030, by rfl⟩ : syracuseStep 9174707 = 13762061) B13762061
theorem B4079321 : Blo 1207921 4079321 := bstep (se 2 (by rfl) ⟨1529745, by rfl⟩ : syracuseStep 4079321 = 3059491) B3059491
theorem B3268313 : Blo 1207921 3268313 := bstep (se 2 (by rfl) ⟨1225617, by rfl⟩ : syracuseStep 3268313 = 2451235) B2451235
theorem B2719475 : Blo 1207921 2719475 := bstep (se 1 (by rfl) ⟨2039606, by rfl⟩ : syracuseStep 2719475 = 4079213) B4079213
theorem B1359607 : Blo 1207921 1359607 := bstep (se 1 (by rfl) ⟨1019705, by rfl⟩ : syracuseStep 1359607 = 2039411) B2039411
theorem B2719511 : Blo 1207921 2719511 := bstep (se 1 (by rfl) ⟨2039633, by rfl⟩ : syracuseStep 2719511 = 4079267) B4079267
theorem B8494913 : Blo 1207921 8494913 := bstep (se 2 (by rfl) ⟨3185592, by rfl⟩ : syracuseStep 8494913 = 6371185) B6371185
theorem B2039627 : Blo 1207921 2039627 := bstep (se 1 (by rfl) ⟨1529720, by rfl⟩ : syracuseStep 2039627 = 3059441) B3059441
theorem B2580311 : Blo 1207921 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B2580353 : Blo 1207921 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B1359787 : Blo 1207921 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B2039755 : Blo 1207921 2039755 := bstep (se 1 (by rfl) ⟨1529816, by rfl⟩ : syracuseStep 2039755 = 3059633) B3059633
theorem B2719691 : Blo 1207921 2719691 := bstep (se 1 (by rfl) ⟨2039768, by rfl⟩ : syracuseStep 2719691 = 4079537) B4079537
theorem B4079645 : Blo 1207921 4079645 := bstep (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) B1529867
theorem B1359931 : Blo 1207921 1359931 := bstep (se 1 (by rfl) ⟨1019948, by rfl⟩ : syracuseStep 1359931 = 2039897) B2039897
theorem B10322093 : Blo 1207921 10322093 := bstep (se 3 (by rfl) ⟨1935392, by rfl⟩ : syracuseStep 10322093 = 3870785) B3870785
theorem B2720015 : Blo 1207921 2720015 := bstep (se 1 (by rfl) ⟨2040011, by rfl⟩ : syracuseStep 2720015 = 4080023) B4080023
theorem B2040079 : Blo 1207921 2040079 := bstep (se 1 (by rfl) ⟨1530059, by rfl⟩ : syracuseStep 2040079 = 3060119) B3060119
theorem B2720033 : Blo 1207921 2720033 := bstep (se 2 (by rfl) ⟨1020012, by rfl⟩ : syracuseStep 2720033 = 2040025) B2040025
theorem B4587961 : Blo 1207921 4587961 := bstep (se 2 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 4587961 = 3440971) B3440971
theorem B1360399 : Blo 1207921 1360399 := bstep (se 1 (by rfl) ⟨1020299, by rfl⟩ : syracuseStep 1360399 = 2040599) B2040599
theorem B2294315 : Blo 1207921 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B2720375 : Blo 1207921 2720375 := bstep (se 1 (by rfl) ⟨2040281, by rfl⟩ : syracuseStep 2720375 = 4080563) B4080563
theorem B2581139 : Blo 1207921 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B5808833 : Blo 1207921 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B4899599 : Blo 1207921 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B2294543 : Blo 1207921 2294543 := bstep (se 1 (by rfl) ⟨1720907, by rfl⟩ : syracuseStep 2294543 = 3441815) B3441815
theorem B6202145 : Blo 1207921 6202145 := bstep (se 2 (by rfl) ⟨2325804, by rfl⟩ : syracuseStep 6202145 = 4651609) B4651609
theorem B2720555 : Blo 1207921 2720555 := bstep (se 1 (by rfl) ⟨2040416, by rfl⟩ : syracuseStep 2720555 = 4080833) B4080833
theorem B2040619 : Blo 1207921 2040619 := bstep (se 1 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 2040619 = 3060929) B3060929
theorem B4653883 : Blo 1207921 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2040761 : Blo 1207921 2040761 := bstep (se 2 (by rfl) ⟨765285, by rfl⟩ : syracuseStep 2040761 = 1530571) B1530571
theorem B3490877 : Blo 1207921 3490877 := bstep (se 3 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 3490877 = 1309079) B1309079
theorem B2720915 : Blo 1207921 2720915 := bstep (se 1 (by rfl) ⟨2040686, by rfl⟩ : syracuseStep 2720915 = 4081373) B4081373
theorem B9299117 : Blo 1207921 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B2450617 : Blo 1207921 2450617 := bstep (se 2 (by rfl) ⟨918981, by rfl⟩ : syracuseStep 2450617 = 1837963) B1837963
theorem B2720969 : Blo 1207921 2720969 := bstep (se 2 (by rfl) ⟨1020363, by rfl⟩ : syracuseStep 2720969 = 2040727) B2040727
theorem B4081049 : Blo 1207921 4081049 := bstep (se 2 (by rfl) ⟨1530393, by rfl⟩ : syracuseStep 4081049 = 3060787) B3060787
theorem B1811897 : Blo 1207921 1811897 := bstep (se 2 (by rfl) ⟨679461, by rfl⟩ : syracuseStep 1811897 = 1358923) B1358923
theorem B6284729 : Blo 1207921 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B1811975 : Blo 1207921 1811975 := bstep (se 1 (by rfl) ⟨1358981, by rfl⟩ : syracuseStep 1811975 = 2717963) B2717963
theorem B1812011 : Blo 1207921 1812011 := bstep (se 1 (by rfl) ⟨1359008, by rfl⟩ : syracuseStep 1812011 = 2718017) B2718017
theorem B1812041 : Blo 1207921 1812041 := bstep (se 2 (by rfl) ⟨679515, by rfl⟩ : syracuseStep 1812041 = 1359031) B1359031
theorem B1812155 : Blo 1207921 1812155 := bstep (se 1 (by rfl) ⟨1359116, by rfl⟩ : syracuseStep 1812155 = 2718233) B2718233
theorem B1812215 : Blo 1207921 1812215 := bstep (se 1 (by rfl) ⟨1359161, by rfl⟩ : syracuseStep 1812215 = 2718323) B2718323
theorem B1812239 : Blo 1207921 1812239 := bstep (se 1 (by rfl) ⟨1359179, by rfl⟩ : syracuseStep 1812239 = 2718359) B2718359
theorem B3442475 : Blo 1207921 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B1812281 : Blo 1207921 1812281 := bstep (se 2 (by rfl) ⟨679605, by rfl⟩ : syracuseStep 1812281 = 1359211) B1359211
theorem B6121331 : Blo 1207921 6121331 := bstep (se 1 (by rfl) ⟨4590998, by rfl⟩ : syracuseStep 6121331 = 9181997) B9181997
theorem B1812359 : Blo 1207921 1812359 := bstep (se 1 (by rfl) ⟨1359269, by rfl⟩ : syracuseStep 1812359 = 2718539) B2718539
theorem B1812395 : Blo 1207921 1812395 := bstep (se 1 (by rfl) ⟨1359296, by rfl⟩ : syracuseStep 1812395 = 2718593) B2718593
theorem B1451963 : Blo 1207921 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B1812425 : Blo 1207921 1812425 := bstep (se 2 (by rfl) ⟨679659, by rfl⟩ : syracuseStep 1812425 = 1359319) B1359319
theorem B20654027 : Blo 1207921 20654027 := bstep (se 1 (by rfl) ⟨15490520, by rfl⟩ : syracuseStep 20654027 = 30981041) B30981041
theorem B1837063 : Blo 1207921 1837063 := bstep (se 1 (by rfl) ⟨1377797, by rfl⟩ : syracuseStep 1837063 = 2755595) B2755595
theorem B1812539 : Blo 1207921 1812539 := bstep (se 1 (by rfl) ⟨1359404, by rfl⟩ : syracuseStep 1812539 = 2718809) B2718809
theorem B4081751 : Blo 1207921 4081751 := bstep (se 1 (by rfl) ⟨3061313, by rfl⟩ : syracuseStep 4081751 = 6122627) B6122627
theorem B1812599 : Blo 1207921 1812599 := bstep (se 1 (by rfl) ⟨1359449, by rfl⟩ : syracuseStep 1812599 = 2718899) B2718899
theorem B1812623 : Blo 1207921 1812623 := bstep (se 1 (by rfl) ⟨1359467, by rfl⟩ : syracuseStep 1812623 = 2718935) B2718935
theorem B2295955 : Blo 1207921 2295955 := bstep (se 1 (by rfl) ⟨1721966, by rfl⟩ : syracuseStep 2295955 = 3443933) B3443933
theorem B22653101 : Blo 1207921 22653101 := bstep (se 3 (by rfl) ⟨4247456, by rfl⟩ : syracuseStep 22653101 = 8494913) B8494913
theorem B1812665 : Blo 1207921 1812665 := bstep (se 2 (by rfl) ⟨679749, by rfl⟩ : syracuseStep 1812665 = 1359499) B1359499
theorem B1812743 : Blo 1207921 1812743 := bstep (se 1 (by rfl) ⟨1359557, by rfl⟩ : syracuseStep 1812743 = 2719115) B2719115
theorem B2451745 : Blo 1207921 2451745 := bstep (se 2 (by rfl) ⟨919404, by rfl⟩ : syracuseStep 2451745 = 1838809) B1838809
theorem B1812779 : Blo 1207921 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B37234997 : Blo 1207921 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B1812809 : Blo 1207921 1812809 := bstep (se 2 (by rfl) ⟨679803, by rfl⟩ : syracuseStep 1812809 = 1359607) B1359607
theorem B6121817 : Blo 1207921 6121817 := bstep (se 2 (by rfl) ⟨2295681, by rfl⟩ : syracuseStep 6121817 = 4591363) B4591363
theorem B376924529 : Blo 1207921 376924529 := bstep (se 2 (by rfl) ⟨141346698, by rfl⟩ : syracuseStep 376924529 = 282693397) B282693397
theorem B4417907 : Blo 1207921 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B1812923 : Blo 1207921 1812923 := bstep (se 1 (by rfl) ⟨1359692, by rfl⟩ : syracuseStep 1812923 = 2719385) B2719385
theorem B1812983 : Blo 1207921 1812983 := bstep (se 1 (by rfl) ⟨1359737, by rfl⟩ : syracuseStep 1812983 = 2719475) B2719475
theorem B1813007 : Blo 1207921 1813007 := bstep (se 1 (by rfl) ⟨1359755, by rfl⟩ : syracuseStep 1813007 = 2719511) B2719511
theorem B2902571 : Blo 1207921 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B1813049 : Blo 1207921 1813049 := bstep (se 2 (by rfl) ⟨679893, by rfl⟩ : syracuseStep 1813049 = 1359787) B1359787
theorem B15698497 : Blo 1207921 15698497 := bstep (se 2 (by rfl) ⟨5886936, by rfl⟩ : syracuseStep 15698497 = 11773873) B11773873
theorem B33999425 : Blo 1207921 33999425 := bstep (se 2 (by rfl) ⟨12749784, by rfl⟩ : syracuseStep 33999425 = 25499569) B25499569
theorem B1813127 : Blo 1207921 1813127 := bstep (se 1 (by rfl) ⟨1359845, by rfl⟩ : syracuseStep 1813127 = 2719691) B2719691
theorem B1813163 : Blo 1207921 1813163 := bstep (se 1 (by rfl) ⟨1359872, by rfl⟩ : syracuseStep 1813163 = 2719745) B2719745
theorem B1813193 : Blo 1207921 1813193 := bstep (se 2 (by rfl) ⟨679947, by rfl⟩ : syracuseStep 1813193 = 1359895) B1359895
theorem B6884129 : Blo 1207921 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B11619121 : Blo 1207921 11619121 := bstep (se 2 (by rfl) ⟨4357170, by rfl⟩ : syracuseStep 11619121 = 8714341) B8714341
theorem B1813307 : Blo 1207921 1813307 := bstep (se 1 (by rfl) ⟨1359980, by rfl⟩ : syracuseStep 1813307 = 2719961) B2719961
theorem B3058519 : Blo 1207921 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B1813367 : Blo 1207921 1813367 := bstep (se 1 (by rfl) ⟨1360025, by rfl⟩ : syracuseStep 1813367 = 2720051) B2720051
theorem B1813391 : Blo 1207921 1813391 := bstep (se 1 (by rfl) ⟨1360043, by rfl⟩ : syracuseStep 1813391 = 2720087) B2720087
theorem B8825753 : Blo 1207921 8825753 := bstep (se 2 (by rfl) ⟨3309657, by rfl⟩ : syracuseStep 8825753 = 6619315) B6619315
theorem B1813433 : Blo 1207921 1813433 := bstep (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) B1360075
theorem B3099593 : Blo 1207921 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B1813511 : Blo 1207921 1813511 := bstep (se 1 (by rfl) ⟨1360133, by rfl⟩ : syracuseStep 1813511 = 2720267) B2720267
theorem B1813547 : Blo 1207921 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B1813577 : Blo 1207921 1813577 := bstep (se 2 (by rfl) ⟨680091, by rfl⟩ : syracuseStep 1813577 = 1360183) B1360183
theorem B3058823 : Blo 1207921 3058823 := bstep (se 1 (by rfl) ⟨2294117, by rfl⟩ : syracuseStep 3058823 = 4588235) B4588235
theorem B1813691 : Blo 1207921 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B1936585 : Blo 1207921 1936585 := bstep (se 2 (by rfl) ⟨726219, by rfl⟩ : syracuseStep 1936585 = 1452439) B1452439
theorem B1813751 : Blo 1207921 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B3058955 : Blo 1207921 3058955 := bstep (se 1 (by rfl) ⟨2294216, by rfl⟩ : syracuseStep 3058955 = 4588433) B4588433
theorem B2903311 : Blo 1207921 2903311 := bstep (se 1 (by rfl) ⟨2177483, by rfl⟩ : syracuseStep 2903311 = 4354967) B4354967
theorem B4590863 : Blo 1207921 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B1813775 : Blo 1207921 1813775 := bstep (se 1 (by rfl) ⟨1360331, by rfl⟩ : syracuseStep 1813775 = 2720663) B2720663
theorem B1813817 : Blo 1207921 1813817 := bstep (se 2 (by rfl) ⟨680181, by rfl⟩ : syracuseStep 1813817 = 1360363) B1360363
theorem B1813895 : Blo 1207921 1813895 := bstep (se 1 (by rfl) ⟨1360421, by rfl⟩ : syracuseStep 1813895 = 2720843) B2720843
theorem B1813931 : Blo 1207921 1813931 := bstep (se 1 (by rfl) ⟨1360448, by rfl⟩ : syracuseStep 1813931 = 2720897) B2720897
theorem B1813961 : Blo 1207921 1813961 := bstep (se 2 (by rfl) ⟨680235, by rfl⟩ : syracuseStep 1813961 = 1360471) B1360471
theorem B1814075 : Blo 1207921 1814075 := bstep (se 1 (by rfl) ⟨1360556, by rfl⟩ : syracuseStep 1814075 = 2721113) B2721113
theorem B48385637 : Blo 1207921 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B1207943 : Blo 1207921 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B1207951 : Blo 1207921 1207951 := bstep (se 1 (by rfl) ⟨905963, by rfl⟩ : syracuseStep 1207951 = 1811927) B1811927
theorem B2903705 : Blo 1207921 2903705 := bstep (se 2 (by rfl) ⟨1088889, by rfl⟩ : syracuseStep 2903705 = 2177779) B2177779
theorem B1207995 : Blo 1207921 1207995 := bstep (se 1 (by rfl) ⟨905996, by rfl⟩ : syracuseStep 1207995 = 1811993) B1811993
theorem B9301733 : Blo 1207921 9301733 := bstep (se 4 (by rfl) ⟨872037, by rfl⟩ : syracuseStep 9301733 = 1744075) B1744075
theorem B1208071 : Blo 1207921 1208071 := bstep (se 1 (by rfl) ⟨906053, by rfl⟩ : syracuseStep 1208071 = 1812107) B1812107
theorem B1208079 : Blo 1207921 1208079 := bstep (se 1 (by rfl) ⟨906059, by rfl⟩ : syracuseStep 1208079 = 1812119) B1812119
theorem B3059471 : Blo 1207921 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B13766435 : Blo 1207921 13766435 := bstep (se 1 (by rfl) ⟨10324826, by rfl⟩ : syracuseStep 13766435 = 20649653) B20649653
theorem B1208123 : Blo 1207921 1208123 := bstep (se 1 (by rfl) ⟨906092, by rfl⟩ : syracuseStep 1208123 = 1812185) B1812185
theorem B1208199 : Blo 1207921 1208199 := bstep (se 1 (by rfl) ⟨906149, by rfl⟩ : syracuseStep 1208199 = 1812299) B1812299
theorem B1208207 : Blo 1207921 1208207 := bstep (se 1 (by rfl) ⟨906155, by rfl⟩ : syracuseStep 1208207 = 1812311) B1812311
theorem B3059603 : Blo 1207921 3059603 := bstep (se 1 (by rfl) ⟨2294702, by rfl⟩ : syracuseStep 3059603 = 4589405) B4589405
theorem B1208251 : Blo 1207921 1208251 := bstep (se 1 (by rfl) ⟨906188, by rfl⟩ : syracuseStep 1208251 = 1812377) B1812377
theorem B1208327 : Blo 1207921 1208327 := bstep (se 1 (by rfl) ⟨906245, by rfl⟩ : syracuseStep 1208327 = 1812491) B1812491
theorem B1208335 : Blo 1207921 1208335 := bstep (se 1 (by rfl) ⟨906251, by rfl⟩ : syracuseStep 1208335 = 1812503) B1812503
theorem B1208379 : Blo 1207921 1208379 := bstep (se 1 (by rfl) ⟨906284, by rfl⟩ : syracuseStep 1208379 = 1812569) B1812569
theorem B6533207 : Blo 1207921 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B1208455 : Blo 1207921 1208455 := bstep (se 1 (by rfl) ⟨906341, by rfl⟩ : syracuseStep 1208455 = 1812683) B1812683
theorem B1208463 : Blo 1207921 1208463 := bstep (se 1 (by rfl) ⟨906347, by rfl⟩ : syracuseStep 1208463 = 1812695) B1812695
theorem B14151853 : Blo 1207921 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B1208507 : Blo 1207921 1208507 := bstep (se 1 (by rfl) ⟨906380, by rfl⟩ : syracuseStep 1208507 = 1812761) B1812761
theorem B1208583 : Blo 1207921 1208583 := bstep (se 1 (by rfl) ⟨906437, by rfl⟩ : syracuseStep 1208583 = 1812875) B1812875
theorem B1208591 : Blo 1207921 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1208635 : Blo 1207921 1208635 := bstep (se 1 (by rfl) ⟨906476, by rfl⟩ : syracuseStep 1208635 = 1812953) B1812953
theorem B1208711 : Blo 1207921 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B1208719 : Blo 1207921 1208719 := bstep (se 1 (by rfl) ⟨906539, by rfl⟩ : syracuseStep 1208719 = 1813079) B1813079
theorem B1208763 : Blo 1207921 1208763 := bstep (se 1 (by rfl) ⟨906572, by rfl⟩ : syracuseStep 1208763 = 1813145) B1813145
theorem B1208839 : Blo 1207921 1208839 := bstep (se 1 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 1208839 = 1813259) B1813259
theorem B3674639 : Blo 1207921 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B1208847 : Blo 1207921 1208847 := bstep (se 1 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 1208847 = 1813271) B1813271
theorem B1208891 : Blo 1207921 1208891 := bstep (se 1 (by rfl) ⟨906668, by rfl⟩ : syracuseStep 1208891 = 1813337) B1813337
theorem B5739095 : Blo 1207921 5739095 := bstep (se 1 (by rfl) ⟨4304321, by rfl⟩ : syracuseStep 5739095 = 8608643) B8608643
theorem B1208967 : Blo 1207921 1208967 := bstep (se 1 (by rfl) ⟨906725, by rfl⟩ : syracuseStep 1208967 = 1813451) B1813451
theorem B1208975 : Blo 1207921 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B1209019 : Blo 1207921 1209019 := bstep (se 1 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 1209019 = 1813529) B1813529
theorem B1209095 : Blo 1207921 1209095 := bstep (se 1 (by rfl) ⟨906821, by rfl⟩ : syracuseStep 1209095 = 1813643) B1813643
theorem B1225487 : Blo 1207921 1225487 := bstep (se 1 (by rfl) ⟨919115, by rfl⟩ : syracuseStep 1225487 = 1838231) B1838231
theorem B1209103 : Blo 1207921 1209103 := bstep (se 1 (by rfl) ⟨906827, by rfl⟩ : syracuseStep 1209103 = 1813655) B1813655
theorem B2757419 : Blo 1207921 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B6116147 : Blo 1207921 6116147 := bstep (se 1 (by rfl) ⟨4587110, by rfl⟩ : syracuseStep 6116147 = 9174221) B9174221
theorem B1209147 : Blo 1207921 1209147 := bstep (se 1 (by rfl) ⟨906860, by rfl⟩ : syracuseStep 1209147 = 1813721) B1813721
theorem B14332787 : Blo 1207921 14332787 := bstep (se 1 (by rfl) ⟨10749590, by rfl⟩ : syracuseStep 14332787 = 21499181) B21499181
theorem B2757511 : Blo 1207921 2757511 := bstep (se 1 (by rfl) ⟨2068133, by rfl⟩ : syracuseStep 2757511 = 4136267) B4136267
theorem B1209223 : Blo 1207921 1209223 := bstep (se 1 (by rfl) ⟨906917, by rfl⟩ : syracuseStep 1209223 = 1813835) B1813835
theorem B1209231 : Blo 1207921 1209231 := bstep (se 1 (by rfl) ⟨906923, by rfl⟩ : syracuseStep 1209231 = 1813847) B1813847
theorem B1209275 : Blo 1207921 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B3060737 : Blo 1207921 3060737 := bstep (se 2 (by rfl) ⟨1147776, by rfl⟩ : syracuseStep 3060737 = 2295553) B2295553
theorem B1209351 : Blo 1207921 1209351 := bstep (se 1 (by rfl) ⟨907013, by rfl⟩ : syracuseStep 1209351 = 1814027) B1814027
theorem B1209359 : Blo 1207921 1209359 := bstep (se 1 (by rfl) ⟨907019, by rfl⟩ : syracuseStep 1209359 = 1814039) B1814039
theorem B1209403 : Blo 1207921 1209403 := bstep (se 1 (by rfl) ⟨907052, by rfl⟩ : syracuseStep 1209403 = 1814105) B1814105
theorem B1528951 : Blo 1207921 1528951 := bstep (se 1 (by rfl) ⟨1146713, by rfl⟩ : syracuseStep 1528951 = 2293427) B2293427
theorem B6116471 : Blo 1207921 6116471 := bstep (se 1 (by rfl) ⟨4587353, by rfl⟩ : syracuseStep 6116471 = 9174707) B9174707
theorem B3061111 : Blo 1207921 3061111 := bstep (se 1 (by rfl) ⟨2295833, by rfl⟩ : syracuseStep 3061111 = 4591667) B4591667
theorem B62780849 : Blo 1207921 62780849 := bstep (se 2 (by rfl) ⟨23542818, by rfl⟩ : syracuseStep 62780849 = 47085637) B47085637
theorem B1529275 : Blo 1207921 1529275 := bstep (se 1 (by rfl) ⟨1146956, by rfl⟩ : syracuseStep 1529275 = 2293913) B2293913
theorem B11777501 : Blo 1207921 11777501 := bstep (se 3 (by rfl) ⟨2208281, by rfl⟩ : syracuseStep 11777501 = 4416563) B4416563
theorem B6534893 : Blo 1207921 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B6887227 : Blo 1207921 6887227 := bstep (se 1 (by rfl) ⟨5165420, by rfl⟩ : syracuseStep 6887227 = 10330841) B10330841
theorem B26498933 : Blo 1207921 26498933 := bstep (se 5 (by rfl) ⟨1242137, by rfl⟩ : syracuseStep 26498933 = 2484275) B2484275
theorem B18610073 : Blo 1207921 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B6977501 : Blo 1207921 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B6117443 : Blo 1207921 6117443 := bstep (se 1 (by rfl) ⟨4588082, by rfl⟩ : syracuseStep 6117443 = 9176165) B9176165
theorem B35330165 : Blo 1207921 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B2718071 : Blo 1207921 2718071 := bstep (se 1 (by rfl) ⟨2038553, by rfl⟩ : syracuseStep 2718071 = 4077107) B4077107
theorem B6117767 : Blo 1207921 6117767 := bstep (se 1 (by rfl) ⟨4588325, by rfl⟩ : syracuseStep 6117767 = 9176651) B9176651
theorem B1530247 : Blo 1207921 1530247 := bstep (se 1 (by rfl) ⟨1147685, by rfl⟩ : syracuseStep 1530247 = 2295371) B2295371
theorem B4077971 : Blo 1207921 4077971 := bstep (se 1 (by rfl) ⟨3058478, by rfl⟩ : syracuseStep 4077971 = 6116957) B6116957
theorem B6879755 : Blo 1207921 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B2718251 : Blo 1207921 2718251 := bstep (se 1 (by rfl) ⟨2038688, by rfl⟩ : syracuseStep 2718251 = 4077377) B4077377
theorem B6879937 : Blo 1207921 6879937 := bstep (se 2 (by rfl) ⟨2579976, by rfl⟩ : syracuseStep 6879937 = 5159953) B5159953
theorem B1530667 : Blo 1207921 1530667 := bstep (se 1 (by rfl) ⟨1148000, by rfl⟩ : syracuseStep 1530667 = 2296001) B2296001
theorem B2718611 : Blo 1207921 2718611 := bstep (se 1 (by rfl) ⟨2038958, by rfl⟩ : syracuseStep 2718611 = 4077917) B4077917
theorem B3873683 : Blo 1207921 3873683 := bstep (se 1 (by rfl) ⟨2905262, by rfl⟩ : syracuseStep 3873683 = 5810525) B5810525
theorem B4537241 : Blo 1207921 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B2038729 : Blo 1207921 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B2718665 : Blo 1207921 2718665 := bstep (se 2 (by rfl) ⟨1019499, by rfl⟩ : syracuseStep 2718665 = 2038999) B2038999
theorem B5160023 : Blo 1207921 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B25476227 : Blo 1207921 25476227 := bstep (se 1 (by rfl) ⟨19107170, by rfl⟩ : syracuseStep 25476227 = 38214341) B38214341
theorem B3439901 : Blo 1207921 3439901 := bstep (se 3 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 3439901 = 1289963) B1289963
theorem B3267955 : Blo 1207921 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B1359247 : Blo 1207921 1359247 := bstep (se 1 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 1359247 = 2038871) B2038871
theorem B3268097 : Blo 1207921 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B5807639 : Blo 1207921 5807639 := bstep (se 1 (by rfl) ⟨4355729, by rfl⟩ : syracuseStep 5807639 = 8711459) B8711459
theorem B2039431 : Blo 1207921 2039431 := bstep (se 1 (by rfl) ⟨1529573, by rfl⟩ : syracuseStep 2039431 = 3059147) B3059147
theorem B2719367 : Blo 1207921 2719367 := bstep (se 1 (by rfl) ⟨2039525, by rfl⟩ : syracuseStep 2719367 = 4079051) B4079051
theorem B4079375 : Blo 1207921 4079375 := bstep (se 1 (by rfl) ⟨3059531, by rfl⟩ : syracuseStep 4079375 = 6119063) B6119063
theorem B1720121 : Blo 1207921 1720121 := bstep (se 2 (by rfl) ⟨645045, by rfl⟩ : syracuseStep 1720121 = 1290091) B1290091
theorem B2719547 : Blo 1207921 2719547 := bstep (se 1 (by rfl) ⟨2039660, by rfl⟩ : syracuseStep 2719547 = 4079321) B4079321
theorem B2178875 : Blo 1207921 2178875 := bstep (se 1 (by rfl) ⟨1634156, by rfl⟩ : syracuseStep 2178875 = 3268313) B3268313
theorem B1359751 : Blo 1207921 1359751 := bstep (se 1 (by rfl) ⟨1019813, by rfl⟩ : syracuseStep 1359751 = 2039627) B2039627
theorem B1720207 : Blo 1207921 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B1720235 : Blo 1207921 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B2719673 : Blo 1207921 2719673 := bstep (se 2 (by rfl) ⟨1019877, by rfl⟩ : syracuseStep 2719673 = 2039755) B2039755
theorem B2719763 : Blo 1207921 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B9797669 : Blo 1207921 9797669 := bstep (se 4 (by rfl) ⟨918531, by rfl⟩ : syracuseStep 9797669 = 1837063) B1837063
theorem B6881395 : Blo 1207921 6881395 := bstep (se 1 (by rfl) ⟨5161046, by rfl⟩ : syracuseStep 6881395 = 10322093) B10322093
theorem B2449759 : Blo 1207921 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B2720105 : Blo 1207921 2720105 := bstep (se 2 (by rfl) ⟨1020039, by rfl⟩ : syracuseStep 2720105 = 2040079) B2040079
theorem B3268993 : Blo 1207921 3268993 := bstep (se 2 (by rfl) ⟨1225872, by rfl⟩ : syracuseStep 3268993 = 2451745) B2451745
theorem B3826063 : Blo 1207921 3826063 := bstep (se 1 (by rfl) ⟨2869547, by rfl⟩ : syracuseStep 3826063 = 5739095) B5739095
theorem B1720759 : Blo 1207921 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B2040329 : Blo 1207921 2040329 := bstep (se 2 (by rfl) ⟨765123, by rfl⟩ : syracuseStep 2040329 = 1530247) B1530247
theorem B1360507 : Blo 1207921 1360507 := bstep (se 1 (by rfl) ⟨1020380, by rfl⟩ : syracuseStep 1360507 = 2040761) B2040761
theorem B2040491 : Blo 1207921 2040491 := bstep (se 1 (by rfl) ⟨1530368, by rfl⟩ : syracuseStep 2040491 = 3060737) B3060737
theorem B2327251 : Blo 1207921 2327251 := bstep (se 1 (by rfl) ⟨1745438, by rfl⟩ : syracuseStep 2327251 = 3490877) B3490877
theorem B20931329 : Blo 1207921 20931329 := bstep (se 2 (by rfl) ⟨7849248, by rfl⟩ : syracuseStep 20931329 = 15698497) B15698497
theorem B2720699 : Blo 1207921 2720699 := bstep (se 1 (by rfl) ⟨2040524, by rfl⟩ : syracuseStep 2720699 = 4081049) B4081049
theorem B41853899 : Blo 1207921 41853899 := bstep (se 1 (by rfl) ⟨31390424, by rfl⟩ : syracuseStep 41853899 = 62780849) B62780849
theorem B11781085 : Blo 1207921 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B2720825 : Blo 1207921 2720825 := bstep (se 2 (by rfl) ⟨1020309, by rfl⟩ : syracuseStep 2720825 = 2040619) B2040619
theorem B2040889 : Blo 1207921 2040889 := bstep (se 2 (by rfl) ⟨765333, by rfl⟩ : syracuseStep 2040889 = 1530667) B1530667
theorem B15492161 : Blo 1207921 15492161 := bstep (se 2 (by rfl) ⟨5809560, by rfl⟩ : syracuseStep 15492161 = 11619121) B11619121
theorem B2294983 : Blo 1207921 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B4080887 : Blo 1207921 4080887 := bstep (se 1 (by rfl) ⟨3060665, by rfl⟩ : syracuseStep 4080887 = 6121331) B6121331
theorem B2721167 : Blo 1207921 2721167 := bstep (se 1 (by rfl) ⟨2040875, by rfl⟩ : syracuseStep 2721167 = 4081751) B4081751
theorem B23553443 : Blo 1207921 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B24823331 : Blo 1207921 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B4081211 : Blo 1207921 4081211 := bstep (se 1 (by rfl) ⟨3060908, by rfl⟩ : syracuseStep 4081211 = 6121817) B6121817
theorem B1812047 : Blo 1207921 1812047 := bstep (se 1 (by rfl) ⟨1359035, by rfl⟩ : syracuseStep 1812047 = 2718071) B2718071
theorem B2582113 : Blo 1207921 2582113 := bstep (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) B1936585
theorem B1935047 : Blo 1207921 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B1812167 : Blo 1207921 1812167 := bstep (se 1 (by rfl) ⟨1359125, by rfl⟩ : syracuseStep 1812167 = 2718251) B2718251
theorem B4081481 : Blo 1207921 4081481 := bstep (se 2 (by rfl) ⟨1530555, by rfl⟩ : syracuseStep 4081481 = 3061111) B3061111
theorem B1812329 : Blo 1207921 1812329 := bstep (se 2 (by rfl) ⟨679623, by rfl⟩ : syracuseStep 1812329 = 1359247) B1359247
theorem B4589419 : Blo 1207921 4589419 := bstep (se 1 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 4589419 = 6884129) B6884129
theorem B1812407 : Blo 1207921 1812407 := bstep (se 1 (by rfl) ⟨1359305, by rfl⟩ : syracuseStep 1812407 = 2718611) B2718611
theorem B2582455 : Blo 1207921 2582455 := bstep (se 1 (by rfl) ⟨1936841, by rfl⟩ : syracuseStep 2582455 = 3873683) B3873683
theorem B5883835 : Blo 1207921 5883835 := bstep (se 1 (by rfl) ⟨4412876, by rfl⟩ : syracuseStep 5883835 = 8825753) B8825753
theorem B3024827 : Blo 1207921 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B2066395 : Blo 1207921 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B1812443 : Blo 1207921 1812443 := bstep (se 1 (by rfl) ⟨1359332, by rfl⟩ : syracuseStep 1812443 = 2718665) B2718665
theorem B16984151 : Blo 1207921 16984151 := bstep (se 1 (by rfl) ⟨12738113, by rfl⟩ : syracuseStep 16984151 = 25476227) B25476227
theorem B1812911 : Blo 1207921 1812911 := bstep (se 1 (by rfl) ⟨1359683, by rfl⟩ : syracuseStep 1812911 = 2719367) B2719367
theorem B1935803 : Blo 1207921 1935803 := bstep (se 1 (by rfl) ⟨1451852, by rfl⟩ : syracuseStep 1935803 = 2903705) B2903705
theorem B1813001 : Blo 1207921 1813001 := bstep (se 2 (by rfl) ⟨679875, by rfl⟩ : syracuseStep 1813001 = 1359751) B1359751
theorem B9177623 : Blo 1207921 9177623 := bstep (se 1 (by rfl) ⟨6883217, by rfl⟩ : syracuseStep 9177623 = 13766435) B13766435
theorem B1813031 : Blo 1207921 1813031 := bstep (se 1 (by rfl) ⟨1359773, by rfl⟩ : syracuseStep 1813031 = 2719547) B2719547
theorem B1452583 : Blo 1207921 1452583 := bstep (se 1 (by rfl) ⟨1089437, by rfl⟩ : syracuseStep 1452583 = 2178875) B2178875
theorem B1813115 : Blo 1207921 1813115 := bstep (se 1 (by rfl) ⟨1359836, by rfl⟩ : syracuseStep 1813115 = 2719673) B2719673
theorem B1813241 : Blo 1207921 1813241 := bstep (se 2 (by rfl) ⟨679965, by rfl⟩ : syracuseStep 1813241 = 1359931) B1359931
theorem B1813343 : Blo 1207921 1813343 := bstep (se 1 (by rfl) ⟨1360007, by rfl⟩ : syracuseStep 1813343 = 2720015) B2720015
theorem B1813355 : Blo 1207921 1813355 := bstep (se 1 (by rfl) ⟨1360016, by rfl⟩ : syracuseStep 1813355 = 2720033) B2720033
theorem B1813583 : Blo 1207921 1813583 := bstep (se 1 (by rfl) ⟨1360187, by rfl⟩ : syracuseStep 1813583 = 2720375) B2720375
theorem B1838279 : Blo 1207921 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1813703 : Blo 1207921 1813703 := bstep (se 1 (by rfl) ⟨1360277, by rfl⟩ : syracuseStep 1813703 = 2720555) B2720555
theorem B9555191 : Blo 1207921 9555191 := bstep (se 1 (by rfl) ⟨7166393, by rfl⟩ : syracuseStep 9555191 = 14332787) B14332787
theorem B1813865 : Blo 1207921 1813865 := bstep (se 2 (by rfl) ⟨680199, by rfl⟩ : syracuseStep 1813865 = 1360399) B1360399
theorem B1813943 : Blo 1207921 1813943 := bstep (se 1 (by rfl) ⟨1360457, by rfl⟩ : syracuseStep 1813943 = 2720915) B2720915
theorem B1813979 : Blo 1207921 1813979 := bstep (se 1 (by rfl) ⟨1360484, by rfl⟩ : syracuseStep 1813979 = 2720969) B2720969
theorem B75476549 : Blo 1207921 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B1207931 : Blo 1207921 1207931 := bstep (se 1 (by rfl) ⟨905948, by rfl⟩ : syracuseStep 1207931 = 1811897) B1811897
theorem B4189819 : Blo 1207921 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B13069957 : Blo 1207921 13069957 := bstep (se 4 (by rfl) ⟨1225308, by rfl⟩ : syracuseStep 13069957 = 2450617) B2450617
theorem B7851667 : Blo 1207921 7851667 := bstep (se 1 (by rfl) ⟨5888750, by rfl⟩ : syracuseStep 7851667 = 11777501) B11777501
theorem B1207983 : Blo 1207921 1207983 := bstep (se 1 (by rfl) ⟨905987, by rfl⟩ : syracuseStep 1207983 = 1811975) B1811975
theorem B1208007 : Blo 1207921 1208007 := bstep (se 1 (by rfl) ⟨906005, by rfl⟩ : syracuseStep 1208007 = 1812011) B1812011
theorem B1208027 : Blo 1207921 1208027 := bstep (se 1 (by rfl) ⟨906020, by rfl⟩ : syracuseStep 1208027 = 1812041) B1812041
theorem B6205177 : Blo 1207921 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B1208103 : Blo 1207921 1208103 := bstep (se 1 (by rfl) ⟨906077, by rfl⟩ : syracuseStep 1208103 = 1812155) B1812155
theorem B1208143 : Blo 1207921 1208143 := bstep (se 1 (by rfl) ⟨906107, by rfl⟩ : syracuseStep 1208143 = 1812215) B1812215
theorem B1208159 : Blo 1207921 1208159 := bstep (se 1 (by rfl) ⟨906119, by rfl⟩ : syracuseStep 1208159 = 1812239) B1812239
theorem B1208187 : Blo 1207921 1208187 := bstep (se 1 (by rfl) ⟨906140, by rfl⟩ : syracuseStep 1208187 = 1812281) B1812281
theorem B17665955 : Blo 1207921 17665955 := bstep (se 1 (by rfl) ⟨13249466, by rfl⟩ : syracuseStep 17665955 = 26498933) B26498933
theorem B1208239 : Blo 1207921 1208239 := bstep (se 1 (by rfl) ⟨906179, by rfl⟩ : syracuseStep 1208239 = 1812359) B1812359
theorem B12406715 : Blo 1207921 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B1208263 : Blo 1207921 1208263 := bstep (se 1 (by rfl) ⟨906197, by rfl⟩ : syracuseStep 1208263 = 1812395) B1812395
theorem B1208283 : Blo 1207921 1208283 := bstep (se 1 (by rfl) ⟨906212, by rfl⟩ : syracuseStep 1208283 = 1812425) B1812425
theorem B1208359 : Blo 1207921 1208359 := bstep (se 1 (by rfl) ⟨906269, by rfl⟩ : syracuseStep 1208359 = 1812539) B1812539
theorem B15487037 : Blo 1207921 15487037 := bstep (se 3 (by rfl) ⟨2903819, by rfl⟩ : syracuseStep 15487037 = 5807639) B5807639
theorem B1208399 : Blo 1207921 1208399 := bstep (se 1 (by rfl) ⟨906299, by rfl⟩ : syracuseStep 1208399 = 1812599) B1812599
theorem B1208415 : Blo 1207921 1208415 := bstep (se 1 (by rfl) ⟨906311, by rfl⟩ : syracuseStep 1208415 = 1812623) B1812623
theorem B15102067 : Blo 1207921 15102067 := bstep (se 1 (by rfl) ⟨11326550, by rfl⟩ : syracuseStep 15102067 = 22653101) B22653101
theorem B1208443 : Blo 1207921 1208443 := bstep (se 1 (by rfl) ⟨906332, by rfl⟩ : syracuseStep 1208443 = 1812665) B1812665
theorem B1208495 : Blo 1207921 1208495 := bstep (se 1 (by rfl) ⟨906371, by rfl⟩ : syracuseStep 1208495 = 1812743) B1812743
theorem B1208519 : Blo 1207921 1208519 := bstep (se 1 (by rfl) ⟨906389, by rfl⟩ : syracuseStep 1208519 = 1812779) B1812779
theorem B1208539 : Blo 1207921 1208539 := bstep (se 1 (by rfl) ⟨906404, by rfl⟩ : syracuseStep 1208539 = 1812809) B1812809
theorem B1208615 : Blo 1207921 1208615 := bstep (se 1 (by rfl) ⟨906461, by rfl⟩ : syracuseStep 1208615 = 1812923) B1812923
theorem B1208655 : Blo 1207921 1208655 := bstep (se 1 (by rfl) ⟨906491, by rfl⟩ : syracuseStep 1208655 = 1812983) B1812983
theorem B1208671 : Blo 1207921 1208671 := bstep (se 1 (by rfl) ⟨906503, by rfl⟩ : syracuseStep 1208671 = 1813007) B1813007
theorem B3871081 : Blo 1207921 3871081 := bstep (se 2 (by rfl) ⟨1451655, by rfl⟩ : syracuseStep 3871081 = 2903311) B2903311
theorem B1208699 : Blo 1207921 1208699 := bstep (se 1 (by rfl) ⟨906524, by rfl⟩ : syracuseStep 1208699 = 1813049) B1813049
theorem B1208751 : Blo 1207921 1208751 := bstep (se 1 (by rfl) ⟨906563, by rfl⟩ : syracuseStep 1208751 = 1813127) B1813127
theorem B1208775 : Blo 1207921 1208775 := bstep (se 1 (by rfl) ⟨906581, by rfl⟩ : syracuseStep 1208775 = 1813163) B1813163
theorem B1208795 : Blo 1207921 1208795 := bstep (se 1 (by rfl) ⟨906596, by rfl⟩ : syracuseStep 1208795 = 1813193) B1813193
theorem B1208871 : Blo 1207921 1208871 := bstep (se 1 (by rfl) ⟨906653, by rfl⟩ : syracuseStep 1208871 = 1813307) B1813307
theorem B1208911 : Blo 1207921 1208911 := bstep (se 1 (by rfl) ⟨906683, by rfl⟩ : syracuseStep 1208911 = 1813367) B1813367
theorem B1208927 : Blo 1207921 1208927 := bstep (se 1 (by rfl) ⟨906695, by rfl⟩ : syracuseStep 1208927 = 1813391) B1813391
theorem B17429093 : Blo 1207921 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B1208955 : Blo 1207921 1208955 := bstep (se 1 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 1208955 = 1813433) B1813433
theorem B1209007 : Blo 1207921 1209007 := bstep (se 1 (by rfl) ⟨906755, by rfl⟩ : syracuseStep 1209007 = 1813511) B1813511
theorem B1209031 : Blo 1207921 1209031 := bstep (se 1 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 1209031 = 1813547) B1813547
theorem B1209051 : Blo 1207921 1209051 := bstep (se 1 (by rfl) ⟨906788, by rfl⟩ : syracuseStep 1209051 = 1813577) B1813577
theorem B1209127 : Blo 1207921 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B1209167 : Blo 1207921 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B3060575 : Blo 1207921 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B1209183 : Blo 1207921 1209183 := bstep (se 1 (by rfl) ⟨906887, by rfl⟩ : syracuseStep 1209183 = 1813775) B1813775
theorem B1209211 : Blo 1207921 1209211 := bstep (se 1 (by rfl) ⟨906908, by rfl⟩ : syracuseStep 1209211 = 1813817) B1813817
theorem B1209263 : Blo 1207921 1209263 := bstep (se 1 (by rfl) ⟨906947, by rfl⟩ : syracuseStep 1209263 = 1813895) B1813895
theorem B1209287 : Blo 1207921 1209287 := bstep (se 1 (by rfl) ⟨906965, by rfl⟩ : syracuseStep 1209287 = 1813931) B1813931
theorem B1209307 : Blo 1207921 1209307 := bstep (se 1 (by rfl) ⟨906980, by rfl⟩ : syracuseStep 1209307 = 1813961) B1813961
theorem B1209383 : Blo 1207921 1209383 := bstep (se 1 (by rfl) ⟨907037, by rfl⟩ : syracuseStep 1209383 = 1814075) B1814075
theorem B32257091 : Blo 1207921 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B3871901 : Blo 1207921 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B4355471 : Blo 1207921 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B3061273 : Blo 1207921 3061273 := bstep (se 2 (by rfl) ⟨1147977, by rfl⟩ : syracuseStep 3061273 = 2295955) B2295955
theorem B1529543 : Blo 1207921 1529543 := bstep (se 1 (by rfl) ⟨1147157, by rfl⟩ : syracuseStep 1529543 = 2294315) B2294315
theorem B3872555 : Blo 1207921 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B3266399 : Blo 1207921 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B1529695 : Blo 1207921 1529695 := bstep (se 1 (by rfl) ⟨1147271, by rfl⟩ : syracuseStep 1529695 = 2294543) B2294543
theorem B4134763 : Blo 1207921 4134763 := bstep (se 1 (by rfl) ⟨3101072, by rfl⟩ : syracuseStep 4134763 = 6202145) B6202145
theorem B4077431 : Blo 1207921 4077431 := bstep (se 1 (by rfl) ⟨3058073, by rfl⟩ : syracuseStep 4077431 = 6116147) B6116147
theorem B6117281 : Blo 1207921 6117281 := bstep (se 2 (by rfl) ⟨2293980, by rfl⟩ : syracuseStep 6117281 = 4587961) B4587961
theorem B4077647 : Blo 1207921 4077647 := bstep (se 1 (by rfl) ⟨3058235, by rfl⟩ : syracuseStep 4077647 = 6116471) B6116471
theorem B6199411 : Blo 1207921 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B9173249 : Blo 1207921 9173249 := bstep (se 2 (by rfl) ⟨3439968, by rfl⟩ : syracuseStep 9173249 = 6879937) B6879937
theorem B1005132077 : Blo 1207921 1005132077 := bstep (se 3 (by rfl) ⟨188462264, by rfl⟩ : syracuseStep 1005132077 = 376924529) B376924529
theorem B4078025 : Blo 1207921 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B4356595 : Blo 1207921 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B3676681 : Blo 1207921 3676681 := bstep (se 2 (by rfl) ⟨1378755, by rfl⟩ : syracuseStep 3676681 = 2757511) B2757511
theorem B2718305 : Blo 1207921 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B13769351 : Blo 1207921 13769351 := bstep (se 1 (by rfl) ⟨10327013, by rfl⟩ : syracuseStep 13769351 = 20654027) B20654027
theorem B4651667 : Blo 1207921 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B4078295 : Blo 1207921 4078295 := bstep (se 1 (by rfl) ⟨3058721, by rfl⟩ : syracuseStep 4078295 = 6117443) B6117443
theorem B2038601 : Blo 1207921 2038601 := bstep (se 2 (by rfl) ⟨764475, by rfl⟩ : syracuseStep 2038601 = 1528951) B1528951
theorem B4078511 : Blo 1207921 4078511 := bstep (se 1 (by rfl) ⟨3058883, by rfl⟩ : syracuseStep 4078511 = 6117767) B6117767
theorem B2718647 : Blo 1207921 2718647 := bstep (se 1 (by rfl) ⟨2038985, by rfl⟩ : syracuseStep 2718647 = 4077971) B4077971
theorem B4586503 : Blo 1207921 4586503 := bstep (se 1 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 4586503 = 6879755) B6879755
theorem B22666283 : Blo 1207921 22666283 := bstep (se 1 (by rfl) ⟨16999712, by rfl⟩ : syracuseStep 22666283 = 33999425) B33999425
theorem B2039033 : Blo 1207921 2039033 := bstep (se 2 (by rfl) ⟨764637, by rfl⟩ : syracuseStep 2039033 = 1529275) B1529275
theorem B3267965 : Blo 1207921 3267965 := bstep (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) B1225487
theorem B3440015 : Blo 1207921 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B2039215 : Blo 1207921 2039215 := bstep (se 1 (by rfl) ⟨1529411, by rfl⟩ : syracuseStep 2039215 = 3058823) B3058823
theorem B4586989 : Blo 1207921 4586989 := bstep (se 3 (by rfl) ⟨860060, by rfl⟩ : syracuseStep 4586989 = 1720121) B1720121
theorem B2039303 : Blo 1207921 2039303 := bstep (se 1 (by rfl) ⟨1529477, by rfl⟩ : syracuseStep 2039303 = 3058955) B3058955
theorem B2719241 : Blo 1207921 2719241 := bstep (se 2 (by rfl) ⟨1019715, by rfl⟩ : syracuseStep 2719241 = 2039431) B2039431
theorem B2293267 : Blo 1207921 2293267 := bstep (se 1 (by rfl) ⟨1719950, by rfl⟩ : syracuseStep 2293267 = 3439901) B3439901
theorem B2178731 : Blo 1207921 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B9182969 : Blo 1207921 9182969 := bstep (se 2 (by rfl) ⟨3443613, by rfl⟩ : syracuseStep 9182969 = 6887227) B6887227
theorem B4587293 : Blo 1207921 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B6201155 : Blo 1207921 6201155 := bstep (se 1 (by rfl) ⟨4650866, by rfl⟩ : syracuseStep 6201155 = 9301733) B9301733
theorem B2039647 : Blo 1207921 2039647 := bstep (se 1 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 2039647 = 3059471) B3059471
theorem B2719583 : Blo 1207921 2719583 := bstep (se 1 (by rfl) ⟨2039687, by rfl⟩ : syracuseStep 2719583 = 4079375) B4079375
theorem B2293609 : Blo 1207921 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B2039735 : Blo 1207921 2039735 := bstep (se 1 (by rfl) ⟨1529801, by rfl⟩ : syracuseStep 2039735 = 3059603) B3059603
theorem B8265881 : Blo 1207921 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B9175193 : Blo 1207921 9175193 := bstep (se 2 (by rfl) ⟨3440697, by rfl⟩ : syracuseStep 9175193 = 6881395) B6881395
theorem B20136089 : Blo 1207921 20136089 := bstep (se 2 (by rfl) ⟨7551033, by rfl⟩ : syracuseStep 20136089 = 15102067) B15102067
theorem B1360219 : Blo 1207921 1360219 := bstep (se 1 (by rfl) ⟨1020164, by rfl⟩ : syracuseStep 1360219 = 2040329) B2040329
theorem B1360327 : Blo 1207921 1360327 := bstep (se 1 (by rfl) ⟨1020245, by rfl⟩ : syracuseStep 1360327 = 2040491) B2040491
theorem B5161441 : Blo 1207921 5161441 := bstep (se 2 (by rfl) ⟨1935540, by rfl⟩ : syracuseStep 5161441 = 3871081) B3871081
theorem B4358657 : Blo 1207921 4358657 := bstep (se 2 (by rfl) ⟨1634496, by rfl⟩ : syracuseStep 4358657 = 3268993) B3268993
theorem B2040383 : Blo 1207921 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B2294345 : Blo 1207921 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B27902599 : Blo 1207921 27902599 := bstep (se 1 (by rfl) ⟨20926949, by rfl⟩ : syracuseStep 27902599 = 41853899) B41853899
theorem B5808793 : Blo 1207921 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B21504727 : Blo 1207921 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B2720591 : Blo 1207921 2720591 := bstep (se 1 (by rfl) ⟨2040443, by rfl⟩ : syracuseStep 2720591 = 4080887) B4080887
theorem B16548887 : Blo 1207921 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B2720807 : Blo 1207921 2720807 := bstep (se 1 (by rfl) ⟨2040605, by rfl⟩ : syracuseStep 2720807 = 4081211) B4081211
theorem B2581703 : Blo 1207921 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B2720987 : Blo 1207921 2720987 := bstep (se 1 (by rfl) ⟨2040740, by rfl⟩ : syracuseStep 2720987 = 4081481) B4081481
theorem B2016551 : Blo 1207921 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B11322767 : Blo 1207921 11322767 := bstep (se 1 (by rfl) ⟨8492075, by rfl⟩ : syracuseStep 11322767 = 16984151) B16984151
theorem B2721185 : Blo 1207921 2721185 := bstep (se 2 (by rfl) ⟨1020444, by rfl⟩ : syracuseStep 2721185 = 2040889) B2040889
theorem B1812203 : Blo 1207921 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B1812431 : Blo 1207921 1812431 := bstep (se 1 (by rfl) ⟨1359323, by rfl⟩ : syracuseStep 1812431 = 2718647) B2718647
theorem B3057689 : Blo 1207921 3057689 := bstep (se 2 (by rfl) ⟨1146633, by rfl⟩ : syracuseStep 3057689 = 2293267) B2293267
theorem B4081697 : Blo 1207921 4081697 := bstep (se 2 (by rfl) ⟨1530636, by rfl⟩ : syracuseStep 4081697 = 3061273) B3061273
theorem B3442817 : Blo 1207921 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B17426609 : Blo 1207921 17426609 := bstep (se 2 (by rfl) ⟨6534978, by rfl⟩ : syracuseStep 17426609 = 13069957) B13069957
theorem B1812827 : Blo 1207921 1812827 := bstep (se 1 (by rfl) ⟨1359620, by rfl⟩ : syracuseStep 1812827 = 2719241) B2719241
theorem B50317699 : Blo 1207921 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B1452487 : Blo 1207921 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B3058145 : Blo 1207921 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B6121979 : Blo 1207921 6121979 := bstep (se 1 (by rfl) ⟨4591484, by rfl⟩ : syracuseStep 6121979 = 9182969) B9182969
theorem B3058195 : Blo 1207921 3058195 := bstep (se 1 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 3058195 = 4587293) B4587293
theorem B1813055 : Blo 1207921 1813055 := bstep (se 1 (by rfl) ⟨1359791, by rfl⟩ : syracuseStep 1813055 = 2719583) B2719583
theorem B3443273 : Blo 1207921 3443273 := bstep (se 2 (by rfl) ⟨1291227, by rfl⟩ : syracuseStep 3443273 = 2582455) B2582455
theorem B2755193 : Blo 1207921 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B1813175 : Blo 1207921 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B6531779 : Blo 1207921 6531779 := bstep (se 1 (by rfl) ⟨4898834, by rfl⟩ : syracuseStep 6531779 = 9797669) B9797669
theorem B10324691 : Blo 1207921 10324691 := bstep (se 1 (by rfl) ⟨7743518, by rfl⟩ : syracuseStep 10324691 = 15487037) B15487037
theorem B1813403 : Blo 1207921 1813403 := bstep (se 1 (by rfl) ⟨1360052, by rfl⟩ : syracuseStep 1813403 = 2720105) B2720105
theorem B11619395 : Blo 1207921 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B10325069 : Blo 1207921 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B4902077 : Blo 1207921 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B1813799 : Blo 1207921 1813799 := bstep (se 1 (by rfl) ⟨1360349, by rfl⟩ : syracuseStep 1813799 = 2720699) B2720699
theorem B4902241 : Blo 1207921 4902241 := bstep (se 2 (by rfl) ⟨1838340, by rfl⟩ : syracuseStep 4902241 = 3676681) B3676681
theorem B1813883 : Blo 1207921 1813883 := bstep (se 1 (by rfl) ⟨1360412, by rfl⟩ : syracuseStep 1813883 = 2720825) B2720825
theorem B1936777 : Blo 1207921 1936777 := bstep (se 2 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 1936777 = 1452583) B1452583
theorem B1814009 : Blo 1207921 1814009 := bstep (se 2 (by rfl) ⟨680253, by rfl⟩ : syracuseStep 1814009 = 1360507) B1360507
theorem B1814111 : Blo 1207921 1814111 := bstep (se 1 (by rfl) ⟨1360583, by rfl⟩ : syracuseStep 1814111 = 2721167) B2721167
theorem B1208031 : Blo 1207921 1208031 := bstep (se 1 (by rfl) ⟨906023, by rfl⟩ : syracuseStep 1208031 = 1812047) B1812047
theorem B1208111 : Blo 1207921 1208111 := bstep (se 1 (by rfl) ⟨906083, by rfl⟩ : syracuseStep 1208111 = 1812167) B1812167
theorem B1208219 : Blo 1207921 1208219 := bstep (se 1 (by rfl) ⟨906164, by rfl⟩ : syracuseStep 1208219 = 1812329) B1812329
theorem B1208271 : Blo 1207921 1208271 := bstep (se 1 (by rfl) ⟨906203, by rfl⟩ : syracuseStep 1208271 = 1812407) B1812407
theorem B15708113 : Blo 1207921 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B1208295 : Blo 1207921 1208295 := bstep (se 1 (by rfl) ⟨906221, by rfl⟩ : syracuseStep 1208295 = 1812443) B1812443
theorem B6115337 : Blo 1207921 6115337 := bstep (se 2 (by rfl) ⟨2293251, by rfl⟩ : syracuseStep 6115337 = 4586503) B4586503
theorem B6115499 : Blo 1207921 6115499 := bstep (se 1 (by rfl) ⟨4586624, by rfl⟩ : syracuseStep 6115499 = 9173249) B9173249
theorem B3059977 : Blo 1207921 3059977 := bstep (se 2 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 3059977 = 2294983) B2294983
theorem B1208607 : Blo 1207921 1208607 := bstep (se 1 (by rfl) ⟨906455, by rfl⟩ : syracuseStep 1208607 = 1812911) B1812911
theorem B1290535 : Blo 1207921 1290535 := bstep (se 1 (by rfl) ⟨967901, by rfl⟩ : syracuseStep 1290535 = 1935803) B1935803
theorem B1208667 : Blo 1207921 1208667 := bstep (se 1 (by rfl) ⟨906500, by rfl⟩ : syracuseStep 1208667 = 1813001) B1813001
theorem B1208687 : Blo 1207921 1208687 := bstep (se 1 (by rfl) ⟨906515, by rfl⟩ : syracuseStep 1208687 = 1813031) B1813031
theorem B1208743 : Blo 1207921 1208743 := bstep (se 1 (by rfl) ⟨906557, by rfl⟩ : syracuseStep 1208743 = 1813115) B1813115
theorem B9179567 : Blo 1207921 9179567 := bstep (se 1 (by rfl) ⟨6884675, by rfl⟩ : syracuseStep 9179567 = 13769351) B13769351
theorem B3101111 : Blo 1207921 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B1208827 : Blo 1207921 1208827 := bstep (se 1 (by rfl) ⟨906620, by rfl⟩ : syracuseStep 1208827 = 1813241) B1813241
theorem B1208895 : Blo 1207921 1208895 := bstep (se 1 (by rfl) ⟨906671, by rfl⟩ : syracuseStep 1208895 = 1813343) B1813343
theorem B1208903 : Blo 1207921 1208903 := bstep (se 1 (by rfl) ⟨906677, by rfl⟩ : syracuseStep 1208903 = 1813355) B1813355
theorem B6115985 : Blo 1207921 6115985 := bstep (se 2 (by rfl) ⟨2293494, by rfl⟩ : syracuseStep 6115985 = 4586989) B4586989
theorem B55816877 : Blo 1207921 55816877 := bstep (se 3 (by rfl) ⟨10465664, by rfl⟩ : syracuseStep 55816877 = 20931329) B20931329
theorem B15110855 : Blo 1207921 15110855 := bstep (se 1 (by rfl) ⟨11333141, by rfl⟩ : syracuseStep 15110855 = 22666283) B22666283
theorem B1209055 : Blo 1207921 1209055 := bstep (se 1 (by rfl) ⟨906791, by rfl⟩ : syracuseStep 1209055 = 1813583) B1813583
theorem B1209135 : Blo 1207921 1209135 := bstep (se 1 (by rfl) ⟨906851, by rfl⟩ : syracuseStep 1209135 = 1813703) B1813703
theorem B6370127 : Blo 1207921 6370127 := bstep (se 1 (by rfl) ⟨4777595, by rfl⟩ : syracuseStep 6370127 = 9555191) B9555191
theorem B16536413 : Blo 1207921 16536413 := bstep (se 3 (by rfl) ⟨3100577, by rfl⟩ : syracuseStep 16536413 = 6201155) B6201155
theorem B1209243 : Blo 1207921 1209243 := bstep (se 1 (by rfl) ⟨906932, by rfl⟩ : syracuseStep 1209243 = 1813865) B1813865
theorem B1209295 : Blo 1207921 1209295 := bstep (se 1 (by rfl) ⟨906971, by rfl⟩ : syracuseStep 1209295 = 1813943) B1813943
theorem B1209319 : Blo 1207921 1209319 := bstep (se 1 (by rfl) ⟨906989, by rfl⟩ : syracuseStep 1209319 = 1813979) B1813979
theorem B7845113 : Blo 1207921 7845113 := bstep (se 2 (by rfl) ⟨2941917, by rfl⟩ : syracuseStep 7845113 = 5883835) B5883835
theorem B11777303 : Blo 1207921 11777303 := bstep (se 1 (by rfl) ⟨8832977, by rfl⟩ : syracuseStep 11777303 = 17665955) B17665955
theorem B8271143 : Blo 1207921 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B3266345 : Blo 1207921 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B5101417 : Blo 1207921 5101417 := bstep (se 2 (by rfl) ⟨1913031, by rfl⟩ : syracuseStep 5101417 = 3826063) B3826063
theorem B10328107 : Blo 1207921 10328107 := bstep (se 1 (by rfl) ⟨7746080, by rfl⟩ : syracuseStep 10328107 = 15492161) B15492161
theorem B15702295 : Blo 1207921 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B3103001 : Blo 1207921 3103001 := bstep (se 2 (by rfl) ⟨1163625, by rfl⟩ : syracuseStep 3103001 = 2327251) B2327251
theorem B8714573 : Blo 1207921 8714573 := bstep (se 3 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 8714573 = 3267965) B3267965
theorem B11614589 : Blo 1207921 11614589 := bstep (se 3 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 11614589 = 4355471) B4355471
theorem B2177599 : Blo 1207921 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B2718287 : Blo 1207921 2718287 := bstep (se 1 (by rfl) ⟨2038715, by rfl⟩ : syracuseStep 2718287 = 4077431) B4077431
theorem B4078187 : Blo 1207921 4078187 := bstep (se 1 (by rfl) ⟨3058640, by rfl⟩ : syracuseStep 4078187 = 6117281) B6117281
theorem B33094277 : Blo 1207921 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B2718431 : Blo 1207921 2718431 := bstep (se 1 (by rfl) ⟨2038823, by rfl⟩ : syracuseStep 2718431 = 4077647) B4077647
theorem B670088051 : Blo 1207921 670088051 := bstep (se 1 (by rfl) ⟨502566038, by rfl⟩ : syracuseStep 670088051 = 1005132077) B1005132077
theorem B2718683 : Blo 1207921 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B6118415 : Blo 1207921 6118415 := bstep (se 1 (by rfl) ⟨4588811, by rfl⟩ : syracuseStep 6118415 = 9177623) B9177623
theorem B2718863 : Blo 1207921 2718863 := bstep (se 1 (by rfl) ⟨2039147, by rfl⟩ : syracuseStep 2718863 = 4078295) B4078295
theorem B5160125 : Blo 1207921 5160125 := bstep (se 3 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 5160125 = 1935047) B1935047
theorem B4078781 : Blo 1207921 4078781 := bstep (se 3 (by rfl) ⟨764771, by rfl⟩ : syracuseStep 4078781 = 1529543) B1529543
theorem B1359067 : Blo 1207921 1359067 := bstep (se 1 (by rfl) ⟨1019300, by rfl⟩ : syracuseStep 1359067 = 2038601) B2038601
theorem B2718953 : Blo 1207921 2718953 := bstep (se 2 (by rfl) ⟨1019607, by rfl⟩ : syracuseStep 2718953 = 2039215) B2039215
theorem B2719007 : Blo 1207921 2719007 := bstep (se 1 (by rfl) ⟨2039255, by rfl⟩ : syracuseStep 2719007 = 4078511) B4078511
theorem B5586425 : Blo 1207921 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B1359355 : Blo 1207921 1359355 := bstep (se 1 (by rfl) ⟨1019516, by rfl⟩ : syracuseStep 1359355 = 2039033) B2039033
theorem B10468889 : Blo 1207921 10468889 := bstep (se 2 (by rfl) ⟨3925833, by rfl⟩ : syracuseStep 10468889 = 7851667) B7851667
theorem B2293343 : Blo 1207921 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1359535 : Blo 1207921 1359535 := bstep (se 1 (by rfl) ⟨1019651, by rfl⟩ : syracuseStep 1359535 = 2039303) B2039303
theorem B2039593 : Blo 1207921 2039593 := bstep (se 2 (by rfl) ⟨764847, by rfl⟩ : syracuseStep 2039593 = 1529695) B1529695
theorem B2719529 : Blo 1207921 2719529 := bstep (se 2 (by rfl) ⟨1019823, by rfl⟩ : syracuseStep 2719529 = 2039647) B2039647
theorem B5513017 : Blo 1207921 5513017 := bstep (se 2 (by rfl) ⟨2067381, by rfl⟩ : syracuseStep 5513017 = 4134763) B4134763
theorem B6119225 : Blo 1207921 6119225 := bstep (se 2 (by rfl) ⟨2294709, by rfl⟩ : syracuseStep 6119225 = 4589419) B4589419
theorem B1359823 : Blo 1207921 1359823 := bstep (se 1 (by rfl) ⟨1019867, by rfl⟩ : syracuseStep 1359823 = 2039735) B2039735
theorem B13770809 : Blo 1207921 13770809 := bstep (se 2 (by rfl) ⟨5164053, by rfl⟩ : syracuseStep 13770809 = 10328107) B10328107
theorem B44130365 : Blo 1207921 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B6119711 : Blo 1207921 6119711 := bstep (se 1 (by rfl) ⟨4589783, by rfl⟩ : syracuseStep 6119711 = 9179567) B9179567
theorem B4079969 : Blo 1207921 4079969 := bstep (se 2 (by rfl) ⟨1529988, by rfl⟩ : syracuseStep 4079969 = 3059977) B3059977
theorem B1360255 : Blo 1207921 1360255 := bstep (se 1 (by rfl) ⟨1020191, by rfl⟩ : syracuseStep 1360255 = 2040383) B2040383
theorem B6881921 : Blo 1207921 6881921 := bstep (se 2 (by rfl) ⟨2580720, by rfl⟩ : syracuseStep 6881921 = 5161441) B5161441
theorem B1721135 : Blo 1207921 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B1344367 : Blo 1207921 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B5514095 : Blo 1207921 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B28672969 : Blo 1207921 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B2721131 : Blo 1207921 2721131 := bstep (se 1 (by rfl) ⟨2040848, by rfl⟩ : syracuseStep 2721131 = 4081697) B4081697
theorem B2295211 : Blo 1207921 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B11617739 : Blo 1207921 11617739 := bstep (se 1 (by rfl) ⟨8713304, by rfl⟩ : syracuseStep 11617739 = 17426609) B17426609
theorem B6882853 : Blo 1207921 6882853 := bstep (se 4 (by rfl) ⟨645267, by rfl⟩ : syracuseStep 6882853 = 1290535) B1290535
theorem B5809715 : Blo 1207921 5809715 := bstep (se 1 (by rfl) ⟨4357286, by rfl⟩ : syracuseStep 5809715 = 8714573) B8714573
theorem B7743059 : Blo 1207921 7743059 := bstep (se 1 (by rfl) ⟨5807294, by rfl⟩ : syracuseStep 7743059 = 11614589) B11614589
theorem B1812089 : Blo 1207921 1812089 := bstep (se 2 (by rfl) ⟨679533, by rfl⟩ : syracuseStep 1812089 = 1359067) B1359067
theorem B4081319 : Blo 1207921 4081319 := bstep (se 1 (by rfl) ⟨3060989, by rfl⟩ : syracuseStep 4081319 = 6121979) B6121979
theorem B2295515 : Blo 1207921 2295515 := bstep (se 1 (by rfl) ⟨1721636, by rfl⟩ : syracuseStep 2295515 = 3443273) B3443273
theorem B1812191 : Blo 1207921 1812191 := bstep (se 1 (by rfl) ⟨1359143, by rfl⟩ : syracuseStep 1812191 = 2718287) B2718287
theorem B22062851 : Blo 1207921 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B6883127 : Blo 1207921 6883127 := bstep (se 1 (by rfl) ⟨5162345, by rfl⟩ : syracuseStep 6883127 = 10324691) B10324691
theorem B1812287 : Blo 1207921 1812287 := bstep (se 1 (by rfl) ⟨1359215, by rfl⟩ : syracuseStep 1812287 = 2718431) B2718431
theorem B2582369 : Blo 1207921 2582369 := bstep (se 2 (by rfl) ⟨968388, by rfl⟩ : syracuseStep 2582369 = 1936777) B1936777
theorem B1812455 : Blo 1207921 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B1812473 : Blo 1207921 1812473 := bstep (se 2 (by rfl) ⟨679677, by rfl⟩ : syracuseStep 1812473 = 1359355) B1359355
theorem B6883379 : Blo 1207921 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1812575 : Blo 1207921 1812575 := bstep (se 1 (by rfl) ⟨1359431, by rfl⟩ : syracuseStep 1812575 = 2718863) B2718863
theorem B8710253 : Blo 1207921 8710253 := bstep (se 3 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 8710253 = 3266345) B3266345
theorem B1812635 : Blo 1207921 1812635 := bstep (se 1 (by rfl) ⟨1359476, by rfl⟩ : syracuseStep 1812635 = 2718953) B2718953
theorem B1812671 : Blo 1207921 1812671 := bstep (se 1 (by rfl) ⟨1359503, by rfl⟩ : syracuseStep 1812671 = 2719007) B2719007
theorem B1812713 : Blo 1207921 1812713 := bstep (se 2 (by rfl) ⟨679767, by rfl⟩ : syracuseStep 1812713 = 1359535) B1359535
theorem B7350689 : Blo 1207921 7350689 := bstep (se 2 (by rfl) ⟨2756508, by rfl⟩ : syracuseStep 7350689 = 5513017) B5513017
theorem B6801889 : Blo 1207921 6801889 := bstep (se 2 (by rfl) ⟨2550708, by rfl⟩ : syracuseStep 6801889 = 5101417) B5101417
theorem B1813019 : Blo 1207921 1813019 := bstep (se 1 (by rfl) ⟨1359764, by rfl⟩ : syracuseStep 1813019 = 2719529) B2719529
theorem B1813097 : Blo 1207921 1813097 := bstep (se 2 (by rfl) ⟨679911, by rfl⟩ : syracuseStep 1813097 = 1359823) B1359823
theorem B10472075 : Blo 1207921 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B2067407 : Blo 1207921 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B37211251 : Blo 1207921 37211251 := bstep (se 1 (by rfl) ⟨27908438, by rfl⟩ : syracuseStep 37211251 = 55816877) B55816877
theorem B1813625 : Blo 1207921 1813625 := bstep (se 2 (by rfl) ⟨680109, by rfl⟩ : syracuseStep 1813625 = 1360219) B1360219
theorem B4246751 : Blo 1207921 4246751 := bstep (se 1 (by rfl) ⟨3185063, by rfl⟩ : syracuseStep 4246751 = 6370127) B6370127
theorem B1813727 : Blo 1207921 1813727 := bstep (se 1 (by rfl) ⟨1360295, by rfl⟩ : syracuseStep 1813727 = 2720591) B2720591
theorem B1936649 : Blo 1207921 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B1813769 : Blo 1207921 1813769 := bstep (se 2 (by rfl) ⟨680163, by rfl⟩ : syracuseStep 1813769 = 1360327) B1360327
theorem B1813871 : Blo 1207921 1813871 := bstep (se 1 (by rfl) ⟨1360403, by rfl⟩ : syracuseStep 1813871 = 2720807) B2720807
theorem B2903465 : Blo 1207921 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B1813991 : Blo 1207921 1813991 := bstep (se 1 (by rfl) ⟨1360493, by rfl⟩ : syracuseStep 1813991 = 2720987) B2720987
theorem B7851535 : Blo 1207921 7851535 := bstep (se 1 (by rfl) ⟨5888651, by rfl⟩ : syracuseStep 7851535 = 11777303) B11777303
theorem B7745057 : Blo 1207921 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B7548511 : Blo 1207921 7548511 := bstep (se 1 (by rfl) ⟨5661383, by rfl⟩ : syracuseStep 7548511 = 11322767) B11322767
theorem B1814123 : Blo 1207921 1814123 := bstep (se 1 (by rfl) ⟨1360592, by rfl⟩ : syracuseStep 1814123 = 2721185) B2721185
theorem B1208135 : Blo 1207921 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B1208287 : Blo 1207921 1208287 := bstep (se 1 (by rfl) ⟨906215, by rfl⟩ : syracuseStep 1208287 = 1812431) B1812431
theorem B2068667 : Blo 1207921 2068667 := bstep (se 1 (by rfl) ⟨1551500, by rfl⟩ : syracuseStep 2068667 = 3103001) B3103001
theorem B1208551 : Blo 1207921 1208551 := bstep (se 1 (by rfl) ⟨906413, by rfl⟩ : syracuseStep 1208551 = 1812827) B1812827
theorem B1208703 : Blo 1207921 1208703 := bstep (se 1 (by rfl) ⟨906527, by rfl⟩ : syracuseStep 1208703 = 1813055) B1813055
theorem B1208783 : Blo 1207921 1208783 := bstep (se 1 (by rfl) ⟨906587, by rfl⟩ : syracuseStep 1208783 = 1813175) B1813175
theorem B4354519 : Blo 1207921 4354519 := bstep (se 1 (by rfl) ⟨3265889, by rfl⟩ : syracuseStep 4354519 = 6531779) B6531779
theorem B1208935 : Blo 1207921 1208935 := bstep (se 1 (by rfl) ⟨906701, by rfl⟩ : syracuseStep 1208935 = 1813403) B1813403
theorem B7746263 : Blo 1207921 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B1209199 : Blo 1207921 1209199 := bstep (se 1 (by rfl) ⟨906899, by rfl⟩ : syracuseStep 1209199 = 1813799) B1813799
theorem B1209255 : Blo 1207921 1209255 := bstep (se 1 (by rfl) ⟨906941, by rfl⟩ : syracuseStep 1209255 = 1813883) B1813883
theorem B3724283 : Blo 1207921 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B1209339 : Blo 1207921 1209339 := bstep (se 1 (by rfl) ⟨907004, by rfl⟩ : syracuseStep 1209339 = 1814009) B1814009
theorem B1528895 : Blo 1207921 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B1209407 : Blo 1207921 1209407 := bstep (se 1 (by rfl) ⟨907055, by rfl⟩ : syracuseStep 1209407 = 1814111) B1814111
theorem B4076891 : Blo 1207921 4076891 := bstep (se 1 (by rfl) ⟨3057668, by rfl⟩ : syracuseStep 4076891 = 6115337) B6115337
theorem B5510587 : Blo 1207921 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B6116795 : Blo 1207921 6116795 := bstep (se 1 (by rfl) ⟨4587596, by rfl⟩ : syracuseStep 6116795 = 9175193) B9175193
theorem B13424059 : Blo 1207921 13424059 := bstep (se 1 (by rfl) ⟨10068044, by rfl⟩ : syracuseStep 13424059 = 20136089) B20136089
theorem B4076999 : Blo 1207921 4076999 := bstep (se 1 (by rfl) ⟨3057749, by rfl⟩ : syracuseStep 4076999 = 6115499) B6115499
theorem B20936393 : Blo 1207921 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B4077323 : Blo 1207921 4077323 := bstep (se 1 (by rfl) ⟨3057992, by rfl⟩ : syracuseStep 4077323 = 6115985) B6115985
theorem B10073903 : Blo 1207921 10073903 := bstep (se 1 (by rfl) ⟨7555427, by rfl⟩ : syracuseStep 10073903 = 15110855) B15110855
theorem B13072205 : Blo 1207921 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B67090265 : Blo 1207921 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B11024275 : Blo 1207921 11024275 := bstep (se 1 (by rfl) ⟨8268206, by rfl⟩ : syracuseStep 11024275 = 16536413) B16536413
theorem B20920301 : Blo 1207921 20920301 := bstep (se 3 (by rfl) ⟨3922556, by rfl⟩ : syracuseStep 20920301 = 7845113) B7845113
theorem B4077593 : Blo 1207921 4077593 := bstep (se 2 (by rfl) ⟨1529097, by rfl⟩ : syracuseStep 4077593 = 3058195) B3058195
theorem B148813861 : Blo 1207921 148813861 := bstep (se 4 (by rfl) ⟨13951299, by rfl⟩ : syracuseStep 148813861 = 27902599) B27902599
theorem B11623085 : Blo 1207921 11623085 := bstep (se 3 (by rfl) ⟨2179328, by rfl⟩ : syracuseStep 11623085 = 4358657) B4358657
theorem B2038459 : Blo 1207921 2038459 := bstep (se 1 (by rfl) ⟨1528844, by rfl⟩ : syracuseStep 2038459 = 3057689) B3057689
theorem B6118253 : Blo 1207921 6118253 := bstep (se 3 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 6118253 = 2294345) B2294345
theorem B2038763 : Blo 1207921 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B7347181 : Blo 1207921 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B2718791 : Blo 1207921 2718791 := bstep (se 1 (by rfl) ⟨2039093, by rfl⟩ : syracuseStep 2718791 = 4078187) B4078187
theorem B6536321 : Blo 1207921 6536321 := bstep (se 2 (by rfl) ⟨2451120, by rfl⟩ : syracuseStep 6536321 = 4902241) B4902241
theorem B446725367 : Blo 1207921 446725367 := bstep (se 1 (by rfl) ⟨335044025, by rfl⟩ : syracuseStep 446725367 = 670088051) B670088051
theorem B4078943 : Blo 1207921 4078943 := bstep (se 1 (by rfl) ⟨3059207, by rfl⟩ : syracuseStep 4078943 = 6118415) B6118415
theorem B3440083 : Blo 1207921 3440083 := bstep (se 1 (by rfl) ⟨2580062, by rfl⟩ : syracuseStep 3440083 = 5160125) B5160125
theorem B2719187 : Blo 1207921 2719187 := bstep (se 1 (by rfl) ⟨2039390, by rfl⟩ : syracuseStep 2719187 = 4078781) B4078781
theorem B6979259 : Blo 1207921 6979259 := bstep (se 1 (by rfl) ⟨5234444, by rfl⟩ : syracuseStep 6979259 = 10468889) B10468889
theorem B2719457 : Blo 1207921 2719457 := bstep (se 2 (by rfl) ⟨1019796, by rfl⟩ : syracuseStep 2719457 = 2039593) B2039593
theorem B4079483 : Blo 1207921 4079483 := bstep (se 1 (by rfl) ⟨3059612, by rfl⟩ : syracuseStep 4079483 = 6119225) B6119225
theorem B198418481 : Blo 1207921 198418481 := bstep (se 2 (by rfl) ⟨74406930, by rfl⟩ : syracuseStep 198418481 = 148813861) B148813861
theorem B4079807 : Blo 1207921 4079807 := bstep (se 1 (by rfl) ⟨3059855, by rfl⟩ : syracuseStep 4079807 = 6119711) B6119711
theorem B2719979 : Blo 1207921 2719979 := bstep (se 1 (by rfl) ⟨2039984, by rfl⟩ : syracuseStep 2719979 = 4079969) B4079969
theorem B4587947 : Blo 1207921 4587947 := bstep (se 1 (by rfl) ⟨3440960, by rfl⟩ : syracuseStep 4587947 = 6881921) B6881921
theorem B9069185 : Blo 1207921 9069185 := bstep (se 2 (by rfl) ⟨3400944, by rfl⟩ : syracuseStep 9069185 = 6801889) B6801889
theorem B2482855 : Blo 1207921 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B5162039 : Blo 1207921 5162039 := bstep (se 1 (by rfl) ⟨3871529, by rfl⟩ : syracuseStep 5162039 = 7743059) B7743059
theorem B7742573 : Blo 1207921 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B2720879 : Blo 1207921 2720879 := bstep (se 1 (by rfl) ⟨2040659, by rfl⟩ : syracuseStep 2720879 = 4081319) B4081319
theorem B4588751 : Blo 1207921 4588751 := bstep (se 1 (by rfl) ⟨3441563, by rfl⟩ : syracuseStep 4588751 = 6883127) B6883127
theorem B1721579 : Blo 1207921 1721579 := bstep (se 1 (by rfl) ⟨1291184, by rfl⟩ : syracuseStep 1721579 = 2582369) B2582369
theorem B4588919 : Blo 1207921 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B4900459 : Blo 1207921 4900459 := bstep (se 1 (by rfl) ⟨3675344, by rfl⟩ : syracuseStep 4900459 = 7350689) B7350689
theorem B6981383 : Blo 1207921 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B7169957 : Blo 1207921 7169957 := bstep (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) B1344367
theorem B1812527 : Blo 1207921 1812527 := bstep (se 1 (by rfl) ⟨1359395, by rfl⟩ : syracuseStep 1812527 = 2718791) B2718791
theorem B9177137 : Blo 1207921 9177137 := bstep (se 2 (by rfl) ⟨3441426, by rfl⟩ : syracuseStep 9177137 = 6882853) B6882853
theorem B4589693 : Blo 1207921 4589693 := bstep (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) B1721135
theorem B26863741 : Blo 1207921 26863741 := bstep (se 3 (by rfl) ⟨5036951, by rfl⟩ : syracuseStep 26863741 = 10073903) B10073903
theorem B1812791 : Blo 1207921 1812791 := bstep (se 1 (by rfl) ⟨1359593, by rfl⟩ : syracuseStep 1812791 = 2719187) B2719187
theorem B5163371 : Blo 1207921 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B1812971 : Blo 1207921 1812971 := bstep (se 1 (by rfl) ⟨1359728, by rfl⟩ : syracuseStep 1812971 = 2719457) B2719457
theorem B14699033 : Blo 1207921 14699033 := bstep (se 2 (by rfl) ⟨5512137, by rfl⟩ : syracuseStep 14699033 = 11024275) B11024275
theorem B29420243 : Blo 1207921 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1379111 : Blo 1207921 1379111 := bstep (se 1 (by rfl) ⟨1034333, by rfl⟩ : syracuseStep 1379111 = 2068667) B2068667
theorem B5164175 : Blo 1207921 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B1813673 : Blo 1207921 1813673 := bstep (se 2 (by rfl) ⟨680127, by rfl⟩ : syracuseStep 1813673 = 1360255) B1360255
theorem B5164397 : Blo 1207921 5164397 := bstep (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) B1936649
theorem B1814087 : Blo 1207921 1814087 := bstep (se 1 (by rfl) ⟨1360565, by rfl⟩ : syracuseStep 1814087 = 2721131) B2721131
theorem B7745159 : Blo 1207921 7745159 := bstep (se 1 (by rfl) ⟨5808869, by rfl⟩ : syracuseStep 7745159 = 11617739) B11617739
theorem B1208059 : Blo 1207921 1208059 := bstep (se 1 (by rfl) ⟨906044, by rfl⟩ : syracuseStep 1208059 = 1812089) B1812089
theorem B1208127 : Blo 1207921 1208127 := bstep (se 1 (by rfl) ⟨906095, by rfl⟩ : syracuseStep 1208127 = 1812191) B1812191
theorem B14708567 : Blo 1207921 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1208191 : Blo 1207921 1208191 := bstep (se 1 (by rfl) ⟨906143, by rfl⟩ : syracuseStep 1208191 = 1812287) B1812287
theorem B1208303 : Blo 1207921 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B13946867 : Blo 1207921 13946867 := bstep (se 1 (by rfl) ⟨10460150, by rfl⟩ : syracuseStep 13946867 = 20920301) B20920301
theorem B1208315 : Blo 1207921 1208315 := bstep (se 1 (by rfl) ⟨906236, by rfl⟩ : syracuseStep 1208315 = 1812473) B1812473
theorem B1208383 : Blo 1207921 1208383 := bstep (se 1 (by rfl) ⟨906287, by rfl⟩ : syracuseStep 1208383 = 1812575) B1812575
theorem B1208423 : Blo 1207921 1208423 := bstep (se 1 (by rfl) ⟨906317, by rfl⟩ : syracuseStep 1208423 = 1812635) B1812635
theorem B1208447 : Blo 1207921 1208447 := bstep (se 1 (by rfl) ⟨906335, by rfl⟩ : syracuseStep 1208447 = 1812671) B1812671
theorem B49615001 : Blo 1207921 49615001 := bstep (se 2 (by rfl) ⟨18605625, by rfl⟩ : syracuseStep 49615001 = 37211251) B37211251
theorem B1208475 : Blo 1207921 1208475 := bstep (se 1 (by rfl) ⟨906356, by rfl⟩ : syracuseStep 1208475 = 1812713) B1812713
theorem B1208679 : Blo 1207921 1208679 := bstep (se 1 (by rfl) ⟨906509, by rfl⟩ : syracuseStep 1208679 = 1813019) B1813019
theorem B1208731 : Blo 1207921 1208731 := bstep (se 1 (by rfl) ⟨906548, by rfl⟩ : syracuseStep 1208731 = 1813097) B1813097
theorem B3060281 : Blo 1207921 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B1209083 : Blo 1207921 1209083 := bstep (se 1 (by rfl) ⟨906812, by rfl⟩ : syracuseStep 1209083 = 1813625) B1813625
theorem B10064681 : Blo 1207921 10064681 := bstep (se 2 (by rfl) ⟨3774255, by rfl⟩ : syracuseStep 10064681 = 7548511) B7548511
theorem B2831167 : Blo 1207921 2831167 := bstep (se 1 (by rfl) ⟨2123375, by rfl⟩ : syracuseStep 2831167 = 4246751) B4246751
theorem B1209151 : Blo 1207921 1209151 := bstep (se 1 (by rfl) ⟨906863, by rfl⟩ : syracuseStep 1209151 = 1813727) B1813727
theorem B297816911 : Blo 1207921 297816911 := bstep (se 1 (by rfl) ⟨223362683, by rfl⟩ : syracuseStep 297816911 = 446725367) B446725367
theorem B1209179 : Blo 1207921 1209179 := bstep (se 1 (by rfl) ⟨906884, by rfl⟩ : syracuseStep 1209179 = 1813769) B1813769
theorem B1209247 : Blo 1207921 1209247 := bstep (se 1 (by rfl) ⟨906935, by rfl⟩ : syracuseStep 1209247 = 1813871) B1813871
theorem B1209327 : Blo 1207921 1209327 := bstep (se 1 (by rfl) ⟨906995, by rfl⟩ : syracuseStep 1209327 = 1813991) B1813991
theorem B1209415 : Blo 1207921 1209415 := bstep (se 1 (by rfl) ⟨907061, by rfl⟩ : syracuseStep 1209415 = 1814123) B1814123
theorem B9180539 : Blo 1207921 9180539 := bstep (se 1 (by rfl) ⟨6885404, by rfl⟩ : syracuseStep 9180539 = 13770809) B13770809
theorem B4077053 : Blo 1207921 4077053 := bstep (se 3 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 4077053 = 1528895) B1528895
theorem B167499413 : Blo 1207921 167499413 := bstep (se 6 (by rfl) ⟨3925767, by rfl⟩ : syracuseStep 167499413 = 7851535) B7851535
theorem B3676063 : Blo 1207921 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B5806025 : Blo 1207921 5806025 := bstep (se 2 (by rfl) ⟨2177259, by rfl⟩ : syracuseStep 5806025 = 4354519) B4354519
theorem B2717927 : Blo 1207921 2717927 := bstep (se 1 (by rfl) ⟨2038445, by rfl⟩ : syracuseStep 2717927 = 4076891) B4076891
theorem B2717945 : Blo 1207921 2717945 := bstep (se 2 (by rfl) ⟨1019229, by rfl⟩ : syracuseStep 2717945 = 2038459) B2038459
theorem B4077863 : Blo 1207921 4077863 := bstep (se 1 (by rfl) ⟨3058397, by rfl⟩ : syracuseStep 4077863 = 6116795) B6116795
theorem B2717999 : Blo 1207921 2717999 := bstep (se 1 (by rfl) ⟨2038499, by rfl⟩ : syracuseStep 2717999 = 4076999) B4076999
theorem B3873143 : Blo 1207921 3873143 := bstep (se 1 (by rfl) ⟨2904857, by rfl⟩ : syracuseStep 3873143 = 5809715) B5809715
theorem B13957595 : Blo 1207921 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B1530343 : Blo 1207921 1530343 := bstep (se 1 (by rfl) ⟨1147757, by rfl⟩ : syracuseStep 1530343 = 2295515) B2295515
theorem B2718215 : Blo 1207921 2718215 := bstep (se 1 (by rfl) ⟨2038661, by rfl⟩ : syracuseStep 2718215 = 4077323) B4077323
theorem B8714803 : Blo 1207921 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B44726843 : Blo 1207921 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B38230625 : Blo 1207921 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B9796241 : Blo 1207921 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B2718395 : Blo 1207921 2718395 := bstep (se 1 (by rfl) ⟨2038796, by rfl⟩ : syracuseStep 2718395 = 4077593) B4077593
theorem B5806835 : Blo 1207921 5806835 := bstep (se 1 (by rfl) ⟨4355126, by rfl⟩ : syracuseStep 5806835 = 8710253) B8710253
theorem B7748723 : Blo 1207921 7748723 := bstep (se 1 (by rfl) ⟨5811542, by rfl⟩ : syracuseStep 7748723 = 11623085) B11623085
theorem B4078835 : Blo 1207921 4078835 := bstep (se 1 (by rfl) ⟨3059126, by rfl⟩ : syracuseStep 4078835 = 6118253) B6118253
theorem B7347449 : Blo 1207921 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B17898745 : Blo 1207921 17898745 := bstep (se 2 (by rfl) ⟨6712029, by rfl⟩ : syracuseStep 17898745 = 13424059) B13424059
theorem B4586777 : Blo 1207921 4586777 := bstep (se 2 (by rfl) ⟨1720041, by rfl⟩ : syracuseStep 4586777 = 3440083) B3440083
theorem B1359175 : Blo 1207921 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B4357547 : Blo 1207921 4357547 := bstep (se 1 (by rfl) ⟨3268160, by rfl⟩ : syracuseStep 4357547 = 6536321) B6536321
theorem B22052341 : Blo 1207921 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B2719295 : Blo 1207921 2719295 := bstep (se 1 (by rfl) ⟨2039471, by rfl⟩ : syracuseStep 2719295 = 4078943) B4078943
theorem B4652839 : Blo 1207921 4652839 := bstep (se 1 (by rfl) ⟨3489629, by rfl⟩ : syracuseStep 4652839 = 6979259) B6979259
theorem B2719655 : Blo 1207921 2719655 := bstep (se 1 (by rfl) ⟨2039741, by rfl⟩ : syracuseStep 2719655 = 4079483) B4079483
theorem B2719871 : Blo 1207921 2719871 := bstep (se 1 (by rfl) ⟨2039903, by rfl⟩ : syracuseStep 2719871 = 4079807) B4079807
theorem B2040187 : Blo 1207921 2040187 := bstep (se 1 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 2040187 = 3060281) B3060281
theorem B6046123 : Blo 1207921 6046123 := bstep (se 1 (by rfl) ⟨4534592, by rfl⟩ : syracuseStep 6046123 = 9069185) B9069185
theorem B6709787 : Blo 1207921 6709787 := bstep (se 1 (by rfl) ⟨5032340, by rfl⟩ : syracuseStep 6709787 = 10064681) B10064681
theorem B2040457 : Blo 1207921 2040457 := bstep (se 2 (by rfl) ⟨765171, by rfl⟩ : syracuseStep 2040457 = 1530343) B1530343
theorem B3441359 : Blo 1207921 3441359 := bstep (se 1 (by rfl) ⟨2581019, by rfl⟩ : syracuseStep 3441359 = 5162039) B5162039
theorem B5161715 : Blo 1207921 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B6120359 : Blo 1207921 6120359 := bstep (se 1 (by rfl) ⟨4590269, by rfl⟩ : syracuseStep 6120359 = 9180539) B9180539
theorem B111666275 : Blo 1207921 111666275 := bstep (se 1 (by rfl) ⟨83749706, by rfl⟩ : syracuseStep 111666275 = 167499413) B167499413
theorem B4654255 : Blo 1207921 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B1811951 : Blo 1207921 1811951 := bstep (se 1 (by rfl) ⟨1358963, by rfl⟩ : syracuseStep 1811951 = 2717927) B2717927
theorem B1811963 : Blo 1207921 1811963 := bstep (se 1 (by rfl) ⟨1358972, by rfl⟩ : syracuseStep 1811963 = 2717945) B2717945
theorem B1811999 : Blo 1207921 1811999 := bstep (se 1 (by rfl) ⟨1358999, by rfl⟩ : syracuseStep 1811999 = 2717999) B2717999
theorem B3442247 : Blo 1207921 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B23864993 : Blo 1207921 23864993 := bstep (se 2 (by rfl) ⟨8949372, by rfl⟩ : syracuseStep 23864993 = 17898745) B17898745
theorem B1812143 : Blo 1207921 1812143 := bstep (se 1 (by rfl) ⟨1359107, by rfl⟩ : syracuseStep 1812143 = 2718215) B2718215
theorem B9799355 : Blo 1207921 9799355 := bstep (se 1 (by rfl) ⟨7349516, by rfl⟩ : syracuseStep 9799355 = 14699033) B14699033
theorem B25487083 : Blo 1207921 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B1812233 : Blo 1207921 1812233 := bstep (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) B1359175
theorem B6530827 : Blo 1207921 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B1812263 : Blo 1207921 1812263 := bstep (se 1 (by rfl) ⟨1359197, by rfl⟩ : syracuseStep 1812263 = 2718395) B2718395
theorem B19613495 : Blo 1207921 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B29403121 : Blo 1207921 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B3442783 : Blo 1207921 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B3057851 : Blo 1207921 3057851 := bstep (se 1 (by rfl) ⟨2293388, by rfl⟩ : syracuseStep 3057851 = 4586777) B4586777
theorem B3442931 : Blo 1207921 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B1812863 : Blo 1207921 1812863 := bstep (se 1 (by rfl) ⟨1359647, by rfl⟩ : syracuseStep 1812863 = 2719295) B2719295
theorem B6203785 : Blo 1207921 6203785 := bstep (se 2 (by rfl) ⟨2326419, by rfl⟩ : syracuseStep 6203785 = 4652839) B4652839
theorem B5163439 : Blo 1207921 5163439 := bstep (se 1 (by rfl) ⟨3872579, by rfl⟩ : syracuseStep 5163439 = 7745159) B7745159
theorem B4901417 : Blo 1207921 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B1813103 : Blo 1207921 1813103 := bstep (se 1 (by rfl) ⟨1359827, by rfl⟩ : syracuseStep 1813103 = 2719655) B2719655
theorem B132278987 : Blo 1207921 132278987 := bstep (se 1 (by rfl) ⟨99209240, by rfl⟩ : syracuseStep 132278987 = 198418481) B198418481
theorem B1813319 : Blo 1207921 1813319 := bstep (se 1 (by rfl) ⟨1359989, by rfl⟩ : syracuseStep 1813319 = 2719979) B2719979
theorem B35818321 : Blo 1207921 35818321 := bstep (se 2 (by rfl) ⟨13431870, by rfl⟩ : syracuseStep 35818321 = 26863741) B26863741
theorem B3058631 : Blo 1207921 3058631 := bstep (se 1 (by rfl) ⟨2293973, by rfl⟩ : syracuseStep 3058631 = 4587947) B4587947
theorem B198544607 : Blo 1207921 198544607 := bstep (se 1 (by rfl) ⟨148908455, by rfl⟩ : syracuseStep 198544607 = 297816911) B297816911
theorem B4590877 : Blo 1207921 4590877 := bstep (se 3 (by rfl) ⟨860789, by rfl⟩ : syracuseStep 4590877 = 1721579) B1721579
theorem B11619737 : Blo 1207921 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B1813919 : Blo 1207921 1813919 := bstep (se 1 (by rfl) ⟨1360439, by rfl⟩ : syracuseStep 1813919 = 2720879) B2720879
theorem B3059167 : Blo 1207921 3059167 := bstep (se 1 (by rfl) ⟨2294375, by rfl⟩ : syracuseStep 3059167 = 4588751) B4588751
theorem B13241893 : Blo 1207921 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B3059279 : Blo 1207921 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B9297911 : Blo 1207921 9297911 := bstep (se 1 (by rfl) ⟨6973433, by rfl⟩ : syracuseStep 9297911 = 13946867) B13946867
theorem B4779971 : Blo 1207921 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B3870683 : Blo 1207921 3870683 := bstep (se 1 (by rfl) ⟨2903012, by rfl⟩ : syracuseStep 3870683 = 5806025) B5806025
theorem B1208351 : Blo 1207921 1208351 := bstep (se 1 (by rfl) ⟨906263, by rfl⟩ : syracuseStep 1208351 = 1812527) B1812527
theorem B3059795 : Blo 1207921 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B1208527 : Blo 1207921 1208527 := bstep (se 1 (by rfl) ⟨906395, by rfl⟩ : syracuseStep 1208527 = 1812791) B1812791
theorem B1208647 : Blo 1207921 1208647 := bstep (se 1 (by rfl) ⟨906485, by rfl⟩ : syracuseStep 1208647 = 1812971) B1812971
theorem B3871223 : Blo 1207921 3871223 := bstep (se 1 (by rfl) ⟨2903417, by rfl⟩ : syracuseStep 3871223 = 5806835) B5806835
theorem B5165815 : Blo 1207921 5165815 := bstep (se 1 (by rfl) ⟨3874361, by rfl⟩ : syracuseStep 5165815 = 7748723) B7748723
theorem B1209115 : Blo 1207921 1209115 := bstep (se 1 (by rfl) ⟨906836, by rfl⟩ : syracuseStep 1209115 = 1813673) B1813673
theorem B6533945 : Blo 1207921 6533945 := bstep (se 2 (by rfl) ⟨2450229, by rfl⟩ : syracuseStep 6533945 = 4900459) B4900459
theorem B2905031 : Blo 1207921 2905031 := bstep (se 1 (by rfl) ⟨2178773, by rfl⟩ : syracuseStep 2905031 = 4357547) B4357547
theorem B1209391 : Blo 1207921 1209391 := bstep (se 1 (by rfl) ⟨907043, by rfl⟩ : syracuseStep 1209391 = 1814087) B1814087
theorem B33076667 : Blo 1207921 33076667 := bstep (se 1 (by rfl) ⟨24807500, by rfl⟩ : syracuseStep 33076667 = 49615001) B49615001
theorem B19593197 : Blo 1207921 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B10328381 : Blo 1207921 10328381 := bstep (se 3 (by rfl) ⟨1936571, by rfl⟩ : syracuseStep 10328381 = 3873143) B3873143
theorem B2718035 : Blo 1207921 2718035 := bstep (se 1 (by rfl) ⟨2038526, by rfl⟩ : syracuseStep 2718035 = 4077053) B4077053
theorem B3774889 : Blo 1207921 3774889 := bstep (se 2 (by rfl) ⟨1415583, by rfl⟩ : syracuseStep 3774889 = 2831167) B2831167
theorem B6118091 : Blo 1207921 6118091 := bstep (se 1 (by rfl) ⟨4588568, by rfl⟩ : syracuseStep 6118091 = 9177137) B9177137
theorem B2718575 : Blo 1207921 2718575 := bstep (se 1 (by rfl) ⟨2038931, by rfl⟩ : syracuseStep 2718575 = 4077863) B4077863
theorem B9305063 : Blo 1207921 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B29817895 : Blo 1207921 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B3677629 : Blo 1207921 3677629 := bstep (se 3 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 3677629 = 1379111) B1379111
theorem B2719223 : Blo 1207921 2719223 := bstep (se 1 (by rfl) ⟨2039417, by rfl⟩ : syracuseStep 2719223 = 4078835) B4078835
theorem B9805711 : Blo 1207921 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B2039863 : Blo 1207921 2039863 := bstep (se 1 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 2039863 = 3059795) B3059795
theorem B2580815 : Blo 1207921 2580815 := bstep (se 1 (by rfl) ⟨1935611, by rfl⟩ : syracuseStep 2580815 = 3871223) B3871223
theorem B4473191 : Blo 1207921 4473191 := bstep (se 1 (by rfl) ⟨3354893, by rfl⟩ : syracuseStep 4473191 = 6709787) B6709787
theorem B2294239 : Blo 1207921 2294239 := bstep (se 1 (by rfl) ⟨1720679, by rfl⟩ : syracuseStep 2294239 = 3441359) B3441359
theorem B3441143 : Blo 1207921 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2720249 : Blo 1207921 2720249 := bstep (se 2 (by rfl) ⟨1020093, by rfl⟩ : syracuseStep 2720249 = 2040187) B2040187
theorem B8061497 : Blo 1207921 8061497 := bstep (se 2 (by rfl) ⟨3023061, by rfl⟩ : syracuseStep 8061497 = 6046123) B6046123
theorem B4080239 : Blo 1207921 4080239 := bstep (se 1 (by rfl) ⟨3060179, by rfl⟩ : syracuseStep 4080239 = 6120359) B6120359
theorem B2720609 : Blo 1207921 2720609 := bstep (se 2 (by rfl) ⟨1020228, by rfl⟩ : syracuseStep 2720609 = 2040457) B2040457
theorem B2294831 : Blo 1207921 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B15909995 : Blo 1207921 15909995 := bstep (se 1 (by rfl) ⟨11932496, by rfl⟩ : syracuseStep 15909995 = 23864993) B23864993
theorem B13075663 : Blo 1207921 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B39757193 : Blo 1207921 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B2295287 : Blo 1207921 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B1812023 : Blo 1207921 1812023 := bstep (se 1 (by rfl) ⟨1359017, by rfl⟩ : syracuseStep 1812023 = 2718035) B2718035
theorem B6121169 : Blo 1207921 6121169 := bstep (se 2 (by rfl) ⟨2295438, by rfl⟩ : syracuseStep 6121169 = 4590877) B4590877
theorem B1812383 : Blo 1207921 1812383 := bstep (se 1 (by rfl) ⟨1359287, by rfl⟩ : syracuseStep 1812383 = 2718575) B2718575
theorem B6203375 : Blo 1207921 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B17655857 : Blo 1207921 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B33982777 : Blo 1207921 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B1812815 : Blo 1207921 1812815 := bstep (se 1 (by rfl) ⟨1359611, by rfl⟩ : syracuseStep 1812815 = 2719223) B2719223
theorem B1813247 : Blo 1207921 1813247 := bstep (se 1 (by rfl) ⟨1359935, by rfl⟩ : syracuseStep 1813247 = 2719871) B2719871
theorem B4590377 : Blo 1207921 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B5033185 : Blo 1207921 5033185 := bstep (se 2 (by rfl) ⟨1887444, by rfl⟩ : syracuseStep 5033185 = 3774889) B3774889
theorem B6884585 : Blo 1207921 6884585 := bstep (se 2 (by rfl) ⟨2581719, by rfl⟩ : syracuseStep 6884585 = 5163439) B5163439
theorem B74444183 : Blo 1207921 74444183 := bstep (se 1 (by rfl) ⟨55833137, by rfl⟩ : syracuseStep 74444183 = 111666275) B111666275
theorem B1207967 : Blo 1207921 1207967 := bstep (se 1 (by rfl) ⟨905975, by rfl⟩ : syracuseStep 1207967 = 1811951) B1811951
theorem B1207975 : Blo 1207921 1207975 := bstep (se 1 (by rfl) ⟨905981, by rfl⟩ : syracuseStep 1207975 = 1811963) B1811963
theorem B1207999 : Blo 1207921 1207999 := bstep (se 1 (by rfl) ⟨905999, by rfl⟩ : syracuseStep 1207999 = 1811999) B1811999
theorem B1208095 : Blo 1207921 1208095 := bstep (se 1 (by rfl) ⟨906071, by rfl⟩ : syracuseStep 1208095 = 1812143) B1812143
theorem B6532903 : Blo 1207921 6532903 := bstep (se 1 (by rfl) ⟨4899677, by rfl⟩ : syracuseStep 6532903 = 9799355) B9799355
theorem B1208155 : Blo 1207921 1208155 := bstep (se 1 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 1208155 = 1812233) B1812233
theorem B1208175 : Blo 1207921 1208175 := bstep (se 1 (by rfl) ⟨906131, by rfl⟩ : syracuseStep 1208175 = 1812263) B1812263
theorem B13062131 : Blo 1207921 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B6885587 : Blo 1207921 6885587 := bstep (se 1 (by rfl) ⟨5164190, by rfl⟩ : syracuseStep 6885587 = 10328381) B10328381
theorem B6205673 : Blo 1207921 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B1208575 : Blo 1207921 1208575 := bstep (se 1 (by rfl) ⟨906431, by rfl⟩ : syracuseStep 1208575 = 1812863) B1812863
theorem B1208735 : Blo 1207921 1208735 := bstep (se 1 (by rfl) ⟨906551, by rfl⟩ : syracuseStep 1208735 = 1813103) B1813103
theorem B1208879 : Blo 1207921 1208879 := bstep (se 1 (by rfl) ⟨906659, by rfl⟩ : syracuseStep 1208879 = 1813319) B1813319
theorem B4903505 : Blo 1207921 4903505 := bstep (se 2 (by rfl) ⟨1838814, by rfl⟩ : syracuseStep 4903505 = 3677629) B3677629
theorem B132363071 : Blo 1207921 132363071 := bstep (se 1 (by rfl) ⟨99272303, by rfl⟩ : syracuseStep 132363071 = 198544607) B198544607
theorem B7746491 : Blo 1207921 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B1209279 : Blo 1207921 1209279 := bstep (se 1 (by rfl) ⟨906959, by rfl⟩ : syracuseStep 1209279 = 1813919) B1813919
theorem B7746749 : Blo 1207921 7746749 := bstep (se 3 (by rfl) ⟨1452515, by rfl⟩ : syracuseStep 7746749 = 2905031) B2905031
theorem B24794429 : Blo 1207921 24794429 := bstep (se 3 (by rfl) ⟨4648955, by rfl⟩ : syracuseStep 24794429 = 9297911) B9297911
theorem B39204161 : Blo 1207921 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B8271713 : Blo 1207921 8271713 := bstep (se 2 (by rfl) ⟨3101892, by rfl⟩ : syracuseStep 8271713 = 6203785) B6203785
theorem B4355963 : Blo 1207921 4355963 := bstep (se 1 (by rfl) ⟨3266972, by rfl⟩ : syracuseStep 4355963 = 6533945) B6533945
theorem B22051111 : Blo 1207921 22051111 := bstep (se 1 (by rfl) ⟨16538333, by rfl⟩ : syracuseStep 22051111 = 33076667) B33076667
theorem B6887753 : Blo 1207921 6887753 := bstep (se 2 (by rfl) ⟨2582907, by rfl⟩ : syracuseStep 6887753 = 5165815) B5165815
theorem B47757761 : Blo 1207921 47757761 := bstep (se 2 (by rfl) ⟨17909160, by rfl⟩ : syracuseStep 47757761 = 35818321) B35818321
theorem B2038567 : Blo 1207921 2038567 := bstep (se 1 (by rfl) ⟨1528925, by rfl⟩ : syracuseStep 2038567 = 3057851) B3057851
theorem B3267611 : Blo 1207921 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B88185991 : Blo 1207921 88185991 := bstep (se 1 (by rfl) ⟨66139493, by rfl⟩ : syracuseStep 88185991 = 132278987) B132278987
theorem B4078727 : Blo 1207921 4078727 := bstep (se 1 (by rfl) ⟨3059045, by rfl⟩ : syracuseStep 4078727 = 6118091) B6118091
theorem B4078889 : Blo 1207921 4078889 := bstep (se 2 (by rfl) ⟨1529583, by rfl⟩ : syracuseStep 4078889 = 3059167) B3059167
theorem B2039087 : Blo 1207921 2039087 := bstep (se 1 (by rfl) ⟨1529315, by rfl⟩ : syracuseStep 2039087 = 3058631) B3058631
theorem B8707769 : Blo 1207921 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B2039519 : Blo 1207921 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B13074281 : Blo 1207921 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B3186647 : Blo 1207921 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B2580455 : Blo 1207921 2580455 := bstep (se 1 (by rfl) ⟨1935341, by rfl⟩ : syracuseStep 2580455 = 3870683) B3870683
theorem B2719817 : Blo 1207921 2719817 := bstep (se 2 (by rfl) ⟨1019931, by rfl⟩ : syracuseStep 2719817 = 2039863) B2039863
theorem B6119549 : Blo 1207921 6119549 := bstep (se 3 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 6119549 = 2294831) B2294831
theorem B1720543 : Blo 1207921 1720543 := bstep (se 1 (by rfl) ⟨1290407, by rfl⟩ : syracuseStep 1720543 = 2580815) B2580815
theorem B2294095 : Blo 1207921 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B5374331 : Blo 1207921 5374331 := bstep (se 1 (by rfl) ⟨4030748, by rfl⟩ : syracuseStep 5374331 = 8061497) B8061497
theorem B29401481 : Blo 1207921 29401481 := bstep (se 2 (by rfl) ⟨11025555, by rfl⟩ : syracuseStep 29401481 = 22051111) B22051111
theorem B3269003 : Blo 1207921 3269003 := bstep (se 1 (by rfl) ⟨2451752, by rfl⟩ : syracuseStep 3269003 = 4903505) B4903505
theorem B2720159 : Blo 1207921 2720159 := bstep (se 1 (by rfl) ⟨2040119, by rfl⟩ : syracuseStep 2720159 = 4080239) B4080239
theorem B45310369 : Blo 1207921 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B16548461 : Blo 1207921 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B11928509 : Blo 1207921 11928509 := bstep (se 3 (by rfl) ⟨2236595, by rfl⟩ : syracuseStep 11928509 = 4473191) B4473191
theorem B4080779 : Blo 1207921 4080779 := bstep (se 1 (by rfl) ⟨3060584, by rfl⟩ : syracuseStep 4080779 = 6121169) B6121169
theorem B5514475 : Blo 1207921 5514475 := bstep (se 1 (by rfl) ⟨4135856, by rfl⟩ : syracuseStep 5514475 = 8271713) B8271713
theorem B117581321 : Blo 1207921 117581321 := bstep (se 2 (by rfl) ⟨44092995, by rfl⟩ : syracuseStep 117581321 = 88185991) B88185991
theorem B17434217 : Blo 1207921 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B4589723 : Blo 1207921 4589723 := bstep (se 1 (by rfl) ⟨3442292, by rfl⟩ : syracuseStep 4589723 = 6884585) B6884585
theorem B49629455 : Blo 1207921 49629455 := bstep (se 1 (by rfl) ⟨37222091, by rfl⟩ : syracuseStep 49629455 = 74444183) B74444183
theorem B8710537 : Blo 1207921 8710537 := bstep (se 2 (by rfl) ⟨3266451, by rfl⟩ : syracuseStep 8710537 = 6532903) B6532903
theorem B2124431 : Blo 1207921 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B4590391 : Blo 1207921 4590391 := bstep (se 1 (by rfl) ⟨3442793, by rfl⟩ : syracuseStep 4590391 = 6885587) B6885587
theorem B1813499 : Blo 1207921 1813499 := bstep (se 1 (by rfl) ⟨1360124, by rfl⟩ : syracuseStep 1813499 = 2720249) B2720249
theorem B1813739 : Blo 1207921 1813739 := bstep (se 1 (by rfl) ⟨1360304, by rfl⟩ : syracuseStep 1813739 = 2720609) B2720609
theorem B5164327 : Blo 1207921 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B3058985 : Blo 1207921 3058985 := bstep (se 2 (by rfl) ⟨1147119, by rfl⟩ : syracuseStep 3058985 = 2294239) B2294239
theorem B264473909 : Blo 1207921 264473909 := bstep (se 5 (by rfl) ⟨12397214, by rfl⟩ : syracuseStep 264473909 = 24794429) B24794429
theorem B5164499 : Blo 1207921 5164499 := bstep (se 1 (by rfl) ⟨3873374, by rfl⟩ : syracuseStep 5164499 = 7746749) B7746749
theorem B26136107 : Blo 1207921 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B26504795 : Blo 1207921 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B1208015 : Blo 1207921 1208015 := bstep (se 1 (by rfl) ⟨906011, by rfl⟩ : syracuseStep 1208015 = 1812023) B1812023
theorem B2903975 : Blo 1207921 2903975 := bstep (se 1 (by rfl) ⟨2177981, by rfl⟩ : syracuseStep 2903975 = 4355963) B4355963
theorem B1208255 : Blo 1207921 1208255 := bstep (se 1 (by rfl) ⟨906191, by rfl⟩ : syracuseStep 1208255 = 1812383) B1812383
theorem B4591835 : Blo 1207921 4591835 := bstep (se 1 (by rfl) ⟨3443876, by rfl⟩ : syracuseStep 4591835 = 6887753) B6887753
theorem B1208543 : Blo 1207921 1208543 := bstep (se 1 (by rfl) ⟨906407, by rfl⟩ : syracuseStep 1208543 = 1812815) B1812815
theorem B31838507 : Blo 1207921 31838507 := bstep (se 1 (by rfl) ⟨23878880, by rfl⟩ : syracuseStep 31838507 = 47757761) B47757761
theorem B1208831 : Blo 1207921 1208831 := bstep (se 1 (by rfl) ⟨906623, by rfl⟩ : syracuseStep 1208831 = 1813247) B1813247
theorem B3060251 : Blo 1207921 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B5805179 : Blo 1207921 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B88242047 : Blo 1207921 88242047 := bstep (se 1 (by rfl) ⟨66181535, by rfl⟩ : syracuseStep 88242047 = 132363071) B132363071
theorem B10606663 : Blo 1207921 10606663 := bstep (se 1 (by rfl) ⟨7954997, by rfl⟩ : syracuseStep 10606663 = 15909995) B15909995
theorem B1530191 : Blo 1207921 1530191 := bstep (se 1 (by rfl) ⟨1147643, by rfl⟩ : syracuseStep 1530191 = 2295287) B2295287
theorem B2718089 : Blo 1207921 2718089 := bstep (se 2 (by rfl) ⟨1019283, by rfl⟩ : syracuseStep 2718089 = 2038567) B2038567
theorem B26843653 : Blo 1207921 26843653 := bstep (se 4 (by rfl) ⟨2516592, by rfl⟩ : syracuseStep 26843653 = 5033185) B5033185
theorem B4135583 : Blo 1207921 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B11770571 : Blo 1207921 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B2178407 : Blo 1207921 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B2719151 : Blo 1207921 2719151 := bstep (se 1 (by rfl) ⟨2039363, by rfl⟩ : syracuseStep 2719151 = 4078727) B4078727
theorem B2719259 : Blo 1207921 2719259 := bstep (se 1 (by rfl) ⟨2039444, by rfl⟩ : syracuseStep 2719259 = 4078889) B4078889
theorem B1359391 : Blo 1207921 1359391 := bstep (se 1 (by rfl) ⟨1019543, by rfl⟩ : syracuseStep 1359391 = 2039087) B2039087
theorem B1359679 : Blo 1207921 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B8716187 : Blo 1207921 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B6881213 : Blo 1207921 6881213 := bstep (se 3 (by rfl) ⟨1290227, by rfl⟩ : syracuseStep 6881213 = 2580455) B2580455
theorem B8708087 : Blo 1207921 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B4079699 : Blo 1207921 4079699 := bstep (se 1 (by rfl) ⟨3059774, by rfl⟩ : syracuseStep 4079699 = 6119549) B6119549
theorem B21225671 : Blo 1207921 21225671 := bstep (se 1 (by rfl) ⟨15919253, by rfl⟩ : syracuseStep 21225671 = 31838507) B31838507
theorem B2294057 : Blo 1207921 2294057 := bstep (se 2 (by rfl) ⟨860271, by rfl⟩ : syracuseStep 2294057 = 1720543) B1720543
theorem B2040167 : Blo 1207921 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B35791537 : Blo 1207921 35791537 := bstep (se 2 (by rfl) ⟨13421826, by rfl⟩ : syracuseStep 35791537 = 26843653) B26843653
theorem B2720519 : Blo 1207921 2720519 := bstep (se 1 (by rfl) ⟨2040389, by rfl⟩ : syracuseStep 2720519 = 4080779) B4080779
theorem B4080509 : Blo 1207921 4080509 := bstep (se 3 (by rfl) ⟨765095, by rfl⟩ : syracuseStep 4080509 = 1530191) B1530191
theorem B8717341 : Blo 1207921 8717341 := bstep (se 3 (by rfl) ⟨1634501, by rfl⟩ : syracuseStep 8717341 = 3269003) B3269003
theorem B6120521 : Blo 1207921 6120521 := bstep (se 2 (by rfl) ⟨2295195, by rfl⟩ : syracuseStep 6120521 = 4590391) B4590391
theorem B58828031 : Blo 1207921 58828031 := bstep (se 1 (by rfl) ⟨44121023, by rfl⟩ : syracuseStep 58828031 = 88242047) B88242047
theorem B1812059 : Blo 1207921 1812059 := bstep (se 1 (by rfl) ⟨1359044, by rfl⟩ : syracuseStep 1812059 = 2718089) B2718089
theorem B46491245 : Blo 1207921 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B11028221 : Blo 1207921 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B1812521 : Blo 1207921 1812521 := bstep (se 2 (by rfl) ⟨679695, by rfl⟩ : syracuseStep 1812521 = 1359391) B1359391
theorem B1452271 : Blo 1207921 1452271 := bstep (se 1 (by rfl) ⟨1089203, by rfl⟩ : syracuseStep 1452271 = 2178407) B2178407
theorem B1812767 : Blo 1207921 1812767 := bstep (se 1 (by rfl) ⟨1359575, by rfl⟩ : syracuseStep 1812767 = 2719151) B2719151
theorem B3442999 : Blo 1207921 3442999 := bstep (se 1 (by rfl) ⟨2582249, by rfl⟩ : syracuseStep 3442999 = 5164499) B5164499
theorem B1812839 : Blo 1207921 1812839 := bstep (se 1 (by rfl) ⟨1359629, by rfl⟩ : syracuseStep 1812839 = 2719259) B2719259
theorem B1812905 : Blo 1207921 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B5810791 : Blo 1207921 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B1935983 : Blo 1207921 1935983 := bstep (se 1 (by rfl) ⟨1451987, by rfl⟩ : syracuseStep 1935983 = 2903975) B2903975
theorem B1813211 : Blo 1207921 1813211 := bstep (se 1 (by rfl) ⟨1359908, by rfl⟩ : syracuseStep 1813211 = 2719817) B2719817
theorem B14142217 : Blo 1207921 14142217 := bstep (se 2 (by rfl) ⟨5303331, by rfl⟩ : syracuseStep 14142217 = 10606663) B10606663
theorem B3582887 : Blo 1207921 3582887 := bstep (se 1 (by rfl) ⟨2687165, by rfl⟩ : syracuseStep 3582887 = 5374331) B5374331
theorem B1813439 : Blo 1207921 1813439 := bstep (se 1 (by rfl) ⟨1360079, by rfl⟩ : syracuseStep 1813439 = 2720159) B2720159
theorem B3058793 : Blo 1207921 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B3870119 : Blo 1207921 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B3059815 : Blo 1207921 3059815 := bstep (se 1 (by rfl) ⟨2294861, by rfl⟩ : syracuseStep 3059815 = 4589723) B4589723
theorem B7352633 : Blo 1207921 7352633 := bstep (se 2 (by rfl) ⟨2757237, by rfl⟩ : syracuseStep 7352633 = 5514475) B5514475
theorem B6885769 : Blo 1207921 6885769 := bstep (se 2 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 6885769 = 5164327) B5164327
theorem B1208999 : Blo 1207921 1208999 := bstep (se 1 (by rfl) ⟨906749, by rfl⟩ : syracuseStep 1208999 = 1813499) B1813499
theorem B1209159 : Blo 1207921 1209159 := bstep (se 1 (by rfl) ⟨906869, by rfl⟩ : syracuseStep 1209159 = 1813739) B1813739
theorem B23221565 : Blo 1207921 23221565 := bstep (se 3 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 23221565 = 8708087) B8708087
theorem B3061223 : Blo 1207921 3061223 := bstep (se 1 (by rfl) ⟨2295917, by rfl⟩ : syracuseStep 3061223 = 4591835) B4591835
theorem B19600987 : Blo 1207921 19600987 := bstep (se 1 (by rfl) ⟨14700740, by rfl⟩ : syracuseStep 19600987 = 29401481) B29401481
theorem B11032307 : Blo 1207921 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B11614049 : Blo 1207921 11614049 := bstep (se 2 (by rfl) ⟨4355268, by rfl⟩ : syracuseStep 11614049 = 8710537) B8710537
theorem B60413825 : Blo 1207921 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B7952339 : Blo 1207921 7952339 := bstep (se 1 (by rfl) ⟨5964254, by rfl⟩ : syracuseStep 7952339 = 11928509) B11928509
theorem B78387547 : Blo 1207921 78387547 := bstep (se 1 (by rfl) ⟨58790660, by rfl⟩ : syracuseStep 78387547 = 117581321) B117581321
theorem B33086303 : Blo 1207921 33086303 := bstep (se 1 (by rfl) ⟨24814727, by rfl⟩ : syracuseStep 33086303 = 49629455) B49629455
theorem B1416287 : Blo 1207921 1416287 := bstep (se 1 (by rfl) ⟨1062215, by rfl⟩ : syracuseStep 1416287 = 2124431) B2124431
theorem B7847047 : Blo 1207921 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B2039323 : Blo 1207921 2039323 := bstep (se 1 (by rfl) ⟨1529492, by rfl⟩ : syracuseStep 2039323 = 3058985) B3058985
theorem B176315939 : Blo 1207921 176315939 := bstep (se 1 (by rfl) ⟨132236954, by rfl⟩ : syracuseStep 176315939 = 264473909) B264473909
theorem B17424071 : Blo 1207921 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B17669863 : Blo 1207921 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B4587475 : Blo 1207921 4587475 := bstep (se 1 (by rfl) ⟨3440606, by rfl⟩ : syracuseStep 4587475 = 6881213) B6881213
theorem B2719799 : Blo 1207921 2719799 := bstep (se 1 (by rfl) ⟨2039849, by rfl⟩ : syracuseStep 2719799 = 4079699) B4079699
theorem B4079753 : Blo 1207921 4079753 := bstep (se 2 (by rfl) ⟨1529907, by rfl⟩ : syracuseStep 4079753 = 3059815) B3059815
theorem B1360111 : Blo 1207921 1360111 := bstep (se 1 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 1360111 = 2040167) B2040167
theorem B3776765 : Blo 1207921 3776765 := bstep (se 3 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 3776765 = 1416287) B1416287
theorem B2720339 : Blo 1207921 2720339 := bstep (se 1 (by rfl) ⟨2040254, by rfl⟩ : syracuseStep 2720339 = 4080509) B4080509
theorem B4080347 : Blo 1207921 4080347 := bstep (se 1 (by rfl) ⟨3060260, by rfl⟩ : syracuseStep 4080347 = 6120521) B6120521
theorem B2040815 : Blo 1207921 2040815 := bstep (se 1 (by rfl) ⟨1530611, by rfl⟩ : syracuseStep 2040815 = 3061223) B3061223
theorem B7742699 : Blo 1207921 7742699 := bstep (se 1 (by rfl) ⟨5807024, by rfl⟩ : syracuseStep 7742699 = 11614049) B11614049
theorem B5301559 : Blo 1207921 5301559 := bstep (se 1 (by rfl) ⟨3976169, by rfl⟩ : syracuseStep 5301559 = 7952339) B7952339
theorem B10462729 : Blo 1207921 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B26134649 : Blo 1207921 26134649 := bstep (se 2 (by rfl) ⟨9800493, by rfl⟩ : syracuseStep 26134649 = 19600987) B19600987
theorem B9554365 : Blo 1207921 9554365 := bstep (se 3 (by rfl) ⟨1791443, by rfl⟩ : syracuseStep 9554365 = 3582887) B3582887
theorem B14150447 : Blo 1207921 14150447 := bstep (se 1 (by rfl) ⟨10612835, by rfl⟩ : syracuseStep 14150447 = 21225671) B21225671
theorem B4901755 : Blo 1207921 4901755 := bstep (se 1 (by rfl) ⟨3676316, by rfl⟩ : syracuseStep 4901755 = 7352633) B7352633
theorem B1936361 : Blo 1207921 1936361 := bstep (se 2 (by rfl) ⟨726135, by rfl⟩ : syracuseStep 1936361 = 1452271) B1452271
theorem B4590665 : Blo 1207921 4590665 := bstep (se 2 (by rfl) ⟨1721499, by rfl⟩ : syracuseStep 4590665 = 3442999) B3442999
theorem B104516729 : Blo 1207921 104516729 := bstep (se 2 (by rfl) ⟨39193773, by rfl⟩ : syracuseStep 104516729 = 78387547) B78387547
theorem B1813679 : Blo 1207921 1813679 := bstep (se 1 (by rfl) ⟨1360259, by rfl⟩ : syracuseStep 1813679 = 2720519) B2720519
theorem B39218687 : Blo 1207921 39218687 := bstep (se 1 (by rfl) ⟨29414015, by rfl⟩ : syracuseStep 39218687 = 58828031) B58828031
theorem B47722049 : Blo 1207921 47722049 := bstep (se 2 (by rfl) ⟨17895768, by rfl⟩ : syracuseStep 47722049 = 35791537) B35791537
theorem B1208039 : Blo 1207921 1208039 := bstep (se 1 (by rfl) ⟨906029, by rfl⟩ : syracuseStep 1208039 = 1812059) B1812059
theorem B30994163 : Blo 1207921 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B7352147 : Blo 1207921 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B40275883 : Blo 1207921 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B1208347 : Blo 1207921 1208347 := bstep (se 1 (by rfl) ⟨906260, by rfl⟩ : syracuseStep 1208347 = 1812521) B1812521
theorem B1208511 : Blo 1207921 1208511 := bstep (se 1 (by rfl) ⟨906383, by rfl⟩ : syracuseStep 1208511 = 1812767) B1812767
theorem B1208559 : Blo 1207921 1208559 := bstep (se 1 (by rfl) ⟨906419, by rfl⟩ : syracuseStep 1208559 = 1812839) B1812839
theorem B1208603 : Blo 1207921 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B1290655 : Blo 1207921 1290655 := bstep (se 1 (by rfl) ⟨967991, by rfl⟩ : syracuseStep 1290655 = 1935983) B1935983
theorem B1208807 : Blo 1207921 1208807 := bstep (se 1 (by rfl) ⟨906605, by rfl⟩ : syracuseStep 1208807 = 1813211) B1813211
theorem B22057535 : Blo 1207921 22057535 := bstep (se 1 (by rfl) ⟨16543151, by rfl⟩ : syracuseStep 22057535 = 33086303) B33086303
theorem B1208959 : Blo 1207921 1208959 := bstep (se 1 (by rfl) ⟨906719, by rfl⟩ : syracuseStep 1208959 = 1813439) B1813439
theorem B117543959 : Blo 1207921 117543959 := bstep (se 1 (by rfl) ⟨88157969, by rfl⟩ : syracuseStep 117543959 = 176315939) B176315939
theorem B6116633 : Blo 1207921 6116633 := bstep (se 2 (by rfl) ⟨2293737, by rfl⟩ : syracuseStep 6116633 = 4587475) B4587475
theorem B1529371 : Blo 1207921 1529371 := bstep (se 1 (by rfl) ⟨1147028, by rfl⟩ : syracuseStep 1529371 = 2294057) B2294057
theorem B9181025 : Blo 1207921 9181025 := bstep (se 2 (by rfl) ⟨3442884, by rfl⟩ : syracuseStep 9181025 = 6885769) B6885769
theorem B7747721 : Blo 1207921 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B15481043 : Blo 1207921 15481043 := bstep (se 1 (by rfl) ⟨11610782, by rfl⟩ : syracuseStep 15481043 = 23221565) B23221565
theorem B18856289 : Blo 1207921 18856289 := bstep (se 2 (by rfl) ⟨7071108, by rfl⟩ : syracuseStep 18856289 = 14142217) B14142217
theorem B10320317 : Blo 1207921 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B7354871 : Blo 1207921 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B11623121 : Blo 1207921 11623121 := bstep (se 2 (by rfl) ⟨4358670, by rfl⟩ : syracuseStep 11623121 = 8717341) B8717341
theorem B2719097 : Blo 1207921 2719097 := bstep (se 2 (by rfl) ⟨1019661, by rfl⟩ : syracuseStep 2719097 = 2039323) B2039323
theorem B2039195 : Blo 1207921 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B23559817 : Blo 1207921 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B11616047 : Blo 1207921 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B2719835 : Blo 1207921 2719835 := bstep (se 1 (by rfl) ⟨2039876, by rfl⟩ : syracuseStep 2719835 = 4079753) B4079753
theorem B14705023 : Blo 1207921 14705023 := bstep (se 1 (by rfl) ⟨11028767, by rfl⟩ : syracuseStep 14705023 = 22057535) B22057535
theorem B2720231 : Blo 1207921 2720231 := bstep (se 1 (by rfl) ⟨2040173, by rfl⟩ : syracuseStep 2720231 = 4080347) B4080347
theorem B1720873 : Blo 1207921 1720873 := bstep (se 2 (by rfl) ⟨645327, by rfl⟩ : syracuseStep 1720873 = 1290655) B1290655
theorem B12739153 : Blo 1207921 12739153 := bstep (se 2 (by rfl) ⟨4777182, by rfl⟩ : syracuseStep 12739153 = 9554365) B9554365
theorem B1360543 : Blo 1207921 1360543 := bstep (se 1 (by rfl) ⟨1020407, by rfl⟩ : syracuseStep 1360543 = 2040815) B2040815
theorem B5161799 : Blo 1207921 5161799 := bstep (se 1 (by rfl) ⟨3871349, by rfl⟩ : syracuseStep 5161799 = 7742699) B7742699
theorem B6120683 : Blo 1207921 6120683 := bstep (se 1 (by rfl) ⟨4590512, by rfl⟩ : syracuseStep 6120683 = 9181025) B9181025
theorem B1812731 : Blo 1207921 1812731 := bstep (se 1 (by rfl) ⟨1359548, by rfl⟩ : syracuseStep 1812731 = 2719097) B2719097
theorem B20662775 : Blo 1207921 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B7744031 : Blo 1207921 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B4901431 : Blo 1207921 4901431 := bstep (se 1 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 4901431 = 7352147) B7352147
theorem B53701177 : Blo 1207921 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B1813199 : Blo 1207921 1813199 := bstep (se 1 (by rfl) ⟨1359899, by rfl⟩ : syracuseStep 1813199 = 2719799) B2719799
theorem B1813481 : Blo 1207921 1813481 := bstep (se 2 (by rfl) ⟨680055, by rfl⟩ : syracuseStep 1813481 = 1360111) B1360111
theorem B1813559 : Blo 1207921 1813559 := bstep (se 1 (by rfl) ⟨1360169, by rfl⟩ : syracuseStep 1813559 = 2720339) B2720339
theorem B10071373 : Blo 1207921 10071373 := bstep (se 3 (by rfl) ⟨1888382, by rfl⟩ : syracuseStep 10071373 = 3776765) B3776765
theorem B5165147 : Blo 1207921 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B12570859 : Blo 1207921 12570859 := bstep (se 1 (by rfl) ⟨9428144, by rfl⟩ : syracuseStep 12570859 = 18856289) B18856289
theorem B4903247 : Blo 1207921 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B9433631 : Blo 1207921 9433631 := bstep (se 1 (by rfl) ⟨7075223, by rfl⟩ : syracuseStep 9433631 = 14150447) B14150447
theorem B1290907 : Blo 1207921 1290907 := bstep (se 1 (by rfl) ⟨968180, by rfl⟩ : syracuseStep 1290907 = 1936361) B1936361
theorem B3060443 : Blo 1207921 3060443 := bstep (se 1 (by rfl) ⟨2295332, by rfl⟩ : syracuseStep 3060443 = 4590665) B4590665
theorem B69677819 : Blo 1207921 69677819 := bstep (se 1 (by rfl) ⟨52258364, by rfl⟩ : syracuseStep 69677819 = 104516729) B104516729
theorem B1209119 : Blo 1207921 1209119 := bstep (se 1 (by rfl) ⟨906839, by rfl⟩ : syracuseStep 1209119 = 1813679) B1813679
theorem B31413089 : Blo 1207921 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B26145791 : Blo 1207921 26145791 := bstep (se 1 (by rfl) ⟨19609343, by rfl⟩ : syracuseStep 26145791 = 39218687) B39218687
theorem B31814699 : Blo 1207921 31814699 := bstep (se 1 (by rfl) ⟨23861024, by rfl⟩ : syracuseStep 31814699 = 47722049) B47722049
theorem B78362639 : Blo 1207921 78362639 := bstep (se 1 (by rfl) ⟨58771979, by rfl⟩ : syracuseStep 78362639 = 117543959) B117543959
theorem B4077755 : Blo 1207921 4077755 := bstep (se 1 (by rfl) ⟨3058316, by rfl⟩ : syracuseStep 4077755 = 6116633) B6116633
theorem B6535673 : Blo 1207921 6535673 := bstep (se 2 (by rfl) ⟨2450877, by rfl⟩ : syracuseStep 6535673 = 4901755) B4901755
theorem B17423099 : Blo 1207921 17423099 := bstep (se 1 (by rfl) ⟨13067324, by rfl⟩ : syracuseStep 17423099 = 26134649) B26134649
theorem B10320695 : Blo 1207921 10320695 := bstep (se 1 (by rfl) ⟨7740521, by rfl⟩ : syracuseStep 10320695 = 15481043) B15481043
theorem B6880211 : Blo 1207921 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B7068745 : Blo 1207921 7068745 := bstep (se 2 (by rfl) ⟨2650779, by rfl⟩ : syracuseStep 7068745 = 5301559) B5301559
theorem B7748747 : Blo 1207921 7748747 := bstep (se 1 (by rfl) ⟨5811560, by rfl⟩ : syracuseStep 7748747 = 11623121) B11623121
theorem B13950305 : Blo 1207921 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B2039161 : Blo 1207921 2039161 := bstep (se 2 (by rfl) ⟨764685, by rfl⟩ : syracuseStep 2039161 = 1529371) B1529371
theorem B1359463 : Blo 1207921 1359463 := bstep (se 1 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 1359463 = 2039195) B2039195
theorem B3268831 : Blo 1207921 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B2040295 : Blo 1207921 2040295 := bstep (se 1 (by rfl) ⟨1530221, by rfl⟩ : syracuseStep 2040295 = 3060443) B3060443
theorem B3441199 : Blo 1207921 3441199 := bstep (se 1 (by rfl) ⟨2580899, by rfl⟩ : syracuseStep 3441199 = 5161799) B5161799
theorem B2294497 : Blo 1207921 2294497 := bstep (se 2 (by rfl) ⟨860436, by rfl⟩ : syracuseStep 2294497 = 1720873) B1720873
theorem B4080455 : Blo 1207921 4080455 := bstep (se 1 (by rfl) ⟨3060341, by rfl⟩ : syracuseStep 4080455 = 6120683) B6120683
theorem B67044581 : Blo 1207921 67044581 := bstep (se 4 (by rfl) ⟨6285429, by rfl⟩ : syracuseStep 67044581 = 12570859) B12570859
theorem B52241759 : Blo 1207921 52241759 := bstep (se 1 (by rfl) ⟨39181319, by rfl⟩ : syracuseStep 52241759 = 78362639) B78362639
theorem B5162687 : Blo 1207921 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B13428497 : Blo 1207921 13428497 := bstep (se 2 (by rfl) ⟨5035686, by rfl⟩ : syracuseStep 13428497 = 10071373) B10071373
theorem B1812617 : Blo 1207921 1812617 := bstep (se 2 (by rfl) ⟨679731, by rfl⟩ : syracuseStep 1812617 = 1359463) B1359463
theorem B9300203 : Blo 1207921 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B1813223 : Blo 1207921 1813223 := bstep (se 1 (by rfl) ⟨1359917, by rfl⟩ : syracuseStep 1813223 = 2719835) B2719835
theorem B13773725 : Blo 1207921 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B1813487 : Blo 1207921 1813487 := bstep (se 1 (by rfl) ⟨1360115, by rfl⟩ : syracuseStep 1813487 = 2720231) B2720231
theorem B339356789 : Blo 1207921 339356789 := bstep (se 5 (by rfl) ⟨15907349, by rfl⟩ : syracuseStep 339356789 = 31814699) B31814699
theorem B46451879 : Blo 1207921 46451879 := bstep (se 1 (by rfl) ⟨34838909, by rfl⟩ : syracuseStep 46451879 = 69677819) B69677819
theorem B19606697 : Blo 1207921 19606697 := bstep (se 2 (by rfl) ⟨7352511, by rfl⟩ : syracuseStep 19606697 = 14705023) B14705023
theorem B20942059 : Blo 1207921 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B71601569 : Blo 1207921 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B16985537 : Blo 1207921 16985537 := bstep (se 2 (by rfl) ⟨6369576, by rfl⟩ : syracuseStep 16985537 = 12739153) B12739153
theorem B6884837 : Blo 1207921 6884837 := bstep (se 4 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 6884837 = 1290907) B1290907
theorem B1814057 : Blo 1207921 1814057 := bstep (se 2 (by rfl) ⟨680271, by rfl⟩ : syracuseStep 1814057 = 1360543) B1360543
theorem B9424993 : Blo 1207921 9424993 := bstep (se 2 (by rfl) ⟨3534372, by rfl⟩ : syracuseStep 9424993 = 7068745) B7068745
theorem B1208487 : Blo 1207921 1208487 := bstep (se 1 (by rfl) ⟨906365, by rfl⟩ : syracuseStep 1208487 = 1812731) B1812731
theorem B13775183 : Blo 1207921 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B1208799 : Blo 1207921 1208799 := bstep (se 1 (by rfl) ⟨906599, by rfl⟩ : syracuseStep 1208799 = 1813199) B1813199
theorem B1208987 : Blo 1207921 1208987 := bstep (se 1 (by rfl) ⟨906740, by rfl⟩ : syracuseStep 1208987 = 1813481) B1813481
theorem B1209039 : Blo 1207921 1209039 := bstep (se 1 (by rfl) ⟨906779, by rfl⟩ : syracuseStep 1209039 = 1813559) B1813559
theorem B5165831 : Blo 1207921 5165831 := bstep (se 1 (by rfl) ⟨3874373, by rfl⟩ : syracuseStep 5165831 = 7748747) B7748747
theorem B17430527 : Blo 1207921 17430527 := bstep (se 1 (by rfl) ⟨13072895, by rfl⟩ : syracuseStep 17430527 = 26145791) B26145791
theorem B6535241 : Blo 1207921 6535241 := bstep (se 2 (by rfl) ⟨2450715, by rfl⟩ : syracuseStep 6535241 = 4901431) B4901431
theorem B25156349 : Blo 1207921 25156349 := bstep (se 3 (by rfl) ⟨4716815, by rfl⟩ : syracuseStep 25156349 = 9433631) B9433631
theorem B2718503 : Blo 1207921 2718503 := bstep (se 1 (by rfl) ⟨2038877, by rfl⟩ : syracuseStep 2718503 = 4077755) B4077755
theorem B4357115 : Blo 1207921 4357115 := bstep (se 1 (by rfl) ⟨3267836, by rfl⟩ : syracuseStep 4357115 = 6535673) B6535673
theorem B2718881 : Blo 1207921 2718881 := bstep (se 2 (by rfl) ⟨1019580, by rfl⟩ : syracuseStep 2718881 = 2039161) B2039161
theorem B11615399 : Blo 1207921 11615399 := bstep (se 1 (by rfl) ⟨8711549, by rfl⟩ : syracuseStep 11615399 = 17423099) B17423099
theorem B6880463 : Blo 1207921 6880463 := bstep (se 1 (by rfl) ⟨5160347, by rfl⟩ : syracuseStep 6880463 = 10320695) B10320695
theorem B4586807 : Blo 1207921 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B12566657 : Blo 1207921 12566657 := bstep (se 2 (by rfl) ⟨4712496, by rfl⟩ : syracuseStep 12566657 = 9424993) B9424993
theorem B9183455 : Blo 1207921 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B4358441 : Blo 1207921 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2720303 : Blo 1207921 2720303 := bstep (se 1 (by rfl) ⟨2040227, by rfl⟩ : syracuseStep 2720303 = 4080455) B4080455
theorem B2720393 : Blo 1207921 2720393 := bstep (se 2 (by rfl) ⟨1020147, by rfl⟩ : syracuseStep 2720393 = 2040295) B2040295
theorem B4588265 : Blo 1207921 4588265 := bstep (se 2 (by rfl) ⟨1720599, by rfl⟩ : syracuseStep 4588265 = 3441199) B3441199
theorem B44696387 : Blo 1207921 44696387 := bstep (se 1 (by rfl) ⟨33522290, by rfl⟩ : syracuseStep 44696387 = 67044581) B67044581
theorem B3441791 : Blo 1207921 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B16770899 : Blo 1207921 16770899 := bstep (se 1 (by rfl) ⟨12578174, by rfl⟩ : syracuseStep 16770899 = 25156349) B25156349
theorem B1812335 : Blo 1207921 1812335 := bstep (se 1 (by rfl) ⟨1359251, by rfl⟩ : syracuseStep 1812335 = 2718503) B2718503
theorem B1812587 : Blo 1207921 1812587 := bstep (se 1 (by rfl) ⟨1359440, by rfl⟩ : syracuseStep 1812587 = 2718881) B2718881
theorem B30967919 : Blo 1207921 30967919 := bstep (se 1 (by rfl) ⟨23225939, by rfl⟩ : syracuseStep 30967919 = 46451879) B46451879
theorem B7743599 : Blo 1207921 7743599 := bstep (se 1 (by rfl) ⟨5807699, by rfl⟩ : syracuseStep 7743599 = 11615399) B11615399
theorem B3057871 : Blo 1207921 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B11323691 : Blo 1207921 11323691 := bstep (se 1 (by rfl) ⟨8492768, by rfl⟩ : syracuseStep 11323691 = 16985537) B16985537
theorem B4589891 : Blo 1207921 4589891 := bstep (se 1 (by rfl) ⟨3442418, by rfl⟩ : syracuseStep 4589891 = 6884837) B6884837
theorem B3443887 : Blo 1207921 3443887 := bstep (se 1 (by rfl) ⟨2582915, by rfl⟩ : syracuseStep 3443887 = 5165831) B5165831
theorem B34827839 : Blo 1207921 34827839 := bstep (se 1 (by rfl) ⟨26120879, by rfl⟩ : syracuseStep 34827839 = 52241759) B52241759
theorem B3059329 : Blo 1207921 3059329 := bstep (se 2 (by rfl) ⟨1147248, by rfl⟩ : syracuseStep 3059329 = 2294497) B2294497
theorem B11620351 : Blo 1207921 11620351 := bstep (se 1 (by rfl) ⟨8715263, by rfl⟩ : syracuseStep 11620351 = 17430527) B17430527
theorem B1208411 : Blo 1207921 1208411 := bstep (se 1 (by rfl) ⟨906308, by rfl⟩ : syracuseStep 1208411 = 1812617) B1812617
theorem B27922745 : Blo 1207921 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B1208815 : Blo 1207921 1208815 := bstep (se 1 (by rfl) ⟨906611, by rfl⟩ : syracuseStep 1208815 = 1813223) B1813223
theorem B1208991 : Blo 1207921 1208991 := bstep (se 1 (by rfl) ⟨906743, by rfl⟩ : syracuseStep 1208991 = 1813487) B1813487
theorem B2904743 : Blo 1207921 2904743 := bstep (se 1 (by rfl) ⟨2178557, by rfl⟩ : syracuseStep 2904743 = 4357115) B4357115
theorem B13071131 : Blo 1207921 13071131 := bstep (se 1 (by rfl) ⟨9803348, by rfl⟩ : syracuseStep 13071131 = 19606697) B19606697
theorem B1209371 : Blo 1207921 1209371 := bstep (se 1 (by rfl) ⟨907028, by rfl⟩ : syracuseStep 1209371 = 1814057) B1814057
theorem B8952331 : Blo 1207921 8952331 := bstep (se 1 (by rfl) ⟨6714248, by rfl⟩ : syracuseStep 8952331 = 13428497) B13428497
theorem B4356827 : Blo 1207921 4356827 := bstep (se 1 (by rfl) ⟨3267620, by rfl⟩ : syracuseStep 4356827 = 6535241) B6535241
theorem B6200135 : Blo 1207921 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B9182483 : Blo 1207921 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B226237859 : Blo 1207921 226237859 := bstep (se 1 (by rfl) ⟨169678394, by rfl⟩ : syracuseStep 226237859 = 339356789) B339356789
theorem B4586975 : Blo 1207921 4586975 := bstep (se 1 (by rfl) ⟨3440231, by rfl⟩ : syracuseStep 4586975 = 6880463) B6880463
theorem B47734379 : Blo 1207921 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B11936441 : Blo 1207921 11936441 := bstep (se 2 (by rfl) ⟨4476165, by rfl⟩ : syracuseStep 11936441 = 8952331) B8952331
theorem B20645279 : Blo 1207921 20645279 := bstep (se 1 (by rfl) ⟨15483959, by rfl⟩ : syracuseStep 20645279 = 30967919) B30967919
theorem B5162399 : Blo 1207921 5162399 := bstep (se 1 (by rfl) ⟨3871799, by rfl⟩ : syracuseStep 5162399 = 7743599) B7743599
theorem B6121655 : Blo 1207921 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B150825239 : Blo 1207921 150825239 := bstep (se 1 (by rfl) ⟨113118929, by rfl⟩ : syracuseStep 150825239 = 226237859) B226237859
theorem B3057983 : Blo 1207921 3057983 := bstep (se 1 (by rfl) ⟨2293487, by rfl⟩ : syracuseStep 3057983 = 4586975) B4586975
theorem B23218559 : Blo 1207921 23218559 := bstep (se 1 (by rfl) ⟨17413919, by rfl⟩ : syracuseStep 23218559 = 34827839) B34827839
theorem B15493801 : Blo 1207921 15493801 := bstep (se 2 (by rfl) ⟨5810175, by rfl⟩ : syracuseStep 15493801 = 11620351) B11620351
theorem B6122303 : Blo 1207921 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B9178109 : Blo 1207921 9178109 := bstep (se 3 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 9178109 = 3441791) B3441791
theorem B1813535 : Blo 1207921 1813535 := bstep (se 1 (by rfl) ⟨1360151, by rfl⟩ : syracuseStep 1813535 = 2720303) B2720303
theorem B1813595 : Blo 1207921 1813595 := bstep (se 1 (by rfl) ⟨1360196, by rfl⟩ : syracuseStep 1813595 = 2720393) B2720393
theorem B1936495 : Blo 1207921 1936495 := bstep (se 1 (by rfl) ⟨1452371, by rfl⟩ : syracuseStep 1936495 = 2904743) B2904743
theorem B3058843 : Blo 1207921 3058843 := bstep (se 1 (by rfl) ⟨2294132, by rfl⟩ : syracuseStep 3058843 = 4588265) B4588265
theorem B29797591 : Blo 1207921 29797591 := bstep (se 1 (by rfl) ⟨22348193, by rfl⟩ : syracuseStep 29797591 = 44696387) B44696387
theorem B74460653 : Blo 1207921 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B1208223 : Blo 1207921 1208223 := bstep (se 1 (by rfl) ⟨906167, by rfl⟩ : syracuseStep 1208223 = 1812335) B1812335
theorem B1208391 : Blo 1207921 1208391 := bstep (se 1 (by rfl) ⟨906293, by rfl⟩ : syracuseStep 1208391 = 1812587) B1812587
theorem B7549127 : Blo 1207921 7549127 := bstep (se 1 (by rfl) ⟨5661845, by rfl⟩ : syracuseStep 7549127 = 11323691) B11323691
theorem B3059927 : Blo 1207921 3059927 := bstep (se 1 (by rfl) ⟨2294945, by rfl⟩ : syracuseStep 3059927 = 4589891) B4589891
theorem B4591849 : Blo 1207921 4591849 := bstep (se 2 (by rfl) ⟨1721943, by rfl⟩ : syracuseStep 4591849 = 3443887) B3443887
theorem B2904551 : Blo 1207921 2904551 := bstep (se 1 (by rfl) ⟨2178413, by rfl⟩ : syracuseStep 2904551 = 4356827) B4356827
theorem B4133423 : Blo 1207921 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B31822919 : Blo 1207921 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B8377771 : Blo 1207921 8377771 := bstep (se 1 (by rfl) ⟨6283328, by rfl⟩ : syracuseStep 8377771 = 12566657) B12566657
theorem B2905627 : Blo 1207921 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B4077161 : Blo 1207921 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B8714087 : Blo 1207921 8714087 := bstep (se 1 (by rfl) ⟨6535565, by rfl⟩ : syracuseStep 8714087 = 13071131) B13071131
theorem B11180599 : Blo 1207921 11180599 := bstep (se 1 (by rfl) ⟨8385449, by rfl⟩ : syracuseStep 11180599 = 16770899) B16770899
theorem B4079105 : Blo 1207921 4079105 := bstep (se 2 (by rfl) ⟨1529664, by rfl⟩ : syracuseStep 4079105 = 3059329) B3059329
theorem B2039951 : Blo 1207921 2039951 := bstep (se 1 (by rfl) ⟨1529963, by rfl⟩ : syracuseStep 2039951 = 3059927) B3059927
theorem B59629861 : Blo 1207921 59629861 := bstep (se 4 (by rfl) ⟨5590299, by rfl⟩ : syracuseStep 59629861 = 11180599) B11180599
theorem B13763519 : Blo 1207921 13763519 := bstep (se 1 (by rfl) ⟨10322639, by rfl⟩ : syracuseStep 13763519 = 20645279) B20645279
theorem B3441599 : Blo 1207921 3441599 := bstep (se 1 (by rfl) ⟨2581199, by rfl⟩ : syracuseStep 3441599 = 5162399) B5162399
theorem B5809391 : Blo 1207921 5809391 := bstep (se 1 (by rfl) ⟨4357043, by rfl⟩ : syracuseStep 5809391 = 8714087) B8714087
theorem B4081103 : Blo 1207921 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B2581993 : Blo 1207921 2581993 := bstep (se 2 (by rfl) ⟨968247, by rfl⟩ : syracuseStep 2581993 = 1936495) B1936495
theorem B100550159 : Blo 1207921 100550159 := bstep (se 1 (by rfl) ⟨75412619, by rfl⟩ : syracuseStep 100550159 = 150825239) B150825239
theorem B4081535 : Blo 1207921 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B5032751 : Blo 1207921 5032751 := bstep (se 1 (by rfl) ⟨3774563, by rfl⟩ : syracuseStep 5032751 = 7549127) B7549127
theorem B6122465 : Blo 1207921 6122465 := bstep (se 2 (by rfl) ⟨2295924, by rfl⟩ : syracuseStep 6122465 = 4591849) B4591849
theorem B1936367 : Blo 1207921 1936367 := bstep (se 1 (by rfl) ⟨1452275, by rfl⟩ : syracuseStep 1936367 = 2904551) B2904551
theorem B2755615 : Blo 1207921 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B15479039 : Blo 1207921 15479039 := bstep (se 1 (by rfl) ⟨11609279, by rfl⟩ : syracuseStep 15479039 = 23218559) B23218559
theorem B31830509 : Blo 1207921 31830509 := bstep (se 3 (by rfl) ⟨5968220, by rfl⟩ : syracuseStep 31830509 = 11936441) B11936441
theorem B11170361 : Blo 1207921 11170361 := bstep (se 2 (by rfl) ⟨4188885, by rfl⟩ : syracuseStep 11170361 = 8377771) B8377771
theorem B1209023 : Blo 1207921 1209023 := bstep (se 1 (by rfl) ⟨906767, by rfl⟩ : syracuseStep 1209023 = 1813535) B1813535
theorem B1209063 : Blo 1207921 1209063 := bstep (se 1 (by rfl) ⟨906797, by rfl⟩ : syracuseStep 1209063 = 1813595) B1813595
theorem B49640435 : Blo 1207921 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B21215279 : Blo 1207921 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B20658401 : Blo 1207921 20658401 := bstep (se 2 (by rfl) ⟨7746900, by rfl⟩ : syracuseStep 20658401 = 15493801) B15493801
theorem B2718107 : Blo 1207921 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B4078457 : Blo 1207921 4078457 := bstep (se 2 (by rfl) ⟨1529421, by rfl⟩ : syracuseStep 4078457 = 3058843) B3058843
theorem B2038655 : Blo 1207921 2038655 := bstep (se 1 (by rfl) ⟨1528991, by rfl⟩ : syracuseStep 2038655 = 3057983) B3057983
theorem B39730121 : Blo 1207921 39730121 := bstep (se 2 (by rfl) ⟨14898795, by rfl⟩ : syracuseStep 39730121 = 29797591) B29797591
theorem B6118739 : Blo 1207921 6118739 := bstep (se 1 (by rfl) ⟨4589054, by rfl⟩ : syracuseStep 6118739 = 9178109) B9178109
theorem B3874169 : Blo 1207921 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B2719403 : Blo 1207921 2719403 := bstep (se 1 (by rfl) ⟨2039552, by rfl⟩ : syracuseStep 2719403 = 4079105) B4079105
theorem B1359967 : Blo 1207921 1359967 := bstep (se 1 (by rfl) ⟨1019975, by rfl⟩ : syracuseStep 1359967 = 2039951) B2039951
theorem B7446907 : Blo 1207921 7446907 := bstep (se 1 (by rfl) ⟨5585180, by rfl⟩ : syracuseStep 7446907 = 11170361) B11170361
theorem B9175679 : Blo 1207921 9175679 := bstep (se 1 (by rfl) ⟨6881759, by rfl⟩ : syracuseStep 9175679 = 13763519) B13763519
theorem B2294399 : Blo 1207921 2294399 := bstep (se 1 (by rfl) ⟨1720799, by rfl⟩ : syracuseStep 2294399 = 3441599) B3441599
theorem B2720735 : Blo 1207921 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B2721023 : Blo 1207921 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B13772267 : Blo 1207921 13772267 := bstep (se 1 (by rfl) ⟨10329200, by rfl⟩ : syracuseStep 13772267 = 20658401) B20658401
theorem B1812071 : Blo 1207921 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B26486747 : Blo 1207921 26486747 := bstep (se 1 (by rfl) ⟨19865060, by rfl⟩ : syracuseStep 26486747 = 39730121) B39730121
theorem B3442657 : Blo 1207921 3442657 := bstep (se 2 (by rfl) ⟨1290996, by rfl⟩ : syracuseStep 3442657 = 2581993) B2581993
theorem B4081643 : Blo 1207921 4081643 := bstep (se 1 (by rfl) ⟨3061232, by rfl⟩ : syracuseStep 4081643 = 6122465) B6122465
theorem B13420669 : Blo 1207921 13420669 := bstep (se 3 (by rfl) ⟨2516375, by rfl⟩ : syracuseStep 13420669 = 5032751) B5032751
theorem B2582779 : Blo 1207921 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B1812935 : Blo 1207921 1812935 := bstep (se 1 (by rfl) ⟨1359701, by rfl⟩ : syracuseStep 1812935 = 2719403) B2719403
theorem B79506481 : Blo 1207921 79506481 := bstep (se 2 (by rfl) ⟨29814930, by rfl⟩ : syracuseStep 79506481 = 59629861) B59629861
theorem B84881357 : Blo 1207921 84881357 := bstep (se 3 (by rfl) ⟨15915254, by rfl⟩ : syracuseStep 84881357 = 31830509) B31830509
theorem B14143519 : Blo 1207921 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B3674153 : Blo 1207921 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B1290911 : Blo 1207921 1290911 := bstep (se 1 (by rfl) ⟨968183, by rfl⟩ : syracuseStep 1290911 = 1936367) B1936367
theorem B10319359 : Blo 1207921 10319359 := bstep (se 1 (by rfl) ⟨7739519, by rfl⟩ : syracuseStep 10319359 = 15479039) B15479039
theorem B33093623 : Blo 1207921 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B3872927 : Blo 1207921 3872927 := bstep (se 1 (by rfl) ⟨2904695, by rfl⟩ : syracuseStep 3872927 = 5809391) B5809391
theorem B67033439 : Blo 1207921 67033439 := bstep (se 1 (by rfl) ⟨50275079, by rfl⟩ : syracuseStep 67033439 = 100550159) B100550159
theorem B2718971 : Blo 1207921 2718971 := bstep (se 1 (by rfl) ⟨2039228, by rfl⟩ : syracuseStep 2718971 = 4078457) B4078457
theorem B1359103 : Blo 1207921 1359103 := bstep (se 1 (by rfl) ⟨1019327, by rfl⟩ : syracuseStep 1359103 = 2038655) B2038655
theorem B4079159 : Blo 1207921 4079159 := bstep (se 1 (by rfl) ⟨3059369, by rfl⟩ : syracuseStep 4079159 = 6118739) B6118739
theorem B2449435 : Blo 1207921 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B18858025 : Blo 1207921 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B2721095 : Blo 1207921 2721095 := bstep (se 1 (by rfl) ⟨2040821, by rfl⟩ : syracuseStep 2721095 = 4081643) B4081643
theorem B22062415 : Blo 1207921 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B2581951 : Blo 1207921 2581951 := bstep (se 1 (by rfl) ⟨1936463, by rfl⟩ : syracuseStep 2581951 = 3872927) B3872927
theorem B44688959 : Blo 1207921 44688959 := bstep (se 1 (by rfl) ⟨33516719, by rfl⟩ : syracuseStep 44688959 = 67033439) B67033439
theorem B1812137 : Blo 1207921 1812137 := bstep (se 2 (by rfl) ⟨679551, by rfl⟩ : syracuseStep 1812137 = 1359103) B1359103
theorem B3442429 : Blo 1207921 3442429 := bstep (se 3 (by rfl) ⟨645455, by rfl⟩ : syracuseStep 3442429 = 1290911) B1290911
theorem B39716837 : Blo 1207921 39716837 := bstep (se 4 (by rfl) ⟨3723453, by rfl⟩ : syracuseStep 39716837 = 7446907) B7446907
theorem B1812647 : Blo 1207921 1812647 := bstep (se 1 (by rfl) ⟨1359485, by rfl⟩ : syracuseStep 1812647 = 2718971) B2718971
theorem B4590209 : Blo 1207921 4590209 := bstep (se 2 (by rfl) ⟨1721328, by rfl⟩ : syracuseStep 4590209 = 3442657) B3442657
theorem B1813289 : Blo 1207921 1813289 := bstep (se 2 (by rfl) ⟨679983, by rfl⟩ : syracuseStep 1813289 = 1359967) B1359967
theorem B17894225 : Blo 1207921 17894225 := bstep (se 2 (by rfl) ⟨6710334, by rfl⟩ : syracuseStep 17894225 = 13420669) B13420669
theorem B3443705 : Blo 1207921 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B1813823 : Blo 1207921 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B1814015 : Blo 1207921 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B1208047 : Blo 1207921 1208047 := bstep (se 1 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 1208047 = 1812071) B1812071
theorem B17657831 : Blo 1207921 17657831 := bstep (se 1 (by rfl) ⟨13243373, by rfl⟩ : syracuseStep 17657831 = 26486747) B26486747
theorem B106008641 : Blo 1207921 106008641 := bstep (se 2 (by rfl) ⟨39753240, by rfl⟩ : syracuseStep 106008641 = 79506481) B79506481
theorem B1208623 : Blo 1207921 1208623 := bstep (se 1 (by rfl) ⟨906467, by rfl⟩ : syracuseStep 1208623 = 1812935) B1812935
theorem B13759145 : Blo 1207921 13759145 := bstep (se 2 (by rfl) ⟨5159679, by rfl⟩ : syracuseStep 13759145 = 10319359) B10319359
theorem B56587571 : Blo 1207921 56587571 := bstep (se 1 (by rfl) ⟨42440678, by rfl⟩ : syracuseStep 56587571 = 84881357) B84881357
theorem B6117119 : Blo 1207921 6117119 := bstep (se 1 (by rfl) ⟨4587839, by rfl⟩ : syracuseStep 6117119 = 9175679) B9175679
theorem B1529599 : Blo 1207921 1529599 := bstep (se 1 (by rfl) ⟨1147199, by rfl⟩ : syracuseStep 1529599 = 2294399) B2294399
theorem B9181511 : Blo 1207921 9181511 := bstep (se 1 (by rfl) ⟨6886133, by rfl⟩ : syracuseStep 9181511 = 13772267) B13772267
theorem B2719439 : Blo 1207921 2719439 := bstep (se 1 (by rfl) ⟨2039579, by rfl⟩ : syracuseStep 2719439 = 4079159) B4079159
theorem B70672427 : Blo 1207921 70672427 := bstep (se 1 (by rfl) ⟨53004320, by rfl⟩ : syracuseStep 70672427 = 106008641) B106008641
theorem B37725047 : Blo 1207921 37725047 := bstep (se 1 (by rfl) ⟨28293785, by rfl⟩ : syracuseStep 37725047 = 56587571) B56587571
theorem B26477891 : Blo 1207921 26477891 := bstep (se 1 (by rfl) ⟨19858418, by rfl⟩ : syracuseStep 26477891 = 39716837) B39716837
theorem B6121007 : Blo 1207921 6121007 := bstep (se 1 (by rfl) ⟨4590755, by rfl⟩ : syracuseStep 6121007 = 9181511) B9181511
theorem B11929483 : Blo 1207921 11929483 := bstep (se 1 (by rfl) ⟨8947112, by rfl⟩ : syracuseStep 11929483 = 17894225) B17894225
theorem B3442601 : Blo 1207921 3442601 := bstep (se 2 (by rfl) ⟨1290975, by rfl⟩ : syracuseStep 3442601 = 2581951) B2581951
theorem B2295803 : Blo 1207921 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B4589905 : Blo 1207921 4589905 := bstep (se 2 (by rfl) ⟨1721214, by rfl⟩ : syracuseStep 4589905 = 3442429) B3442429
theorem B1812959 : Blo 1207921 1812959 := bstep (se 1 (by rfl) ⟨1359719, by rfl⟩ : syracuseStep 1812959 = 2719439) B2719439
theorem B100576133 : Blo 1207921 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B1814063 : Blo 1207921 1814063 := bstep (se 1 (by rfl) ⟨1360547, by rfl⟩ : syracuseStep 1814063 = 2721095) B2721095
theorem B1208091 : Blo 1207921 1208091 := bstep (se 1 (by rfl) ⟨906068, by rfl⟩ : syracuseStep 1208091 = 1812137) B1812137
theorem B1208431 : Blo 1207921 1208431 := bstep (se 1 (by rfl) ⟨906323, by rfl⟩ : syracuseStep 1208431 = 1812647) B1812647
theorem B3060139 : Blo 1207921 3060139 := bstep (se 1 (by rfl) ⟨2295104, by rfl⟩ : syracuseStep 3060139 = 4590209) B4590209
theorem B1208859 : Blo 1207921 1208859 := bstep (se 1 (by rfl) ⟨906644, by rfl⟩ : syracuseStep 1208859 = 1813289) B1813289
theorem B1209215 : Blo 1207921 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B1209343 : Blo 1207921 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B3265913 : Blo 1207921 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B9172763 : Blo 1207921 9172763 := bstep (se 1 (by rfl) ⟨6879572, by rfl⟩ : syracuseStep 9172763 = 13759145) B13759145
theorem B29792639 : Blo 1207921 29792639 := bstep (se 1 (by rfl) ⟨22344479, by rfl⟩ : syracuseStep 29792639 = 44688959) B44688959
theorem B4078079 : Blo 1207921 4078079 := bstep (se 1 (by rfl) ⟨3058559, by rfl⟩ : syracuseStep 4078079 = 6117119) B6117119
theorem B29416553 : Blo 1207921 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B2039465 : Blo 1207921 2039465 := bstep (se 2 (by rfl) ⟨764799, by rfl⟩ : syracuseStep 2039465 = 1529599) B1529599
theorem B11771887 : Blo 1207921 11771887 := bstep (se 1 (by rfl) ⟨8828915, by rfl⟩ : syracuseStep 11771887 = 17657831) B17657831
theorem B6119873 : Blo 1207921 6119873 := bstep (se 2 (by rfl) ⟨2294952, by rfl⟩ : syracuseStep 6119873 = 4589905) B4589905
theorem B4080185 : Blo 1207921 4080185 := bstep (se 2 (by rfl) ⟨1530069, by rfl⟩ : syracuseStep 4080185 = 3060139) B3060139
theorem B25150031 : Blo 1207921 25150031 := bstep (se 1 (by rfl) ⟨18862523, by rfl⟩ : syracuseStep 25150031 = 37725047) B37725047
theorem B4080671 : Blo 1207921 4080671 := bstep (se 1 (by rfl) ⟨3060503, by rfl⟩ : syracuseStep 4080671 = 6121007) B6121007
theorem B2295067 : Blo 1207921 2295067 := bstep (se 1 (by rfl) ⟨1721300, by rfl⟩ : syracuseStep 2295067 = 3442601) B3442601
theorem B6122141 : Blo 1207921 6122141 := bstep (se 3 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 6122141 = 2295803) B2295803
theorem B47114951 : Blo 1207921 47114951 := bstep (se 1 (by rfl) ⟨35336213, by rfl⟩ : syracuseStep 47114951 = 70672427) B70672427
theorem B6115175 : Blo 1207921 6115175 := bstep (se 1 (by rfl) ⟨4586381, by rfl⟩ : syracuseStep 6115175 = 9172763) B9172763
theorem B19861759 : Blo 1207921 19861759 := bstep (se 1 (by rfl) ⟨14896319, by rfl⟩ : syracuseStep 19861759 = 29792639) B29792639
theorem B1208639 : Blo 1207921 1208639 := bstep (se 1 (by rfl) ⟨906479, by rfl⟩ : syracuseStep 1208639 = 1812959) B1812959
theorem B1209375 : Blo 1207921 1209375 := bstep (se 1 (by rfl) ⟨907031, by rfl⟩ : syracuseStep 1209375 = 1814063) B1814063
theorem B15905977 : Blo 1207921 15905977 := bstep (se 2 (by rfl) ⟨5964741, by rfl⟩ : syracuseStep 15905977 = 11929483) B11929483
theorem B17651927 : Blo 1207921 17651927 := bstep (se 1 (by rfl) ⟨13238945, by rfl⟩ : syracuseStep 17651927 = 26477891) B26477891
theorem B2177275 : Blo 1207921 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B2718719 : Blo 1207921 2718719 := bstep (se 1 (by rfl) ⟨2039039, by rfl⟩ : syracuseStep 2718719 = 4078079) B4078079
theorem B67050755 : Blo 1207921 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B19611035 : Blo 1207921 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B1359643 : Blo 1207921 1359643 := bstep (se 1 (by rfl) ⟨1019732, by rfl⟩ : syracuseStep 1359643 = 2039465) B2039465
theorem B15695849 : Blo 1207921 15695849 := bstep (se 2 (by rfl) ⟨5885943, by rfl⟩ : syracuseStep 15695849 = 11771887) B11771887
theorem B4079915 : Blo 1207921 4079915 := bstep (se 1 (by rfl) ⟨3059936, by rfl⟩ : syracuseStep 4079915 = 6119873) B6119873
theorem B2720123 : Blo 1207921 2720123 := bstep (se 1 (by rfl) ⟨2040092, by rfl⟩ : syracuseStep 2720123 = 4080185) B4080185
theorem B2720447 : Blo 1207921 2720447 := bstep (se 1 (by rfl) ⟨2040335, by rfl⟩ : syracuseStep 2720447 = 4080671) B4080671
theorem B4081427 : Blo 1207921 4081427 := bstep (se 1 (by rfl) ⟨3061070, by rfl⟩ : syracuseStep 4081427 = 6122141) B6122141
theorem B1812479 : Blo 1207921 1812479 := bstep (se 1 (by rfl) ⟨1359359, by rfl⟩ : syracuseStep 1812479 = 2718719) B2718719
theorem B1812857 : Blo 1207921 1812857 := bstep (se 2 (by rfl) ⟨679821, by rfl⟩ : syracuseStep 1812857 = 1359643) B1359643
theorem B10463899 : Blo 1207921 10463899 := bstep (se 1 (by rfl) ⟨7847924, by rfl⟩ : syracuseStep 10463899 = 15695849) B15695849
theorem B2903033 : Blo 1207921 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B84831877 : Blo 1207921 84831877 := bstep (se 4 (by rfl) ⟨7952988, by rfl⟩ : syracuseStep 84831877 = 15905977) B15905977
theorem B11767951 : Blo 1207921 11767951 := bstep (se 1 (by rfl) ⟨8825963, by rfl⟩ : syracuseStep 11767951 = 17651927) B17651927
theorem B3060089 : Blo 1207921 3060089 := bstep (se 2 (by rfl) ⟨1147533, by rfl⟩ : syracuseStep 3060089 = 2295067) B2295067
theorem B502559477 : Blo 1207921 502559477 := bstep (se 5 (by rfl) ⟨23557475, by rfl⟩ : syracuseStep 502559477 = 47114951) B47114951
theorem B44700503 : Blo 1207921 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B4076783 : Blo 1207921 4076783 := bstep (se 1 (by rfl) ⟨3057587, by rfl⟩ : syracuseStep 4076783 = 6115175) B6115175
theorem B26482345 : Blo 1207921 26482345 := bstep (se 2 (by rfl) ⟨9930879, by rfl⟩ : syracuseStep 26482345 = 19861759) B19861759
theorem B16766687 : Blo 1207921 16766687 := bstep (se 1 (by rfl) ⟨12575015, by rfl⟩ : syracuseStep 16766687 = 25150031) B25150031
theorem B13074023 : Blo 1207921 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B2719943 : Blo 1207921 2719943 := bstep (se 1 (by rfl) ⟨2039957, by rfl⟩ : syracuseStep 2719943 = 4079915) B4079915
theorem B2040059 : Blo 1207921 2040059 := bstep (se 1 (by rfl) ⟨1530044, by rfl⟩ : syracuseStep 2040059 = 3060089) B3060089
theorem B13951865 : Blo 1207921 13951865 := bstep (se 2 (by rfl) ⟨5231949, by rfl⟩ : syracuseStep 13951865 = 10463899) B10463899
theorem B2720951 : Blo 1207921 2720951 := bstep (se 1 (by rfl) ⟨2040713, by rfl⟩ : syracuseStep 2720951 = 4081427) B4081427
theorem B1935355 : Blo 1207921 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B113109169 : Blo 1207921 113109169 := bstep (se 2 (by rfl) ⟨42415938, by rfl⟩ : syracuseStep 113109169 = 84831877) B84831877
theorem B15690601 : Blo 1207921 15690601 := bstep (se 2 (by rfl) ⟨5883975, by rfl⟩ : syracuseStep 15690601 = 11767951) B11767951
theorem B1813415 : Blo 1207921 1813415 := bstep (se 1 (by rfl) ⟨1360061, by rfl⟩ : syracuseStep 1813415 = 2720123) B2720123
theorem B1813631 : Blo 1207921 1813631 := bstep (se 1 (by rfl) ⟨1360223, by rfl⟩ : syracuseStep 1813631 = 2720447) B2720447
theorem B335039651 : Blo 1207921 335039651 := bstep (se 1 (by rfl) ⟨251279738, by rfl⟩ : syracuseStep 335039651 = 502559477) B502559477
theorem B564956693 : Blo 1207921 564956693 := bstep (se 6 (by rfl) ⟨13241172, by rfl⟩ : syracuseStep 564956693 = 26482345) B26482345
theorem B1208319 : Blo 1207921 1208319 := bstep (se 1 (by rfl) ⟨906239, by rfl⟩ : syracuseStep 1208319 = 1812479) B1812479
theorem B1208571 : Blo 1207921 1208571 := bstep (se 1 (by rfl) ⟨906428, by rfl⟩ : syracuseStep 1208571 = 1812857) B1812857
theorem B2717855 : Blo 1207921 2717855 := bstep (se 1 (by rfl) ⟨2038391, by rfl⟩ : syracuseStep 2717855 = 4076783) B4076783
theorem B44711165 : Blo 1207921 44711165 := bstep (se 3 (by rfl) ⟨8383343, by rfl⟩ : syracuseStep 44711165 = 16766687) B16766687
theorem B119201341 : Blo 1207921 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B8716015 : Blo 1207921 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B1360039 : Blo 1207921 1360039 := bstep (se 1 (by rfl) ⟨1020029, by rfl⟩ : syracuseStep 1360039 = 2040059) B2040059
theorem B1811903 : Blo 1207921 1811903 := bstep (se 1 (by rfl) ⟨1358927, by rfl⟩ : syracuseStep 1811903 = 2717855) B2717855
theorem B158935121 : Blo 1207921 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B376637795 : Blo 1207921 376637795 := bstep (se 1 (by rfl) ⟨282478346, by rfl⟩ : syracuseStep 376637795 = 564956693) B564956693
theorem B1813295 : Blo 1207921 1813295 := bstep (se 1 (by rfl) ⟨1359971, by rfl⟩ : syracuseStep 1813295 = 2719943) B2719943
theorem B9301243 : Blo 1207921 9301243 := bstep (se 1 (by rfl) ⟨6975932, by rfl⟩ : syracuseStep 9301243 = 13951865) B13951865
theorem B1813967 : Blo 1207921 1813967 := bstep (se 1 (by rfl) ⟨1360475, by rfl⟩ : syracuseStep 1813967 = 2720951) B2720951
theorem B1208943 : Blo 1207921 1208943 := bstep (se 1 (by rfl) ⟨906707, by rfl⟩ : syracuseStep 1208943 = 1813415) B1813415
theorem B1209087 : Blo 1207921 1209087 := bstep (se 1 (by rfl) ⟨906815, by rfl⟩ : syracuseStep 1209087 = 1813631) B1813631
theorem B223359767 : Blo 1207921 223359767 := bstep (se 1 (by rfl) ⟨167519825, by rfl⟩ : syracuseStep 223359767 = 335039651) B335039651
theorem B29807443 : Blo 1207921 29807443 := bstep (se 1 (by rfl) ⟨22355582, by rfl⟩ : syracuseStep 29807443 = 44711165) B44711165
theorem B11621353 : Blo 1207921 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B150812225 : Blo 1207921 150812225 := bstep (se 2 (by rfl) ⟨56554584, by rfl⟩ : syracuseStep 150812225 = 113109169) B113109169
theorem B20920801 : Blo 1207921 20920801 := bstep (se 2 (by rfl) ⟨7845300, by rfl⟩ : syracuseStep 20920801 = 15690601) B15690601
theorem B2580473 : Blo 1207921 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B148906511 : Blo 1207921 148906511 := bstep (se 1 (by rfl) ⟨111679883, by rfl⟩ : syracuseStep 148906511 = 223359767) B223359767
theorem B27894401 : Blo 1207921 27894401 := bstep (se 2 (by rfl) ⟨10460400, by rfl⟩ : syracuseStep 27894401 = 20920801) B20920801
theorem B100541483 : Blo 1207921 100541483 := bstep (se 1 (by rfl) ⟨75406112, by rfl⟩ : syracuseStep 100541483 = 150812225) B150812225
theorem B105956747 : Blo 1207921 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B1813385 : Blo 1207921 1813385 := bstep (se 2 (by rfl) ⟨680019, by rfl⟩ : syracuseStep 1813385 = 1360039) B1360039
theorem B1207935 : Blo 1207921 1207935 := bstep (se 1 (by rfl) ⟨905951, by rfl⟩ : syracuseStep 1207935 = 1811903) B1811903
theorem B39743257 : Blo 1207921 39743257 := bstep (se 2 (by rfl) ⟨14903721, by rfl⟩ : syracuseStep 39743257 = 29807443) B29807443
theorem B15495137 : Blo 1207921 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B1208863 : Blo 1207921 1208863 := bstep (se 1 (by rfl) ⟨906647, by rfl⟩ : syracuseStep 1208863 = 1813295) B1813295
theorem B1209311 : Blo 1207921 1209311 := bstep (se 1 (by rfl) ⟨906983, by rfl⟩ : syracuseStep 1209311 = 1813967) B1813967
theorem B251091863 : Blo 1207921 251091863 := bstep (se 1 (by rfl) ⟨188318897, by rfl⟩ : syracuseStep 251091863 = 376637795) B376637795
theorem B12401657 : Blo 1207921 12401657 := bstep (se 2 (by rfl) ⟨4650621, by rfl⟩ : syracuseStep 12401657 = 9301243) B9301243
theorem B1720315 : Blo 1207921 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B99271007 : Blo 1207921 99271007 := bstep (se 1 (by rfl) ⟨74453255, by rfl⟩ : syracuseStep 99271007 = 148906511) B148906511
theorem B18596267 : Blo 1207921 18596267 := bstep (se 1 (by rfl) ⟨13947200, by rfl⟩ : syracuseStep 18596267 = 27894401) B27894401
theorem B67027655 : Blo 1207921 67027655 := bstep (se 1 (by rfl) ⟨50270741, by rfl⟩ : syracuseStep 67027655 = 100541483) B100541483
theorem B8267771 : Blo 1207921 8267771 := bstep (se 1 (by rfl) ⟨6200828, by rfl⟩ : syracuseStep 8267771 = 12401657) B12401657
theorem B1208923 : Blo 1207921 1208923 := bstep (se 1 (by rfl) ⟨906692, by rfl⟩ : syracuseStep 1208923 = 1813385) B1813385
theorem B52991009 : Blo 1207921 52991009 := bstep (se 2 (by rfl) ⟨19871628, by rfl⟩ : syracuseStep 52991009 = 39743257) B39743257
theorem B2293753 : Blo 1207921 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B70637831 : Blo 1207921 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B167394575 : Blo 1207921 167394575 := bstep (se 1 (by rfl) ⟨125545931, by rfl⟩ : syracuseStep 167394575 = 251091863) B251091863
theorem B10330091 : Blo 1207921 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B22047389 : Blo 1207921 22047389 := bstep (se 3 (by rfl) ⟨4133885, by rfl⟩ : syracuseStep 22047389 = 8267771) B8267771
theorem B3058337 : Blo 1207921 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B12397511 : Blo 1207921 12397511 := bstep (se 1 (by rfl) ⟨9298133, by rfl⟩ : syracuseStep 12397511 = 18596267) B18596267
theorem B35327339 : Blo 1207921 35327339 := bstep (se 1 (by rfl) ⟨26495504, by rfl⟩ : syracuseStep 35327339 = 52991009) B52991009
theorem B47091887 : Blo 1207921 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B111596383 : Blo 1207921 111596383 := bstep (se 1 (by rfl) ⟨83697287, by rfl⟩ : syracuseStep 111596383 = 167394575) B167394575
theorem B6886727 : Blo 1207921 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B66180671 : Blo 1207921 66180671 := bstep (se 1 (by rfl) ⟨49635503, by rfl⟩ : syracuseStep 66180671 = 99271007) B99271007
theorem B44685103 : Blo 1207921 44685103 := bstep (se 1 (by rfl) ⟨33513827, by rfl⟩ : syracuseStep 44685103 = 67027655) B67027655
theorem B14698259 : Blo 1207921 14698259 := bstep (se 1 (by rfl) ⟨11023694, by rfl⟩ : syracuseStep 14698259 = 22047389) B22047389
theorem B31394591 : Blo 1207921 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B4591151 : Blo 1207921 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B148795177 : Blo 1207921 148795177 := bstep (se 2 (by rfl) ⟨55798191, by rfl⟩ : syracuseStep 148795177 = 111596383) B111596383
theorem B44120447 : Blo 1207921 44120447 := bstep (se 1 (by rfl) ⟨33090335, by rfl⟩ : syracuseStep 44120447 = 66180671) B66180671
theorem B2038891 : Blo 1207921 2038891 := bstep (se 1 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 2038891 = 3058337) B3058337
theorem B8265007 : Blo 1207921 8265007 := bstep (se 1 (by rfl) ⟨6198755, by rfl⟩ : syracuseStep 8265007 = 12397511) B12397511
theorem B23551559 : Blo 1207921 23551559 := bstep (se 1 (by rfl) ⟨17663669, by rfl⟩ : syracuseStep 23551559 = 35327339) B35327339
theorem B59580137 : Blo 1207921 59580137 := bstep (se 2 (by rfl) ⟨22342551, by rfl⟩ : syracuseStep 59580137 = 44685103) B44685103
theorem B9798839 : Blo 1207921 9798839 := bstep (se 1 (by rfl) ⟨7349129, by rfl⟩ : syracuseStep 9798839 = 14698259) B14698259
theorem B11020009 : Blo 1207921 11020009 := bstep (se 2 (by rfl) ⟨4132503, by rfl⟩ : syracuseStep 11020009 = 8265007) B8265007
theorem B29413631 : Blo 1207921 29413631 := bstep (se 1 (by rfl) ⟨22060223, by rfl⟩ : syracuseStep 29413631 = 44120447) B44120447
theorem B158880365 : Blo 1207921 158880365 := bstep (se 3 (by rfl) ⟨29790068, by rfl⟩ : syracuseStep 158880365 = 59580137) B59580137
theorem B3060767 : Blo 1207921 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B15701039 : Blo 1207921 15701039 := bstep (se 1 (by rfl) ⟨11775779, by rfl⟩ : syracuseStep 15701039 = 23551559) B23551559
theorem B2718521 : Blo 1207921 2718521 := bstep (se 2 (by rfl) ⟨1019445, by rfl⟩ : syracuseStep 2718521 = 2038891) B2038891
theorem B20929727 : Blo 1207921 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B198393569 : Blo 1207921 198393569 := bstep (se 2 (by rfl) ⟨74397588, by rfl⟩ : syracuseStep 198393569 = 148795177) B148795177
theorem B2040511 : Blo 1207921 2040511 := bstep (se 1 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 2040511 = 3060767) B3060767
theorem B1812347 : Blo 1207921 1812347 := bstep (se 1 (by rfl) ⟨1359260, by rfl⟩ : syracuseStep 1812347 = 2718521) B2718521
theorem B13953151 : Blo 1207921 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B132262379 : Blo 1207921 132262379 := bstep (se 1 (by rfl) ⟨99196784, by rfl⟩ : syracuseStep 132262379 = 198393569) B198393569
theorem B6532559 : Blo 1207921 6532559 := bstep (se 1 (by rfl) ⟨4899419, by rfl⟩ : syracuseStep 6532559 = 9798839) B9798839
theorem B14693345 : Blo 1207921 14693345 := bstep (se 2 (by rfl) ⟨5510004, by rfl⟩ : syracuseStep 14693345 = 11020009) B11020009
theorem B19609087 : Blo 1207921 19609087 := bstep (se 1 (by rfl) ⟨14706815, by rfl⟩ : syracuseStep 19609087 = 29413631) B29413631
theorem B105920243 : Blo 1207921 105920243 := bstep (se 1 (by rfl) ⟨79440182, by rfl⟩ : syracuseStep 105920243 = 158880365) B158880365
theorem B10467359 : Blo 1207921 10467359 := bstep (se 1 (by rfl) ⟨7850519, by rfl⟩ : syracuseStep 10467359 = 15701039) B15701039
theorem B18604201 : Blo 1207921 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B2720681 : Blo 1207921 2720681 := bstep (se 2 (by rfl) ⟨1020255, by rfl⟩ : syracuseStep 2720681 = 2040511) B2040511
theorem B1208231 : Blo 1207921 1208231 := bstep (se 1 (by rfl) ⟨906173, by rfl⟩ : syracuseStep 1208231 = 1812347) B1812347
theorem B88174919 : Blo 1207921 88174919 := bstep (se 1 (by rfl) ⟨66131189, by rfl⟩ : syracuseStep 88174919 = 132262379) B132262379
theorem B26145449 : Blo 1207921 26145449 := bstep (se 2 (by rfl) ⟨9804543, by rfl⟩ : syracuseStep 26145449 = 19609087) B19609087
theorem B4355039 : Blo 1207921 4355039 := bstep (se 1 (by rfl) ⟨3266279, by rfl⟩ : syracuseStep 4355039 = 6532559) B6532559
theorem B9795563 : Blo 1207921 9795563 := bstep (se 1 (by rfl) ⟨7346672, by rfl⟩ : syracuseStep 9795563 = 14693345) B14693345
theorem B70613495 : Blo 1207921 70613495 := bstep (se 1 (by rfl) ⟨52960121, by rfl⟩ : syracuseStep 70613495 = 105920243) B105920243
theorem B6978239 : Blo 1207921 6978239 := bstep (se 1 (by rfl) ⟨5233679, by rfl⟩ : syracuseStep 6978239 = 10467359) B10467359
theorem B24805601 : Blo 1207921 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B6530375 : Blo 1207921 6530375 := bstep (se 1 (by rfl) ⟨4897781, by rfl⟩ : syracuseStep 6530375 = 9795563) B9795563
theorem B1813787 : Blo 1207921 1813787 := bstep (se 1 (by rfl) ⟨1360340, by rfl⟩ : syracuseStep 1813787 = 2720681) B2720681
theorem B2903359 : Blo 1207921 2903359 := bstep (se 1 (by rfl) ⟨2177519, by rfl⟩ : syracuseStep 2903359 = 4355039) B4355039
theorem B47075663 : Blo 1207921 47075663 := bstep (se 1 (by rfl) ⟨35306747, by rfl⟩ : syracuseStep 47075663 = 70613495) B70613495
theorem B58783279 : Blo 1207921 58783279 := bstep (se 1 (by rfl) ⟨44087459, by rfl⟩ : syracuseStep 58783279 = 88174919) B88174919
theorem B17430299 : Blo 1207921 17430299 := bstep (se 1 (by rfl) ⟨13072724, by rfl⟩ : syracuseStep 17430299 = 26145449) B26145449
theorem B4652159 : Blo 1207921 4652159 := bstep (se 1 (by rfl) ⟨3489119, by rfl⟩ : syracuseStep 4652159 = 6978239) B6978239
theorem B31383775 : Blo 1207921 31383775 := bstep (se 1 (by rfl) ⟨23537831, by rfl⟩ : syracuseStep 31383775 = 47075663) B47075663
theorem B4353583 : Blo 1207921 4353583 := bstep (se 1 (by rfl) ⟨3265187, by rfl⟩ : syracuseStep 4353583 = 6530375) B6530375
theorem B11620199 : Blo 1207921 11620199 := bstep (se 1 (by rfl) ⟨8715149, by rfl⟩ : syracuseStep 11620199 = 17430299) B17430299
theorem B49623029 : Blo 1207921 49623029 := bstep (se 5 (by rfl) ⟨2326079, by rfl⟩ : syracuseStep 49623029 = 4652159) B4652159
theorem B3871145 : Blo 1207921 3871145 := bstep (se 2 (by rfl) ⟨1451679, by rfl⟩ : syracuseStep 3871145 = 2903359) B2903359
theorem B78377705 : Blo 1207921 78377705 := bstep (se 2 (by rfl) ⟨29391639, by rfl⟩ : syracuseStep 78377705 = 58783279) B58783279
theorem B1209191 : Blo 1207921 1209191 := bstep (se 1 (by rfl) ⟨906893, by rfl⟩ : syracuseStep 1209191 = 1813787) B1813787
theorem B16537067 : Blo 1207921 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B2580763 : Blo 1207921 2580763 := bstep (se 1 (by rfl) ⟨1935572, by rfl⟩ : syracuseStep 2580763 = 3871145) B3871145
theorem B41845033 : Blo 1207921 41845033 := bstep (se 2 (by rfl) ⟨15691887, by rfl⟩ : syracuseStep 41845033 = 31383775) B31383775
theorem B33082019 : Blo 1207921 33082019 := bstep (se 1 (by rfl) ⟨24811514, by rfl⟩ : syracuseStep 33082019 = 49623029) B49623029
theorem B52251803 : Blo 1207921 52251803 := bstep (se 1 (by rfl) ⟨39188852, by rfl⟩ : syracuseStep 52251803 = 78377705) B78377705
theorem B5804777 : Blo 1207921 5804777 := bstep (se 2 (by rfl) ⟨2176791, by rfl⟩ : syracuseStep 5804777 = 4353583) B4353583
theorem B7746799 : Blo 1207921 7746799 := bstep (se 1 (by rfl) ⟨5810099, by rfl⟩ : syracuseStep 7746799 = 11620199) B11620199
theorem B11024711 : Blo 1207921 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B3441017 : Blo 1207921 3441017 := bstep (se 2 (by rfl) ⟨1290381, by rfl⟩ : syracuseStep 3441017 = 2580763) B2580763
theorem B7349807 : Blo 1207921 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B22054679 : Blo 1207921 22054679 := bstep (se 1 (by rfl) ⟨16541009, by rfl⟩ : syracuseStep 22054679 = 33082019) B33082019
theorem B34834535 : Blo 1207921 34834535 := bstep (se 1 (by rfl) ⟨26125901, by rfl⟩ : syracuseStep 34834535 = 52251803) B52251803
theorem B3869851 : Blo 1207921 3869851 := bstep (se 1 (by rfl) ⟨2902388, by rfl⟩ : syracuseStep 3869851 = 5804777) B5804777
theorem B55793377 : Blo 1207921 55793377 := bstep (se 2 (by rfl) ⟨20922516, by rfl⟩ : syracuseStep 55793377 = 41845033) B41845033
theorem B10329065 : Blo 1207921 10329065 := bstep (se 2 (by rfl) ⟨3873399, by rfl⟩ : syracuseStep 10329065 = 7746799) B7746799
theorem B2294011 : Blo 1207921 2294011 := bstep (se 1 (by rfl) ⟨1720508, by rfl⟩ : syracuseStep 2294011 = 3441017) B3441017
theorem B4899871 : Blo 1207921 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B6886043 : Blo 1207921 6886043 := bstep (se 1 (by rfl) ⟨5164532, by rfl⟩ : syracuseStep 6886043 = 10329065) B10329065
theorem B297564677 : Blo 1207921 297564677 := bstep (se 4 (by rfl) ⟨27896688, by rfl⟩ : syracuseStep 297564677 = 55793377) B55793377
theorem B14703119 : Blo 1207921 14703119 := bstep (se 1 (by rfl) ⟨11027339, by rfl⟩ : syracuseStep 14703119 = 22054679) B22054679
theorem B23223023 : Blo 1207921 23223023 := bstep (se 1 (by rfl) ⟨17417267, by rfl⟩ : syracuseStep 23223023 = 34834535) B34834535
theorem B5159801 : Blo 1207921 5159801 := bstep (se 2 (by rfl) ⟨1934925, by rfl⟩ : syracuseStep 5159801 = 3869851) B3869851
theorem B26132645 : Blo 1207921 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B3058681 : Blo 1207921 3058681 := bstep (se 2 (by rfl) ⟨1147005, by rfl⟩ : syracuseStep 3058681 = 2294011) B2294011
theorem B4590695 : Blo 1207921 4590695 := bstep (se 1 (by rfl) ⟨3443021, by rfl⟩ : syracuseStep 4590695 = 6886043) B6886043
theorem B9802079 : Blo 1207921 9802079 := bstep (se 1 (by rfl) ⟨7351559, by rfl⟩ : syracuseStep 9802079 = 14703119) B14703119
theorem B198376451 : Blo 1207921 198376451 := bstep (se 1 (by rfl) ⟨148782338, by rfl⟩ : syracuseStep 198376451 = 297564677) B297564677
theorem B15482015 : Blo 1207921 15482015 := bstep (se 1 (by rfl) ⟨11611511, by rfl⟩ : syracuseStep 15482015 = 23223023) B23223023
theorem B3439867 : Blo 1207921 3439867 := bstep (se 1 (by rfl) ⟨2579900, by rfl⟩ : syracuseStep 3439867 = 5159801) B5159801
theorem B3060463 : Blo 1207921 3060463 := bstep (se 1 (by rfl) ⟨2295347, by rfl⟩ : syracuseStep 3060463 = 4590695) B4590695
theorem B17421763 : Blo 1207921 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B6534719 : Blo 1207921 6534719 := bstep (se 1 (by rfl) ⟨4901039, by rfl⟩ : syracuseStep 6534719 = 9802079) B9802079
theorem B4078241 : Blo 1207921 4078241 := bstep (se 2 (by rfl) ⟨1529340, by rfl⟩ : syracuseStep 4078241 = 3058681) B3058681
theorem B4586489 : Blo 1207921 4586489 := bstep (se 2 (by rfl) ⟨1719933, by rfl⟩ : syracuseStep 4586489 = 3439867) B3439867
theorem B132250967 : Blo 1207921 132250967 := bstep (se 1 (by rfl) ⟨99188225, by rfl⟩ : syracuseStep 132250967 = 198376451) B198376451
theorem B10321343 : Blo 1207921 10321343 := bstep (se 1 (by rfl) ⟨7741007, by rfl⟩ : syracuseStep 10321343 = 15482015) B15482015
theorem B4080617 : Blo 1207921 4080617 := bstep (se 2 (by rfl) ⟨1530231, by rfl⟩ : syracuseStep 4080617 = 3060463) B3060463
theorem B3057659 : Blo 1207921 3057659 := bstep (se 1 (by rfl) ⟨2293244, by rfl⟩ : syracuseStep 3057659 = 4586489) B4586489
theorem B23229017 : Blo 1207921 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B88167311 : Blo 1207921 88167311 := bstep (se 1 (by rfl) ⟨66125483, by rfl⟩ : syracuseStep 88167311 = 132250967) B132250967
theorem B4356479 : Blo 1207921 4356479 := bstep (se 1 (by rfl) ⟨3267359, by rfl⟩ : syracuseStep 4356479 = 6534719) B6534719
theorem B2718827 : Blo 1207921 2718827 := bstep (se 1 (by rfl) ⟨2039120, by rfl⟩ : syracuseStep 2718827 = 4078241) B4078241
theorem B6880895 : Blo 1207921 6880895 := bstep (se 1 (by rfl) ⟨5160671, by rfl⟩ : syracuseStep 6880895 = 10321343) B10321343
theorem B58778207 : Blo 1207921 58778207 := bstep (se 1 (by rfl) ⟨44083655, by rfl⟩ : syracuseStep 58778207 = 88167311) B88167311
theorem B2720411 : Blo 1207921 2720411 := bstep (se 1 (by rfl) ⟨2040308, by rfl⟩ : syracuseStep 2720411 = 4080617) B4080617
theorem B1812551 : Blo 1207921 1812551 := bstep (se 1 (by rfl) ⟨1359413, by rfl⟩ : syracuseStep 1812551 = 2718827) B2718827
theorem B15486011 : Blo 1207921 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B2904319 : Blo 1207921 2904319 := bstep (se 1 (by rfl) ⟨2178239, by rfl⟩ : syracuseStep 2904319 = 4356479) B4356479
theorem B2038439 : Blo 1207921 2038439 := bstep (se 1 (by rfl) ⟨1528829, by rfl⟩ : syracuseStep 2038439 = 3057659) B3057659
theorem B4587263 : Blo 1207921 4587263 := bstep (se 1 (by rfl) ⟨3440447, by rfl⟩ : syracuseStep 4587263 = 6880895) B6880895
theorem B10324007 : Blo 1207921 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B3058175 : Blo 1207921 3058175 := bstep (se 1 (by rfl) ⟨2293631, by rfl⟩ : syracuseStep 3058175 = 4587263) B4587263
theorem B39185471 : Blo 1207921 39185471 := bstep (se 1 (by rfl) ⟨29389103, by rfl⟩ : syracuseStep 39185471 = 58778207) B58778207
theorem B1813607 : Blo 1207921 1813607 := bstep (se 1 (by rfl) ⟨1360205, by rfl⟩ : syracuseStep 1813607 = 2720411) B2720411
theorem B1208367 : Blo 1207921 1208367 := bstep (se 1 (by rfl) ⟨906275, by rfl⟩ : syracuseStep 1208367 = 1812551) B1812551
theorem B15489701 : Blo 1207921 15489701 := bstep (se 4 (by rfl) ⟨1452159, by rfl⟩ : syracuseStep 15489701 = 2904319) B2904319
theorem B1358959 : Blo 1207921 1358959 := bstep (se 1 (by rfl) ⟨1019219, by rfl⟩ : syracuseStep 1358959 = 2038439) B2038439
theorem B6882671 : Blo 1207921 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B1811945 : Blo 1207921 1811945 := bstep (se 2 (by rfl) ⟨679479, by rfl⟩ : syracuseStep 1811945 = 1358959) B1358959
theorem B10326467 : Blo 1207921 10326467 := bstep (se 1 (by rfl) ⟨7744850, by rfl⟩ : syracuseStep 10326467 = 15489701) B15489701
theorem B1209071 : Blo 1207921 1209071 := bstep (se 1 (by rfl) ⟨906803, by rfl⟩ : syracuseStep 1209071 = 1813607) B1813607
theorem B2038783 : Blo 1207921 2038783 := bstep (se 1 (by rfl) ⟨1529087, by rfl⟩ : syracuseStep 2038783 = 3058175) B3058175
theorem B26123647 : Blo 1207921 26123647 := bstep (se 1 (by rfl) ⟨19592735, by rfl⟩ : syracuseStep 26123647 = 39185471) B39185471
theorem B4588447 : Blo 1207921 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B6884311 : Blo 1207921 6884311 := bstep (se 1 (by rfl) ⟨5163233, by rfl⟩ : syracuseStep 6884311 = 10326467) B10326467
theorem B1207963 : Blo 1207921 1207963 := bstep (se 1 (by rfl) ⟨905972, by rfl⟩ : syracuseStep 1207963 = 1811945) B1811945
theorem B2718377 : Blo 1207921 2718377 := bstep (se 2 (by rfl) ⟨1019391, by rfl⟩ : syracuseStep 2718377 = 2038783) B2038783
theorem B34831529 : Blo 1207921 34831529 := bstep (se 2 (by rfl) ⟨13061823, by rfl⟩ : syracuseStep 34831529 = 26123647) B26123647
theorem B1812251 : Blo 1207921 1812251 := bstep (se 1 (by rfl) ⟨1359188, by rfl⟩ : syracuseStep 1812251 = 2718377) B2718377
theorem B9179081 : Blo 1207921 9179081 := bstep (se 2 (by rfl) ⟨3442155, by rfl⟩ : syracuseStep 9179081 = 6884311) B6884311
theorem B23221019 : Blo 1207921 23221019 := bstep (se 1 (by rfl) ⟨17415764, by rfl⟩ : syracuseStep 23221019 = 34831529) B34831529
theorem B6117929 : Blo 1207921 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B1208167 : Blo 1207921 1208167 := bstep (se 1 (by rfl) ⟨906125, by rfl⟩ : syracuseStep 1208167 = 1812251) B1812251
theorem B15480679 : Blo 1207921 15480679 := bstep (se 1 (by rfl) ⟨11610509, by rfl⟩ : syracuseStep 15480679 = 23221019) B23221019
theorem B4078619 : Blo 1207921 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B6119387 : Blo 1207921 6119387 := bstep (se 1 (by rfl) ⟨4589540, by rfl⟩ : syracuseStep 6119387 = 9179081) B9179081
theorem B20640905 : Blo 1207921 20640905 := bstep (se 2 (by rfl) ⟨7740339, by rfl⟩ : syracuseStep 20640905 = 15480679) B15480679
theorem B2719079 : Blo 1207921 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B4079591 : Blo 1207921 4079591 := bstep (se 1 (by rfl) ⟨3059693, by rfl⟩ : syracuseStep 4079591 = 6119387) B6119387
theorem B1812719 : Blo 1207921 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B13760603 : Blo 1207921 13760603 := bstep (se 1 (by rfl) ⟨10320452, by rfl⟩ : syracuseStep 13760603 = 20640905) B20640905
theorem B2719727 : Blo 1207921 2719727 := bstep (se 1 (by rfl) ⟨2039795, by rfl⟩ : syracuseStep 2719727 = 4079591) B4079591
theorem B1813151 : Blo 1207921 1813151 := bstep (se 1 (by rfl) ⟨1359863, by rfl⟩ : syracuseStep 1813151 = 2719727) B2719727
theorem B1208479 : Blo 1207921 1208479 := bstep (se 1 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 1208479 = 1812719) B1812719
theorem B9173735 : Blo 1207921 9173735 := bstep (se 1 (by rfl) ⟨6880301, by rfl⟩ : syracuseStep 9173735 = 13760603) B13760603
theorem B1208767 : Blo 1207921 1208767 := bstep (se 1 (by rfl) ⟨906575, by rfl⟩ : syracuseStep 1208767 = 1813151) B1813151
theorem B6115823 : Blo 1207921 6115823 := bstep (se 1 (by rfl) ⟨4586867, by rfl⟩ : syracuseStep 6115823 = 9173735) B9173735
theorem B4077215 : Blo 1207921 4077215 := bstep (se 1 (by rfl) ⟨3057911, by rfl⟩ : syracuseStep 4077215 = 6115823) B6115823
theorem B2718143 : Blo 1207921 2718143 := bstep (se 1 (by rfl) ⟨2038607, by rfl⟩ : syracuseStep 2718143 = 4077215) B4077215
theorem B1812095 : Blo 1207921 1812095 := bstep (se 1 (by rfl) ⟨1359071, by rfl⟩ : syracuseStep 1812095 = 2718143) B2718143
theorem B1208063 : Blo 1207921 1208063 := bstep (se 1 (by rfl) ⟨906047, by rfl⟩ : syracuseStep 1208063 = 1812095) B1812095

theorem C0 (j : ℕ) (h1 : 301980 ≤ j) (h2 : j ≤ 302354) : Blo 1207921 (4 * j + 3) := by
  interval_cases j
  · exact B1207923
  · exact B1207927
  · exact B1207931
  · exact B1207935
  · exact B1207939
  · exact B1207943
  · exact B1207947
  · exact B1207951
  · exact B1207955
  · exact B1207959
  · exact B1207963
  · exact B1207967
  · exact B1207971
  · exact B1207975
  · exact B1207979
  · exact B1207983
  · exact B1207987
  · exact B1207991
  · exact B1207995
  · exact B1207999
  · exact B1208003
  · exact B1208007
  · exact B1208011
  · exact B1208015
  · exact B1208019
  · exact B1208023
  · exact B1208027
  · exact B1208031
  · exact B1208035
  · exact B1208039
  · exact B1208043
  · exact B1208047
  · exact B1208051
  · exact B1208055
  · exact B1208059
  · exact B1208063
  · exact B1208067
  · exact B1208071
  · exact B1208075
  · exact B1208079
  · exact B1208083
  · exact B1208087
  · exact B1208091
  · exact B1208095
  · exact B1208099
  · exact B1208103
  · exact B1208107
  · exact B1208111
  · exact B1208115
  · exact B1208119
  · exact B1208123
  · exact B1208127
  · exact B1208131
  · exact B1208135
  · exact B1208139
  · exact B1208143
  · exact B1208147
  · exact B1208151
  · exact B1208155
  · exact B1208159
  · exact B1208163
  · exact B1208167
  · exact B1208171
  · exact B1208175
  · exact B1208179
  · exact B1208183
  · exact B1208187
  · exact B1208191
  · exact B1208195
  · exact B1208199
  · exact B1208203
  · exact B1208207
  · exact B1208211
  · exact B1208215
  · exact B1208219
  · exact B1208223
  · exact B1208227
  · exact B1208231
  · exact B1208235
  · exact B1208239
  · exact B1208243
  · exact B1208247
  · exact B1208251
  · exact B1208255
  · exact B1208259
  · exact B1208263
  · exact B1208267
  · exact B1208271
  · exact B1208275
  · exact B1208279
  · exact B1208283
  · exact B1208287
  · exact B1208291
  · exact B1208295
  · exact B1208299
  · exact B1208303
  · exact B1208307
  · exact B1208311
  · exact B1208315
  · exact B1208319
  · exact B1208323
  · exact B1208327
  · exact B1208331
  · exact B1208335
  · exact B1208339
  · exact B1208343
  · exact B1208347
  · exact B1208351
  · exact B1208355
  · exact B1208359
  · exact B1208363
  · exact B1208367
  · exact B1208371
  · exact B1208375
  · exact B1208379
  · exact B1208383
  · exact B1208387
  · exact B1208391
  · exact B1208395
  · exact B1208399
  · exact B1208403
  · exact B1208407
  · exact B1208411
  · exact B1208415
  · exact B1208419
  · exact B1208423
  · exact B1208427
  · exact B1208431
  · exact B1208435
  · exact B1208439
  · exact B1208443
  · exact B1208447
  · exact B1208451
  · exact B1208455
  · exact B1208459
  · exact B1208463
  · exact B1208467
  · exact B1208471
  · exact B1208475
  · exact B1208479
  · exact B1208483
  · exact B1208487
  · exact B1208491
  · exact B1208495
  · exact B1208499
  · exact B1208503
  · exact B1208507
  · exact B1208511
  · exact B1208515
  · exact B1208519
  · exact B1208523
  · exact B1208527
  · exact B1208531
  · exact B1208535
  · exact B1208539
  · exact B1208543
  · exact B1208547
  · exact B1208551
  · exact B1208555
  · exact B1208559
  · exact B1208563
  · exact B1208567
  · exact B1208571
  · exact B1208575
  · exact B1208579
  · exact B1208583
  · exact B1208587
  · exact B1208591
  · exact B1208595
  · exact B1208599
  · exact B1208603
  · exact B1208607
  · exact B1208611
  · exact B1208615
  · exact B1208619
  · exact B1208623
  · exact B1208627
  · exact B1208631
  · exact B1208635
  · exact B1208639
  · exact B1208643
  · exact B1208647
  · exact B1208651
  · exact B1208655
  · exact B1208659
  · exact B1208663
  · exact B1208667
  · exact B1208671
  · exact B1208675
  · exact B1208679
  · exact B1208683
  · exact B1208687
  · exact B1208691
  · exact B1208695
  · exact B1208699
  · exact B1208703
  · exact B1208707
  · exact B1208711
  · exact B1208715
  · exact B1208719
  · exact B1208723
  · exact B1208727
  · exact B1208731
  · exact B1208735
  · exact B1208739
  · exact B1208743
  · exact B1208747
  · exact B1208751
  · exact B1208755
  · exact B1208759
  · exact B1208763
  · exact B1208767
  · exact B1208771
  · exact B1208775
  · exact B1208779
  · exact B1208783
  · exact B1208787
  · exact B1208791
  · exact B1208795
  · exact B1208799
  · exact B1208803
  · exact B1208807
  · exact B1208811
  · exact B1208815
  · exact B1208819
  · exact B1208823
  · exact B1208827
  · exact B1208831
  · exact B1208835
  · exact B1208839
  · exact B1208843
  · exact B1208847
  · exact B1208851
  · exact B1208855
  · exact B1208859
  · exact B1208863
  · exact B1208867
  · exact B1208871
  · exact B1208875
  · exact B1208879
  · exact B1208883
  · exact B1208887
  · exact B1208891
  · exact B1208895
  · exact B1208899
  · exact B1208903
  · exact B1208907
  · exact B1208911
  · exact B1208915
  · exact B1208919
  · exact B1208923
  · exact B1208927
  · exact B1208931
  · exact B1208935
  · exact B1208939
  · exact B1208943
  · exact B1208947
  · exact B1208951
  · exact B1208955
  · exact B1208959
  · exact B1208963
  · exact B1208967
  · exact B1208971
  · exact B1208975
  · exact B1208979
  · exact B1208983
  · exact B1208987
  · exact B1208991
  · exact B1208995
  · exact B1208999
  · exact B1209003
  · exact B1209007
  · exact B1209011
  · exact B1209015
  · exact B1209019
  · exact B1209023
  · exact B1209027
  · exact B1209031
  · exact B1209035
  · exact B1209039
  · exact B1209043
  · exact B1209047
  · exact B1209051
  · exact B1209055
  · exact B1209059
  · exact B1209063
  · exact B1209067
  · exact B1209071
  · exact B1209075
  · exact B1209079
  · exact B1209083
  · exact B1209087
  · exact B1209091
  · exact B1209095
  · exact B1209099
  · exact B1209103
  · exact B1209107
  · exact B1209111
  · exact B1209115
  · exact B1209119
  · exact B1209123
  · exact B1209127
  · exact B1209131
  · exact B1209135
  · exact B1209139
  · exact B1209143
  · exact B1209147
  · exact B1209151
  · exact B1209155
  · exact B1209159
  · exact B1209163
  · exact B1209167
  · exact B1209171
  · exact B1209175
  · exact B1209179
  · exact B1209183
  · exact B1209187
  · exact B1209191
  · exact B1209195
  · exact B1209199
  · exact B1209203
  · exact B1209207
  · exact B1209211
  · exact B1209215
  · exact B1209219
  · exact B1209223
  · exact B1209227
  · exact B1209231
  · exact B1209235
  · exact B1209239
  · exact B1209243
  · exact B1209247
  · exact B1209251
  · exact B1209255
  · exact B1209259
  · exact B1209263
  · exact B1209267
  · exact B1209271
  · exact B1209275
  · exact B1209279
  · exact B1209283
  · exact B1209287
  · exact B1209291
  · exact B1209295
  · exact B1209299
  · exact B1209303
  · exact B1209307
  · exact B1209311
  · exact B1209315
  · exact B1209319
  · exact B1209323
  · exact B1209327
  · exact B1209331
  · exact B1209335
  · exact B1209339
  · exact B1209343
  · exact B1209347
  · exact B1209351
  · exact B1209355
  · exact B1209359
  · exact B1209363
  · exact B1209367
  · exact B1209371
  · exact B1209375
  · exact B1209379
  · exact B1209383
  · exact B1209387
  · exact B1209391
  · exact B1209395
  · exact B1209399
  · exact B1209403
  · exact B1209407
  · exact B1209411
  · exact B1209415
  · exact B1209419

theorem solution (m : ℕ) (hlo : 1207921 ≤ m) (hhi : m ≤ 1209421) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 301980 ≤ j := by omega
    have hj2 : j ≤ 302354 := by omega
    have hb : Blo 1207921 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
