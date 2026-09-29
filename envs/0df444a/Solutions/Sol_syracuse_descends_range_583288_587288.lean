-- Prove2me | solution 1 for syracuse_descends_range_583288_587288
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:24.728245+00:00
-- url     : https://prove2.me/submissions/a21400b8-6eed-4903-b061-56955005a787

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


theorem B3997973 : Blo 583288 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B1671461 : Blo 583288 1671461 := bbase (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) (by norm_num)
theorem B1114573 : Blo 583288 1114573 := bbase (se 3 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 1114573 = 417965) (by norm_num)
theorem B1114717 : Blo 583288 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B2818709 : Blo 583288 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B623261 : Blo 583288 623261 := bbase (se 3 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 623261 = 233723) (by norm_num)
theorem B2228917 : Blo 583288 2228917 := bbase (se 5 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 2228917 = 208961) (by norm_num)
theorem B1114877 : Blo 583288 1114877 := bbase (se 3 (by rfl) ⟨209039, by rfl⟩ : syracuseStep 1114877 = 418079) (by norm_num)
theorem B656221 : Blo 583288 656221 := bbase (se 3 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 656221 = 246083) (by norm_num)
theorem B656257 : Blo 583288 656257 := bbase (se 2 (by rfl) ⟨246096, by rfl⟩ : syracuseStep 656257 = 492193) (by norm_num)
theorem B656293 : Blo 583288 656293 := bbase (se 4 (by rfl) ⟨61527, by rfl⟩ : syracuseStep 656293 = 123055) (by norm_num)
theorem B656329 : Blo 583288 656329 := bbase (se 2 (by rfl) ⟨246123, by rfl⟩ : syracuseStep 656329 = 492247) (by norm_num)
theorem B2229221 : Blo 583288 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B656365 : Blo 583288 656365 := bbase (se 3 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 656365 = 246137) (by norm_num)
theorem B656401 : Blo 583288 656401 := bbase (se 2 (by rfl) ⟨246150, by rfl⟩ : syracuseStep 656401 = 492301) (by norm_num)
theorem B656437 : Blo 583288 656437 := bbase (se 5 (by rfl) ⟨30770, by rfl⟩ : syracuseStep 656437 = 61541) (by norm_num)
theorem B656473 : Blo 583288 656473 := bbase (se 2 (by rfl) ⟨246177, by rfl⟩ : syracuseStep 656473 = 492355) (by norm_num)
theorem B623705 : Blo 583288 623705 := bbase (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) (by norm_num)
theorem B656509 : Blo 583288 656509 := bbase (se 3 (by rfl) ⟨123095, by rfl⟩ : syracuseStep 656509 = 246191) (by norm_num)
theorem B6325397 : Blo 583288 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B656545 : Blo 583288 656545 := bbase (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) (by norm_num)
theorem B656581 : Blo 583288 656581 := bbase (se 4 (by rfl) ⟨61554, by rfl⟩ : syracuseStep 656581 = 123109) (by norm_num)
theorem B656617 : Blo 583288 656617 := bbase (se 2 (by rfl) ⟨246231, by rfl⟩ : syracuseStep 656617 = 492463) (by norm_num)
theorem B984325 : Blo 583288 984325 := bbase (se 4 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 984325 = 184561) (by norm_num)
theorem B656653 : Blo 583288 656653 := bbase (se 3 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 656653 = 246245) (by norm_num)
theorem B656689 : Blo 583288 656689 := bbase (se 2 (by rfl) ⟨246258, by rfl⟩ : syracuseStep 656689 = 492517) (by norm_num)
theorem B623953 : Blo 583288 623953 := bbase (se 2 (by rfl) ⟨233982, by rfl⟩ : syracuseStep 623953 = 467965) (by norm_num)
theorem B656725 : Blo 583288 656725 := bbase (se 12 (by rfl) ⟨240, by rfl⟩ : syracuseStep 656725 = 481) (by norm_num)
theorem B984413 : Blo 583288 984413 := bbase (se 3 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 984413 = 369155) (by norm_num)
theorem B656761 : Blo 583288 656761 := bbase (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) (by norm_num)
theorem B656797 : Blo 583288 656797 := bbase (se 3 (by rfl) ⟨123149, by rfl⟩ : syracuseStep 656797 = 246299) (by norm_num)
theorem B2491813 : Blo 583288 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B656833 : Blo 583288 656833 := bbase (se 2 (by rfl) ⟨246312, by rfl⟩ : syracuseStep 656833 = 492625) (by norm_num)
theorem B984541 : Blo 583288 984541 := bbase (se 3 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 984541 = 369203) (by norm_num)
theorem B1246693 : Blo 583288 1246693 := bbase (se 4 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 1246693 = 233755) (by norm_num)
theorem B656869 : Blo 583288 656869 := bbase (se 4 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 656869 = 123163) (by norm_num)
theorem B656905 : Blo 583288 656905 := bbase (se 2 (by rfl) ⟨246339, by rfl⟩ : syracuseStep 656905 = 492679) (by norm_num)
theorem B656941 : Blo 583288 656941 := bbase (se 3 (by rfl) ⟨123176, by rfl⟩ : syracuseStep 656941 = 246353) (by norm_num)
theorem B984629 : Blo 583288 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B656977 : Blo 583288 656977 := bbase (se 2 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 656977 = 492733) (by norm_num)
theorem B657013 : Blo 583288 657013 := bbase (se 5 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 657013 = 61595) (by norm_num)
theorem B657049 : Blo 583288 657049 := bbase (se 2 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 657049 = 492787) (by norm_num)
theorem B984757 : Blo 583288 984757 := bbase (se 5 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 984757 = 92321) (by norm_num)
theorem B657085 : Blo 583288 657085 := bbase (se 3 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 657085 = 246407) (by norm_num)
theorem B1312469 : Blo 583288 1312469 := bbase (se 7 (by rfl) ⟨15380, by rfl⟩ : syracuseStep 1312469 = 30761) (by norm_num)
theorem B657121 : Blo 583288 657121 := bbase (se 2 (by rfl) ⟨246420, by rfl⟩ : syracuseStep 657121 = 492841) (by norm_num)
theorem B624385 : Blo 583288 624385 := bbase (se 2 (by rfl) ⟨234144, by rfl⟩ : syracuseStep 624385 = 468289) (by norm_num)
theorem B657157 : Blo 583288 657157 := bbase (se 4 (by rfl) ⟨61608, by rfl⟩ : syracuseStep 657157 = 123217) (by norm_num)
theorem B984845 : Blo 583288 984845 := bbase (se 3 (by rfl) ⟨184658, by rfl⟩ : syracuseStep 984845 = 369317) (by norm_num)
theorem B1312541 : Blo 583288 1312541 := bbase (se 3 (by rfl) ⟨246101, by rfl⟩ : syracuseStep 1312541 = 492203) (by norm_num)
theorem B1869605 : Blo 583288 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B657193 : Blo 583288 657193 := bbase (se 2 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 657193 = 492895) (by norm_num)
theorem B624457 : Blo 583288 624457 := bbase (se 2 (by rfl) ⟨234171, by rfl⟩ : syracuseStep 624457 = 468343) (by norm_num)
theorem B657229 : Blo 583288 657229 := bbase (se 3 (by rfl) ⟨123230, by rfl⟩ : syracuseStep 657229 = 246461) (by norm_num)
theorem B591709 : Blo 583288 591709 := bbase (se 3 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 591709 = 221891) (by norm_num)
theorem B1247069 : Blo 583288 1247069 := bbase (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) (by norm_num)
theorem B1312613 : Blo 583288 1312613 := bbase (se 4 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 1312613 = 246115) (by norm_num)
theorem B657265 : Blo 583288 657265 := bbase (se 2 (by rfl) ⟨246474, by rfl⟩ : syracuseStep 657265 = 492949) (by norm_num)
theorem B1410949 : Blo 583288 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B984973 : Blo 583288 984973 := bbase (se 3 (by rfl) ⟨184682, by rfl⟩ : syracuseStep 984973 = 369365) (by norm_num)
theorem B657301 : Blo 583288 657301 := bbase (se 6 (by rfl) ⟨15405, by rfl⟩ : syracuseStep 657301 = 30811) (by norm_num)
theorem B1312685 : Blo 583288 1312685 := bbase (se 3 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 1312685 = 492257) (by norm_num)
theorem B657337 : Blo 583288 657337 := bbase (se 2 (by rfl) ⟨246501, by rfl⟩ : syracuseStep 657337 = 493003) (by norm_num)
theorem B657373 : Blo 583288 657373 := bbase (se 3 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 657373 = 246515) (by norm_num)
theorem B985061 : Blo 583288 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B1476589 : Blo 583288 1476589 := bbase (se 3 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 1476589 = 553721) (by norm_num)
theorem B1312757 : Blo 583288 1312757 := bbase (se 5 (by rfl) ⟨61535, by rfl⟩ : syracuseStep 1312757 = 123071) (by norm_num)
theorem B657409 : Blo 583288 657409 := bbase (se 2 (by rfl) ⟨246528, by rfl⟩ : syracuseStep 657409 = 493057) (by norm_num)
theorem B657445 : Blo 583288 657445 := bbase (se 4 (by rfl) ⟨61635, by rfl⟩ : syracuseStep 657445 = 123271) (by norm_num)
theorem B1312829 : Blo 583288 1312829 := bbase (se 3 (by rfl) ⟨246155, by rfl⟩ : syracuseStep 1312829 = 492311) (by norm_num)
theorem B657481 : Blo 583288 657481 := bbase (se 2 (by rfl) ⟨246555, by rfl⟩ : syracuseStep 657481 = 493111) (by norm_num)
theorem B1476701 : Blo 583288 1476701 := bbase (se 3 (by rfl) ⟨276881, by rfl⟩ : syracuseStep 1476701 = 553763) (by norm_num)
theorem B985189 : Blo 583288 985189 := bbase (se 4 (by rfl) ⟨92361, by rfl⟩ : syracuseStep 985189 = 184723) (by norm_num)
theorem B657517 : Blo 583288 657517 := bbase (se 3 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 657517 = 246569) (by norm_num)
theorem B1312901 : Blo 583288 1312901 := bbase (se 4 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 1312901 = 246169) (by norm_num)
theorem B657553 : Blo 583288 657553 := bbase (se 2 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 657553 = 493165) (by norm_num)
theorem B657589 : Blo 583288 657589 := bbase (se 5 (by rfl) ⟨30824, by rfl⟩ : syracuseStep 657589 = 61649) (by norm_num)
theorem B985277 : Blo 583288 985277 := bbase (se 3 (by rfl) ⟨184739, by rfl⟩ : syracuseStep 985277 = 369479) (by norm_num)
theorem B624829 : Blo 583288 624829 := bbase (se 3 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 624829 = 234311) (by norm_num)
theorem B1312973 : Blo 583288 1312973 := bbase (se 3 (by rfl) ⟨246182, by rfl⟩ : syracuseStep 1312973 = 492365) (by norm_num)
theorem B657625 : Blo 583288 657625 := bbase (se 2 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 657625 = 493219) (by norm_num)
theorem B657661 : Blo 583288 657661 := bbase (se 3 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 657661 = 246623) (by norm_num)
theorem B887053 : Blo 583288 887053 := bbase (se 3 (by rfl) ⟨166322, by rfl⟩ : syracuseStep 887053 = 332645) (by norm_num)
theorem B1313045 : Blo 583288 1313045 := bbase (se 6 (by rfl) ⟨30774, by rfl⟩ : syracuseStep 1313045 = 61549) (by norm_num)
theorem B1476893 : Blo 583288 1476893 := bbase (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) (by norm_num)
theorem B657697 : Blo 583288 657697 := bbase (se 2 (by rfl) ⟨246636, by rfl⟩ : syracuseStep 657697 = 493273) (by norm_num)
theorem B985405 : Blo 583288 985405 := bbase (se 3 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 985405 = 369527) (by norm_num)
theorem B657733 : Blo 583288 657733 := bbase (se 4 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 657733 = 123325) (by norm_num)
theorem B1313117 : Blo 583288 1313117 := bbase (se 3 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 1313117 = 492419) (by norm_num)
theorem B657769 : Blo 583288 657769 := bbase (se 2 (by rfl) ⟨246663, by rfl⟩ : syracuseStep 657769 = 493327) (by norm_num)
theorem B657805 : Blo 583288 657805 := bbase (se 3 (by rfl) ⟨123338, by rfl⟩ : syracuseStep 657805 = 246677) (by norm_num)
theorem B985493 : Blo 583288 985493 := bbase (se 6 (by rfl) ⟨23097, by rfl⟩ : syracuseStep 985493 = 46195) (by norm_num)
theorem B1313189 : Blo 583288 1313189 := bbase (se 4 (by rfl) ⟨123111, by rfl⟩ : syracuseStep 1313189 = 246223) (by norm_num)
theorem B657841 : Blo 583288 657841 := bbase (se 2 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 657841 = 493381) (by norm_num)
theorem B657877 : Blo 583288 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B1313261 : Blo 583288 1313261 := bbase (se 3 (by rfl) ⟨246236, by rfl⟩ : syracuseStep 1313261 = 492473) (by norm_num)
theorem B657913 : Blo 583288 657913 := bbase (se 2 (by rfl) ⟨246717, by rfl⟩ : syracuseStep 657913 = 493435) (by norm_num)
theorem B985621 : Blo 583288 985621 := bbase (se 6 (by rfl) ⟨23100, by rfl⟩ : syracuseStep 985621 = 46201) (by norm_num)
theorem B657949 : Blo 583288 657949 := bbase (se 3 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 657949 = 246731) (by norm_num)
theorem B1968677 : Blo 583288 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B1313333 : Blo 583288 1313333 := bbase (se 5 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 1313333 = 123125) (by norm_num)
theorem B625205 : Blo 583288 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B657985 : Blo 583288 657985 := bbase (se 2 (by rfl) ⟨246744, by rfl⟩ : syracuseStep 657985 = 493489) (by norm_num)
theorem B658021 : Blo 583288 658021 := bbase (se 4 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 658021 = 123379) (by norm_num)
theorem B985709 : Blo 583288 985709 := bbase (se 3 (by rfl) ⟨184820, by rfl⟩ : syracuseStep 985709 = 369641) (by norm_num)
theorem B1477237 : Blo 583288 1477237 := bbase (se 5 (by rfl) ⟨69245, by rfl⟩ : syracuseStep 1477237 = 138491) (by norm_num)
theorem B1313405 : Blo 583288 1313405 := bbase (se 3 (by rfl) ⟨246263, by rfl⟩ : syracuseStep 1313405 = 492527) (by norm_num)
theorem B625277 : Blo 583288 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B658057 : Blo 583288 658057 := bbase (se 2 (by rfl) ⟨246771, by rfl⟩ : syracuseStep 658057 = 493543) (by norm_num)
theorem B658093 : Blo 583288 658093 := bbase (se 3 (by rfl) ⟨123392, by rfl⟩ : syracuseStep 658093 = 246785) (by norm_num)
theorem B1313477 : Blo 583288 1313477 := bbase (se 4 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 1313477 = 246277) (by norm_num)
theorem B658129 : Blo 583288 658129 := bbase (se 2 (by rfl) ⟨246798, by rfl⟩ : syracuseStep 658129 = 493597) (by norm_num)
theorem B1051349 : Blo 583288 1051349 := bbase (se 7 (by rfl) ⟨12320, by rfl⟩ : syracuseStep 1051349 = 24641) (by norm_num)
theorem B1477349 : Blo 583288 1477349 := bbase (se 4 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 1477349 = 277003) (by norm_num)
theorem B985837 : Blo 583288 985837 := bbase (se 3 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 985837 = 369689) (by norm_num)
theorem B658165 : Blo 583288 658165 := bbase (se 5 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 658165 = 61703) (by norm_num)
theorem B1313549 : Blo 583288 1313549 := bbase (se 3 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 1313549 = 492581) (by norm_num)
theorem B658201 : Blo 583288 658201 := bbase (se 2 (by rfl) ⟨246825, by rfl⟩ : syracuseStep 658201 = 493651) (by norm_num)
theorem B625465 : Blo 583288 625465 := bbase (se 2 (by rfl) ⟨234549, by rfl⟩ : syracuseStep 625465 = 469099) (by norm_num)
theorem B658237 : Blo 583288 658237 := bbase (se 3 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 658237 = 246839) (by norm_num)
theorem B985925 : Blo 583288 985925 := bbase (se 4 (by rfl) ⟨92430, by rfl⟩ : syracuseStep 985925 = 184861) (by norm_num)
theorem B1313621 : Blo 583288 1313621 := bbase (se 9 (by rfl) ⟨3848, by rfl⟩ : syracuseStep 1313621 = 7697) (by norm_num)
theorem B658273 : Blo 583288 658273 := bbase (se 2 (by rfl) ⟨246852, by rfl⟩ : syracuseStep 658273 = 493705) (by norm_num)
theorem B2493301 : Blo 583288 2493301 := bbase (se 5 (by rfl) ⟨116873, by rfl⟩ : syracuseStep 2493301 = 233747) (by norm_num)
theorem B1051517 : Blo 583288 1051517 := bbase (se 3 (by rfl) ⟨197159, by rfl⟩ : syracuseStep 1051517 = 394319) (by norm_num)
theorem B2493317 : Blo 583288 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B658309 : Blo 583288 658309 := bbase (se 4 (by rfl) ⟨61716, by rfl⟩ : syracuseStep 658309 = 123433) (by norm_num)
theorem B1313693 : Blo 583288 1313693 := bbase (se 3 (by rfl) ⟨246317, by rfl⟩ : syracuseStep 1313693 = 492635) (by norm_num)
theorem B1477541 : Blo 583288 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B658345 : Blo 583288 658345 := bbase (se 2 (by rfl) ⟨246879, by rfl⟩ : syracuseStep 658345 = 493759) (by norm_num)
theorem B789421 : Blo 583288 789421 := bbase (se 3 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 789421 = 296033) (by norm_num)
theorem B986053 : Blo 583288 986053 := bbase (se 4 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 986053 = 184885) (by norm_num)
theorem B658381 : Blo 583288 658381 := bbase (se 3 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 658381 = 246893) (by norm_num)
theorem B1969109 : Blo 583288 1969109 := bbase (se 7 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 1969109 = 46151) (by norm_num)
theorem B1313765 : Blo 583288 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B658417 : Blo 583288 658417 := bbase (se 2 (by rfl) ⟨246906, by rfl⟩ : syracuseStep 658417 = 493813) (by norm_num)
theorem B625649 : Blo 583288 625649 := bbase (se 2 (by rfl) ⟨234618, by rfl⟩ : syracuseStep 625649 = 469237) (by norm_num)
theorem B658453 : Blo 583288 658453 := bbase (se 6 (by rfl) ⟨15432, by rfl⟩ : syracuseStep 658453 = 30865) (by norm_num)
theorem B986141 : Blo 583288 986141 := bbase (se 3 (by rfl) ⟨184901, by rfl⟩ : syracuseStep 986141 = 369803) (by norm_num)
theorem B1313837 : Blo 583288 1313837 := bbase (se 3 (by rfl) ⟨246344, by rfl⟩ : syracuseStep 1313837 = 492689) (by norm_num)
theorem B658489 : Blo 583288 658489 := bbase (se 2 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 658489 = 493867) (by norm_num)
theorem B658525 : Blo 583288 658525 := bbase (se 3 (by rfl) ⟨123473, by rfl⟩ : syracuseStep 658525 = 246947) (by norm_num)
theorem B1313909 : Blo 583288 1313909 := bbase (se 5 (by rfl) ⟨61589, by rfl⟩ : syracuseStep 1313909 = 123179) (by norm_num)
theorem B658561 : Blo 583288 658561 := bbase (se 2 (by rfl) ⟨246960, by rfl⟩ : syracuseStep 658561 = 493921) (by norm_num)
theorem B1051805 : Blo 583288 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B986269 : Blo 583288 986269 := bbase (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) (by norm_num)
theorem B658597 : Blo 583288 658597 := bbase (se 4 (by rfl) ⟨61743, by rfl⟩ : syracuseStep 658597 = 123487) (by norm_num)
theorem B1313981 : Blo 583288 1313981 := bbase (se 3 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 1313981 = 492743) (by norm_num)
theorem B1182917 : Blo 583288 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B658633 : Blo 583288 658633 := bbase (se 2 (by rfl) ⟨246987, by rfl⟩ : syracuseStep 658633 = 493975) (by norm_num)
theorem B658669 : Blo 583288 658669 := bbase (se 3 (by rfl) ⟨123500, by rfl⟩ : syracuseStep 658669 = 247001) (by norm_num)
theorem B986357 : Blo 583288 986357 := bbase (se 5 (by rfl) ⟨46235, by rfl⟩ : syracuseStep 986357 = 92471) (by norm_num)
theorem B1477885 : Blo 583288 1477885 := bbase (se 3 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 1477885 = 554207) (by norm_num)
theorem B1314053 : Blo 583288 1314053 := bbase (se 4 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 1314053 = 246385) (by norm_num)
theorem B658705 : Blo 583288 658705 := bbase (se 2 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 658705 = 494029) (by norm_num)
theorem B658741 : Blo 583288 658741 := bbase (se 5 (by rfl) ⟨30878, by rfl⟩ : syracuseStep 658741 = 61757) (by norm_num)
theorem B1314125 : Blo 583288 1314125 := bbase (se 3 (by rfl) ⟨246398, by rfl⟩ : syracuseStep 1314125 = 492797) (by norm_num)
theorem B658777 : Blo 583288 658777 := bbase (se 2 (by rfl) ⟨247041, by rfl⟩ : syracuseStep 658777 = 494083) (by norm_num)
theorem B1477997 : Blo 583288 1477997 := bbase (se 3 (by rfl) ⟨277124, by rfl⟩ : syracuseStep 1477997 = 554249) (by norm_num)
theorem B888173 : Blo 583288 888173 := bbase (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) (by norm_num)
theorem B986485 : Blo 583288 986485 := bbase (se 5 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 986485 = 92483) (by norm_num)
theorem B658813 : Blo 583288 658813 := bbase (se 3 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 658813 = 247055) (by norm_num)
theorem B1969541 : Blo 583288 1969541 := bbase (se 4 (by rfl) ⟨184644, by rfl⟩ : syracuseStep 1969541 = 369289) (by norm_num)
theorem B1314197 : Blo 583288 1314197 := bbase (se 6 (by rfl) ⟨30801, by rfl⟩ : syracuseStep 1314197 = 61603) (by norm_num)
theorem B888221 : Blo 583288 888221 := bbase (se 3 (by rfl) ⟨166541, by rfl⟩ : syracuseStep 888221 = 333083) (by norm_num)
theorem B658849 : Blo 583288 658849 := bbase (se 2 (by rfl) ⟨247068, by rfl⟩ : syracuseStep 658849 = 494137) (by norm_num)
theorem B1248709 : Blo 583288 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B658885 : Blo 583288 658885 := bbase (se 4 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 658885 = 123541) (by norm_num)
theorem B986573 : Blo 583288 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B1314269 : Blo 583288 1314269 := bbase (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) (by norm_num)
theorem B658921 : Blo 583288 658921 := bbase (se 2 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 658921 = 494191) (by norm_num)
theorem B658957 : Blo 583288 658957 := bbase (se 3 (by rfl) ⟨123554, by rfl⟩ : syracuseStep 658957 = 247109) (by norm_num)
theorem B1314341 : Blo 583288 1314341 := bbase (se 4 (by rfl) ⟨123219, by rfl⟩ : syracuseStep 1314341 = 246439) (by norm_num)
theorem B1478189 : Blo 583288 1478189 := bbase (se 3 (by rfl) ⟨277160, by rfl⟩ : syracuseStep 1478189 = 554321) (by norm_num)
theorem B658993 : Blo 583288 658993 := bbase (se 2 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 658993 = 494245) (by norm_num)
theorem B986701 : Blo 583288 986701 := bbase (se 3 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 986701 = 370013) (by norm_num)
theorem B659029 : Blo 583288 659029 := bbase (se 8 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 659029 = 7723) (by norm_num)
theorem B1314413 : Blo 583288 1314413 := bbase (se 3 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 1314413 = 492905) (by norm_num)
theorem B659065 : Blo 583288 659065 := bbase (se 2 (by rfl) ⟨247149, by rfl⟩ : syracuseStep 659065 = 494299) (by norm_num)
theorem B659101 : Blo 583288 659101 := bbase (se 3 (by rfl) ⟨123581, by rfl⟩ : syracuseStep 659101 = 247163) (by norm_num)
theorem B986789 : Blo 583288 986789 := bbase (se 4 (by rfl) ⟨92511, by rfl⟩ : syracuseStep 986789 = 185023) (by norm_num)
theorem B1085093 : Blo 583288 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B1314485 : Blo 583288 1314485 := bbase (se 5 (by rfl) ⟨61616, by rfl⟩ : syracuseStep 1314485 = 123233) (by norm_num)
theorem B659137 : Blo 583288 659137 := bbase (se 2 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 659137 = 494353) (by norm_num)
theorem B626401 : Blo 583288 626401 := bbase (se 2 (by rfl) ⟨234900, by rfl⟩ : syracuseStep 626401 = 469801) (by norm_num)
theorem B659173 : Blo 583288 659173 := bbase (se 4 (by rfl) ⟨61797, by rfl⟩ : syracuseStep 659173 = 123595) (by norm_num)
theorem B1314557 : Blo 583288 1314557 := bbase (se 3 (by rfl) ⟨246479, by rfl⟩ : syracuseStep 1314557 = 492959) (by norm_num)
theorem B659209 : Blo 583288 659209 := bbase (se 2 (by rfl) ⟨247203, by rfl⟩ : syracuseStep 659209 = 494407) (by norm_num)
theorem B986917 : Blo 583288 986917 := bbase (se 4 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 986917 = 185047) (by norm_num)
theorem B626473 : Blo 583288 626473 := bbase (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) (by norm_num)
theorem B659245 : Blo 583288 659245 := bbase (se 3 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 659245 = 247217) (by norm_num)
theorem B1969973 : Blo 583288 1969973 := bbase (se 5 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 1969973 = 184685) (by norm_num)
theorem B1314629 : Blo 583288 1314629 := bbase (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) (by norm_num)
theorem B659281 : Blo 583288 659281 := bbase (se 2 (by rfl) ⟨247230, by rfl⟩ : syracuseStep 659281 = 494461) (by norm_num)
theorem B659317 : Blo 583288 659317 := bbase (se 5 (by rfl) ⟨30905, by rfl⟩ : syracuseStep 659317 = 61811) (by norm_num)
theorem B987005 : Blo 583288 987005 := bbase (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) (by norm_num)
theorem B1478533 : Blo 583288 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1314701 : Blo 583288 1314701 := bbase (se 3 (by rfl) ⟨246506, by rfl⟩ : syracuseStep 1314701 = 493013) (by norm_num)
theorem B4231061 : Blo 583288 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B659353 : Blo 583288 659353 := bbase (se 2 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 659353 = 494515) (by norm_num)
theorem B659389 : Blo 583288 659389 := bbase (se 3 (by rfl) ⟨123635, by rfl⟩ : syracuseStep 659389 = 247271) (by norm_num)
theorem B1314773 : Blo 583288 1314773 := bbase (se 7 (by rfl) ⟨15407, by rfl⟩ : syracuseStep 1314773 = 30815) (by norm_num)
theorem B626653 : Blo 583288 626653 := bbase (se 3 (by rfl) ⟨117497, by rfl⟩ : syracuseStep 626653 = 234995) (by norm_num)
theorem B659425 : Blo 583288 659425 := bbase (se 2 (by rfl) ⟨247284, by rfl⟩ : syracuseStep 659425 = 494569) (by norm_num)
theorem B1478645 : Blo 583288 1478645 := bbase (se 5 (by rfl) ⟨69311, by rfl⟩ : syracuseStep 1478645 = 138623) (by norm_num)
theorem B987133 : Blo 583288 987133 := bbase (se 3 (by rfl) ⟨185087, by rfl⟩ : syracuseStep 987133 = 370175) (by norm_num)
theorem B659461 : Blo 583288 659461 := bbase (se 4 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 659461 = 123649) (by norm_num)
theorem B1314845 : Blo 583288 1314845 := bbase (se 3 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 1314845 = 493067) (by norm_num)
theorem B659497 : Blo 583288 659497 := bbase (se 2 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 659497 = 494623) (by norm_num)
theorem B659533 : Blo 583288 659533 := bbase (se 3 (by rfl) ⟨123662, by rfl⟩ : syracuseStep 659533 = 247325) (by norm_num)
theorem B987221 : Blo 583288 987221 := bbase (se 8 (by rfl) ⟨5784, by rfl⟩ : syracuseStep 987221 = 11569) (by norm_num)
theorem B1314917 : Blo 583288 1314917 := bbase (se 4 (by rfl) ⟨123273, by rfl⟩ : syracuseStep 1314917 = 246547) (by norm_num)
theorem B659569 : Blo 583288 659569 := bbase (se 2 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 659569 = 494677) (by norm_num)
theorem B659605 : Blo 583288 659605 := bbase (se 6 (by rfl) ⟨15459, by rfl⟩ : syracuseStep 659605 = 30919) (by norm_num)
theorem B1314989 : Blo 583288 1314989 := bbase (se 3 (by rfl) ⟨246560, by rfl⟩ : syracuseStep 1314989 = 493121) (by norm_num)
theorem B1478837 : Blo 583288 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B659641 : Blo 583288 659641 := bbase (se 2 (by rfl) ⟨247365, by rfl⟩ : syracuseStep 659641 = 494731) (by norm_num)
theorem B987349 : Blo 583288 987349 := bbase (se 7 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 987349 = 23141) (by norm_num)
theorem B659677 : Blo 583288 659677 := bbase (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) (by norm_num)
theorem B1970405 : Blo 583288 1970405 := bbase (se 4 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 1970405 = 369451) (by norm_num)
theorem B1315061 : Blo 583288 1315061 := bbase (se 5 (by rfl) ⟨61643, by rfl⟩ : syracuseStep 1315061 = 123287) (by norm_num)
theorem B659713 : Blo 583288 659713 := bbase (se 2 (by rfl) ⟨247392, by rfl⟩ : syracuseStep 659713 = 494785) (by norm_num)
theorem B659749 : Blo 583288 659749 := bbase (se 4 (by rfl) ⟨61851, by rfl⟩ : syracuseStep 659749 = 123703) (by norm_num)
theorem B987437 : Blo 583288 987437 := bbase (se 3 (by rfl) ⟨185144, by rfl⟩ : syracuseStep 987437 = 370289) (by norm_num)
theorem B1315133 : Blo 583288 1315133 := bbase (se 3 (by rfl) ⟨246587, by rfl⟩ : syracuseStep 1315133 = 493175) (by norm_num)
theorem B1249597 : Blo 583288 1249597 := bbase (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) (by norm_num)
theorem B659785 : Blo 583288 659785 := bbase (se 2 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 659785 = 494839) (by norm_num)
theorem B1053037 : Blo 583288 1053037 := bbase (se 3 (by rfl) ⟨197444, by rfl⟩ : syracuseStep 1053037 = 394889) (by norm_num)
theorem B659821 : Blo 583288 659821 := bbase (se 3 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 659821 = 247433) (by norm_num)
theorem B1315205 : Blo 583288 1315205 := bbase (se 4 (by rfl) ⟨123300, by rfl⟩ : syracuseStep 1315205 = 246601) (by norm_num)
theorem B659857 : Blo 583288 659857 := bbase (se 2 (by rfl) ⟨247446, by rfl⟩ : syracuseStep 659857 = 494893) (by norm_num)
theorem B627097 : Blo 583288 627097 := bbase (se 2 (by rfl) ⟨235161, by rfl⟩ : syracuseStep 627097 = 470323) (by norm_num)
theorem B987565 : Blo 583288 987565 := bbase (se 3 (by rfl) ⟨185168, by rfl⟩ : syracuseStep 987565 = 370337) (by norm_num)
theorem B1053109 : Blo 583288 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B659893 : Blo 583288 659893 := bbase (se 5 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 659893 = 61865) (by norm_num)
theorem B1315277 : Blo 583288 1315277 := bbase (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) (by norm_num)
theorem B659929 : Blo 583288 659929 := bbase (se 2 (by rfl) ⟨247473, by rfl⟩ : syracuseStep 659929 = 494947) (by norm_num)
theorem B594397 : Blo 583288 594397 := bbase (se 3 (by rfl) ⟨111449, by rfl⟩ : syracuseStep 594397 = 222899) (by norm_num)
theorem B659965 : Blo 583288 659965 := bbase (se 3 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 659965 = 247487) (by norm_num)
theorem B987653 : Blo 583288 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B1479181 : Blo 583288 1479181 := bbase (se 3 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 1479181 = 554693) (by norm_num)
theorem B1315349 : Blo 583288 1315349 := bbase (se 6 (by rfl) ⟨30828, by rfl⟩ : syracuseStep 1315349 = 61657) (by norm_num)
theorem B660001 : Blo 583288 660001 := bbase (se 2 (by rfl) ⟨247500, by rfl⟩ : syracuseStep 660001 = 495001) (by norm_num)
theorem B1053253 : Blo 583288 1053253 := bbase (se 4 (by rfl) ⟨98742, by rfl⟩ : syracuseStep 1053253 = 197485) (by norm_num)
theorem B660037 : Blo 583288 660037 := bbase (se 4 (by rfl) ⟨61878, by rfl⟩ : syracuseStep 660037 = 123757) (by norm_num)
theorem B1315421 : Blo 583288 1315421 := bbase (se 3 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 1315421 = 493283) (by norm_num)
theorem B660073 : Blo 583288 660073 := bbase (se 2 (by rfl) ⟨247527, by rfl⟩ : syracuseStep 660073 = 495055) (by norm_num)
theorem B1479293 : Blo 583288 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B987781 : Blo 583288 987781 := bbase (se 4 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 987781 = 185209) (by norm_num)
theorem B660109 : Blo 583288 660109 := bbase (se 3 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 660109 = 247541) (by norm_num)
theorem B1970837 : Blo 583288 1970837 := bbase (se 6 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 1970837 = 92383) (by norm_num)
theorem B1315493 : Blo 583288 1315493 := bbase (se 4 (by rfl) ⟨123327, by rfl⟩ : syracuseStep 1315493 = 246655) (by norm_num)
theorem B660145 : Blo 583288 660145 := bbase (se 2 (by rfl) ⟨247554, by rfl⟩ : syracuseStep 660145 = 495109) (by norm_num)
theorem B660181 : Blo 583288 660181 := bbase (se 7 (by rfl) ⟨7736, by rfl⟩ : syracuseStep 660181 = 15473) (by norm_num)
theorem B987869 : Blo 583288 987869 := bbase (se 3 (by rfl) ⟨185225, by rfl⟩ : syracuseStep 987869 = 370451) (by norm_num)
theorem B1315565 : Blo 583288 1315565 := bbase (se 3 (by rfl) ⟨246668, by rfl⟩ : syracuseStep 1315565 = 493337) (by norm_num)
theorem B660217 : Blo 583288 660217 := bbase (se 2 (by rfl) ⟨247581, by rfl⟩ : syracuseStep 660217 = 495163) (by norm_num)
theorem B660253 : Blo 583288 660253 := bbase (se 3 (by rfl) ⟨123797, by rfl⟩ : syracuseStep 660253 = 247595) (by norm_num)
theorem B1250093 : Blo 583288 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1315637 : Blo 583288 1315637 := bbase (se 5 (by rfl) ⟨61670, by rfl⟩ : syracuseStep 1315637 = 123341) (by norm_num)
theorem B1479485 : Blo 583288 1479485 := bbase (se 3 (by rfl) ⟨277403, by rfl⟩ : syracuseStep 1479485 = 554807) (by norm_num)
theorem B660289 : Blo 583288 660289 := bbase (se 2 (by rfl) ⟨247608, by rfl⟩ : syracuseStep 660289 = 495217) (by norm_num)
theorem B2954069 : Blo 583288 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B987997 : Blo 583288 987997 := bbase (se 3 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 987997 = 370499) (by norm_num)
theorem B660325 : Blo 583288 660325 := bbase (se 4 (by rfl) ⟨61905, by rfl⟩ : syracuseStep 660325 = 123811) (by norm_num)
theorem B1315709 : Blo 583288 1315709 := bbase (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) (by norm_num)
theorem B660361 : Blo 583288 660361 := bbase (se 2 (by rfl) ⟨247635, by rfl⟩ : syracuseStep 660361 = 495271) (by norm_num)
theorem B660397 : Blo 583288 660397 := bbase (se 3 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 660397 = 247649) (by norm_num)
theorem B988085 : Blo 583288 988085 := bbase (se 5 (by rfl) ⟨46316, by rfl⟩ : syracuseStep 988085 = 92633) (by norm_num)
theorem B1315781 : Blo 583288 1315781 := bbase (se 4 (by rfl) ⟨123354, by rfl⟩ : syracuseStep 1315781 = 246709) (by norm_num)
theorem B660433 : Blo 583288 660433 := bbase (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) (by norm_num)
theorem B4985813 : Blo 583288 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B660469 : Blo 583288 660469 := bbase (se 5 (by rfl) ⟨30959, by rfl⟩ : syracuseStep 660469 = 61919) (by norm_num)
theorem B1315853 : Blo 583288 1315853 := bbase (se 3 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 1315853 = 493445) (by norm_num)
theorem B660505 : Blo 583288 660505 := bbase (se 2 (by rfl) ⟨247689, by rfl⟩ : syracuseStep 660505 = 495379) (by norm_num)
theorem B988213 : Blo 583288 988213 := bbase (se 5 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 988213 = 92645) (by norm_num)
theorem B660541 : Blo 583288 660541 := bbase (se 3 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 660541 = 247703) (by norm_num)
theorem B1971269 : Blo 583288 1971269 := bbase (se 4 (by rfl) ⟨184806, by rfl⟩ : syracuseStep 1971269 = 369613) (by norm_num)
theorem B2495573 : Blo 583288 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B1315925 : Blo 583288 1315925 := bbase (se 8 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 1315925 = 15421) (by norm_num)
theorem B660577 : Blo 583288 660577 := bbase (se 2 (by rfl) ⟨247716, by rfl⟩ : syracuseStep 660577 = 495433) (by norm_num)
theorem B660613 : Blo 583288 660613 := bbase (se 4 (by rfl) ⟨61932, by rfl⟩ : syracuseStep 660613 = 123865) (by norm_num)
theorem B988301 : Blo 583288 988301 := bbase (se 3 (by rfl) ⟨185306, by rfl⟩ : syracuseStep 988301 = 370613) (by norm_num)
theorem B1479829 : Blo 583288 1479829 := bbase (se 6 (by rfl) ⟨34683, by rfl⟩ : syracuseStep 1479829 = 69367) (by norm_num)
theorem B1315997 : Blo 583288 1315997 := bbase (se 3 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 1315997 = 493499) (by norm_num)
theorem B660649 : Blo 583288 660649 := bbase (se 2 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 660649 = 495487) (by norm_num)
theorem B890045 : Blo 583288 890045 := bbase (se 3 (by rfl) ⟨166883, by rfl⟩ : syracuseStep 890045 = 333767) (by norm_num)
theorem B660685 : Blo 583288 660685 := bbase (se 3 (by rfl) ⟨123878, by rfl⟩ : syracuseStep 660685 = 247757) (by norm_num)
theorem B1316069 : Blo 583288 1316069 := bbase (se 4 (by rfl) ⟨123381, by rfl⟩ : syracuseStep 1316069 = 246763) (by norm_num)
theorem B1479941 : Blo 583288 1479941 := bbase (se 4 (by rfl) ⟨138744, by rfl⟩ : syracuseStep 1479941 = 277489) (by norm_num)
theorem B988429 : Blo 583288 988429 := bbase (se 3 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 988429 = 370661) (by norm_num)
theorem B1316141 : Blo 583288 1316141 := bbase (se 3 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 1316141 = 493553) (by norm_num)
theorem B988517 : Blo 583288 988517 := bbase (se 4 (by rfl) ⟨92673, by rfl⟩ : syracuseStep 988517 = 185347) (by norm_num)
theorem B5051765 : Blo 583288 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1316213 : Blo 583288 1316213 := bbase (se 5 (by rfl) ⟨61697, by rfl⟩ : syracuseStep 1316213 = 123395) (by norm_num)
theorem B1054117 : Blo 583288 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B1316285 : Blo 583288 1316285 := bbase (se 3 (by rfl) ⟨246803, by rfl⟩ : syracuseStep 1316285 = 493607) (by norm_num)
theorem B1480133 : Blo 583288 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B988645 : Blo 583288 988645 := bbase (se 4 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 988645 = 185371) (by norm_num)
theorem B1971701 : Blo 583288 1971701 := bbase (se 5 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 1971701 = 184847) (by norm_num)
theorem B1054205 : Blo 583288 1054205 := bbase (se 3 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 1054205 = 395327) (by norm_num)
theorem B1316357 : Blo 583288 1316357 := bbase (se 4 (by rfl) ⟨123408, by rfl⟩ : syracuseStep 1316357 = 246817) (by norm_num)
theorem B988733 : Blo 583288 988733 := bbase (se 3 (by rfl) ⟨185387, by rfl⟩ : syracuseStep 988733 = 370775) (by norm_num)
theorem B1316429 : Blo 583288 1316429 := bbase (se 3 (by rfl) ⟨246830, by rfl⟩ : syracuseStep 1316429 = 493661) (by norm_num)
theorem B1873525 : Blo 583288 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B1185421 : Blo 583288 1185421 := bbase (se 3 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 1185421 = 444533) (by norm_num)
theorem B1250957 : Blo 583288 1250957 := bbase (se 3 (by rfl) ⟨234554, by rfl⟩ : syracuseStep 1250957 = 469109) (by norm_num)
theorem B1316501 : Blo 583288 1316501 := bbase (se 6 (by rfl) ⟨30855, by rfl⟩ : syracuseStep 1316501 = 61711) (by norm_num)
theorem B7214741 : Blo 583288 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B988861 : Blo 583288 988861 := bbase (se 3 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 988861 = 370823) (by norm_num)
theorem B1316573 : Blo 583288 1316573 := bbase (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) (by norm_num)
theorem B988949 : Blo 583288 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B1480477 : Blo 583288 1480477 := bbase (se 3 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 1480477 = 555179) (by norm_num)
theorem B1251101 : Blo 583288 1251101 := bbase (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) (by norm_num)
theorem B1316645 : Blo 583288 1316645 := bbase (se 4 (by rfl) ⟨123435, by rfl⟩ : syracuseStep 1316645 = 246871) (by norm_num)
theorem B1316717 : Blo 583288 1316717 := bbase (se 3 (by rfl) ⟨246884, by rfl⟩ : syracuseStep 1316717 = 493769) (by norm_num)
theorem B1873781 : Blo 583288 1873781 := bbase (se 5 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 1873781 = 175667) (by norm_num)
theorem B1480589 : Blo 583288 1480589 := bbase (se 3 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 1480589 = 555221) (by norm_num)
theorem B989077 : Blo 583288 989077 := bbase (se 6 (by rfl) ⟨23181, by rfl⟩ : syracuseStep 989077 = 46363) (by norm_num)
theorem B1972133 : Blo 583288 1972133 := bbase (se 4 (by rfl) ⟨184887, by rfl⟩ : syracuseStep 1972133 = 369775) (by norm_num)
theorem B1054637 : Blo 583288 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B1316789 : Blo 583288 1316789 := bbase (se 5 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 1316789 = 123449) (by norm_num)
theorem B989165 : Blo 583288 989165 := bbase (se 3 (by rfl) ⟨185468, by rfl⟩ : syracuseStep 989165 = 370937) (by norm_num)
theorem B1316861 : Blo 583288 1316861 := bbase (se 3 (by rfl) ⟨246911, by rfl⟩ : syracuseStep 1316861 = 493823) (by norm_num)
theorem B1316933 : Blo 583288 1316933 := bbase (se 4 (by rfl) ⟨123462, by rfl⟩ : syracuseStep 1316933 = 246925) (by norm_num)
theorem B1480781 : Blo 583288 1480781 := bbase (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) (by norm_num)
theorem B2955365 : Blo 583288 2955365 := bbase (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) (by norm_num)
theorem B989293 : Blo 583288 989293 := bbase (se 3 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 989293 = 370985) (by norm_num)
theorem B2136181 : Blo 583288 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B1317005 : Blo 583288 1317005 := bbase (se 3 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 1317005 = 493877) (by norm_num)
theorem B989381 : Blo 583288 989381 := bbase (se 4 (by rfl) ⟨92754, by rfl⟩ : syracuseStep 989381 = 185509) (by norm_num)
theorem B1054925 : Blo 583288 1054925 := bbase (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) (by norm_num)
theorem B1317077 : Blo 583288 1317077 := bbase (se 7 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 1317077 = 30869) (by norm_num)
theorem B1317149 : Blo 583288 1317149 := bbase (se 3 (by rfl) ⟨246965, by rfl⟩ : syracuseStep 1317149 = 493931) (by norm_num)
theorem B989509 : Blo 583288 989509 := bbase (se 4 (by rfl) ⟨92766, by rfl⟩ : syracuseStep 989509 = 185533) (by norm_num)
theorem B1972565 : Blo 583288 1972565 := bbase (se 10 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 1972565 = 5779) (by norm_num)
theorem B1317221 : Blo 583288 1317221 := bbase (se 4 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 1317221 = 246979) (by norm_num)
theorem B989597 : Blo 583288 989597 := bbase (se 3 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 989597 = 371099) (by norm_num)
theorem B1481125 : Blo 583288 1481125 := bbase (se 4 (by rfl) ⟨138855, by rfl⟩ : syracuseStep 1481125 = 277711) (by norm_num)
theorem B1317293 : Blo 583288 1317293 := bbase (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) (by norm_num)
theorem B1317365 : Blo 583288 1317365 := bbase (se 5 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 1317365 = 123503) (by norm_num)
theorem B1251845 : Blo 583288 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B1481237 : Blo 583288 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B989725 : Blo 583288 989725 := bbase (se 3 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 989725 = 371147) (by norm_num)
theorem B1317437 : Blo 583288 1317437 := bbase (se 3 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 1317437 = 494039) (by norm_num)
theorem B989813 : Blo 583288 989813 := bbase (se 5 (by rfl) ⟨46397, by rfl⟩ : syracuseStep 989813 = 92795) (by norm_num)
theorem B1317509 : Blo 583288 1317509 := bbase (se 4 (by rfl) ⟨123516, by rfl⟩ : syracuseStep 1317509 = 247033) (by norm_num)
theorem B1317581 : Blo 583288 1317581 := bbase (se 3 (by rfl) ⟨247046, by rfl⟩ : syracuseStep 1317581 = 494093) (by norm_num)
theorem B1481429 : Blo 583288 1481429 := bbase (se 7 (by rfl) ⟨17360, by rfl⟩ : syracuseStep 1481429 = 34721) (by norm_num)
theorem B989941 : Blo 583288 989941 := bbase (se 5 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 989941 = 92807) (by norm_num)
theorem B1972997 : Blo 583288 1972997 := bbase (se 4 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 1972997 = 369937) (by norm_num)
theorem B1317653 : Blo 583288 1317653 := bbase (se 6 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 1317653 = 61765) (by norm_num)
theorem B990029 : Blo 583288 990029 := bbase (se 3 (by rfl) ⟨185630, by rfl⟩ : syracuseStep 990029 = 371261) (by norm_num)
theorem B1317725 : Blo 583288 1317725 := bbase (se 3 (by rfl) ⟨247073, by rfl⟩ : syracuseStep 1317725 = 494147) (by norm_num)
theorem B1317797 : Blo 583288 1317797 := bbase (se 4 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 1317797 = 247087) (by norm_num)
theorem B990157 : Blo 583288 990157 := bbase (se 3 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 990157 = 371309) (by norm_num)
theorem B1317869 : Blo 583288 1317869 := bbase (se 3 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 1317869 = 494201) (by norm_num)
theorem B990245 : Blo 583288 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B1481773 : Blo 583288 1481773 := bbase (se 3 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 1481773 = 555665) (by norm_num)
theorem B2104373 : Blo 583288 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B1317941 : Blo 583288 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B1318013 : Blo 583288 1318013 := bbase (se 3 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 1318013 = 494255) (by norm_num)
theorem B1481885 : Blo 583288 1481885 := bbase (se 3 (by rfl) ⟨277853, by rfl⟩ : syracuseStep 1481885 = 555707) (by norm_num)
theorem B990373 : Blo 583288 990373 := bbase (se 4 (by rfl) ⟨92847, by rfl⟩ : syracuseStep 990373 = 185695) (by norm_num)
theorem B1973429 : Blo 583288 1973429 := bbase (se 5 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 1973429 = 185009) (by norm_num)
theorem B1318085 : Blo 583288 1318085 := bbase (se 4 (by rfl) ⟨123570, by rfl⟩ : syracuseStep 1318085 = 247141) (by norm_num)
theorem B1252597 : Blo 583288 1252597 := bbase (se 5 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 1252597 = 117431) (by norm_num)
theorem B990461 : Blo 583288 990461 := bbase (se 3 (by rfl) ⟨185711, by rfl⟩ : syracuseStep 990461 = 371423) (by norm_num)
theorem B1318157 : Blo 583288 1318157 := bbase (se 3 (by rfl) ⟨247154, by rfl⟩ : syracuseStep 1318157 = 494309) (by norm_num)
theorem B1187149 : Blo 583288 1187149 := bbase (se 3 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 1187149 = 445181) (by norm_num)
theorem B1318229 : Blo 583288 1318229 := bbase (se 11 (by rfl) ⟨965, by rfl⟩ : syracuseStep 1318229 = 1931) (by norm_num)
theorem B1482077 : Blo 583288 1482077 := bbase (se 3 (by rfl) ⟨277889, by rfl⟩ : syracuseStep 1482077 = 555779) (by norm_num)
theorem B2956661 : Blo 583288 2956661 := bbase (se 5 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 2956661 = 277187) (by norm_num)
theorem B990589 : Blo 583288 990589 := bbase (se 3 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 990589 = 371471) (by norm_num)
theorem B1252741 : Blo 583288 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B1318301 : Blo 583288 1318301 := bbase (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) (by norm_num)
theorem B1187245 : Blo 583288 1187245 := bbase (se 3 (by rfl) ⟨222608, by rfl⟩ : syracuseStep 1187245 = 445217) (by norm_num)
theorem B990677 : Blo 583288 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B2104805 : Blo 583288 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B1318373 : Blo 583288 1318373 := bbase (se 4 (by rfl) ⟨123597, by rfl⟩ : syracuseStep 1318373 = 247195) (by norm_num)
theorem B1318445 : Blo 583288 1318445 := bbase (se 3 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 1318445 = 494417) (by norm_num)
theorem B2367029 : Blo 583288 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B990805 : Blo 583288 990805 := bbase (se 8 (by rfl) ⟨5805, by rfl⟩ : syracuseStep 990805 = 11611) (by norm_num)
theorem B1973861 : Blo 583288 1973861 := bbase (se 4 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 1973861 = 370099) (by norm_num)
theorem B1318517 : Blo 583288 1318517 := bbase (se 5 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 1318517 = 123611) (by norm_num)
theorem B990893 : Blo 583288 990893 := bbase (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) (by norm_num)
theorem B1482421 : Blo 583288 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B1318589 : Blo 583288 1318589 := bbase (se 3 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 1318589 = 494471) (by norm_num)
theorem B1253117 : Blo 583288 1253117 := bbase (se 3 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 1253117 = 469919) (by norm_num)
theorem B1318661 : Blo 583288 1318661 := bbase (se 4 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 1318661 = 247249) (by norm_num)
theorem B1482533 : Blo 583288 1482533 := bbase (se 4 (by rfl) ⟨138987, by rfl⟩ : syracuseStep 1482533 = 277975) (by norm_num)
theorem B991021 : Blo 583288 991021 := bbase (se 3 (by rfl) ⟨185816, by rfl⟩ : syracuseStep 991021 = 371633) (by norm_num)
theorem B1318733 : Blo 583288 1318733 := bbase (se 3 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 1318733 = 494525) (by norm_num)
theorem B4988789 : Blo 583288 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B6004597 : Blo 583288 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B1318805 : Blo 583288 1318805 := bbase (se 6 (by rfl) ⟨30909, by rfl⟩ : syracuseStep 1318805 = 61819) (by norm_num)
theorem B1318877 : Blo 583288 1318877 := bbase (se 3 (by rfl) ⟨247289, by rfl⟩ : syracuseStep 1318877 = 494579) (by norm_num)
theorem B1482725 : Blo 583288 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B1974293 : Blo 583288 1974293 := bbase (se 6 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 1974293 = 92545) (by norm_num)
theorem B1318949 : Blo 583288 1318949 := bbase (se 4 (by rfl) ⟨123651, by rfl⟩ : syracuseStep 1318949 = 247303) (by norm_num)
theorem B1319021 : Blo 583288 1319021 := bbase (se 3 (by rfl) ⟨247316, by rfl⟩ : syracuseStep 1319021 = 494633) (by norm_num)
theorem B1253485 : Blo 583288 1253485 := bbase (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) (by norm_num)
theorem B1777781 : Blo 583288 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B1319093 : Blo 583288 1319093 := bbase (se 5 (by rfl) ⟨61832, by rfl⟩ : syracuseStep 1319093 = 123665) (by norm_num)
theorem B1319165 : Blo 583288 1319165 := bbase (se 3 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 1319165 = 494687) (by norm_num)
theorem B3744053 : Blo 583288 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B1483069 : Blo 583288 1483069 := bbase (se 3 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 1483069 = 556151) (by norm_num)
theorem B1319237 : Blo 583288 1319237 := bbase (se 4 (by rfl) ⟨123678, by rfl⟩ : syracuseStep 1319237 = 247357) (by norm_num)
theorem B1319309 : Blo 583288 1319309 := bbase (se 3 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 1319309 = 494741) (by norm_num)
theorem B1483181 : Blo 583288 1483181 := bbase (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) (by norm_num)
theorem B1974725 : Blo 583288 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1319381 : Blo 583288 1319381 := bbase (se 7 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 1319381 = 30923) (by norm_num)
theorem B1319453 : Blo 583288 1319453 := bbase (se 3 (by rfl) ⟨247397, by rfl⟩ : syracuseStep 1319453 = 494795) (by norm_num)
theorem B1188413 : Blo 583288 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B1876549 : Blo 583288 1876549 := bbase (se 4 (by rfl) ⟨175926, by rfl⟩ : syracuseStep 1876549 = 351853) (by norm_num)
theorem B1319525 : Blo 583288 1319525 := bbase (se 4 (by rfl) ⟨123705, by rfl⟩ : syracuseStep 1319525 = 247411) (by norm_num)
theorem B1483373 : Blo 583288 1483373 := bbase (se 3 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 1483373 = 556265) (by norm_num)
theorem B2957957 : Blo 583288 2957957 := bbase (se 4 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 2957957 = 554617) (by norm_num)
theorem B1319597 : Blo 583288 1319597 := bbase (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) (by norm_num)
theorem B1319669 : Blo 583288 1319669 := bbase (se 5 (by rfl) ⟨61859, by rfl⟩ : syracuseStep 1319669 = 123719) (by norm_num)
theorem B1057549 : Blo 583288 1057549 := bbase (se 3 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 1057549 = 396581) (by norm_num)
theorem B1319741 : Blo 583288 1319741 := bbase (se 3 (by rfl) ⟨247451, by rfl⟩ : syracuseStep 1319741 = 494903) (by norm_num)
theorem B1975157 : Blo 583288 1975157 := bbase (se 5 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 1975157 = 185171) (by norm_num)
theorem B1319813 : Blo 583288 1319813 := bbase (se 4 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 1319813 = 247465) (by norm_num)
theorem B1057693 : Blo 583288 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B1483717 : Blo 583288 1483717 := bbase (se 4 (by rfl) ⟨139098, by rfl⟩ : syracuseStep 1483717 = 278197) (by norm_num)
theorem B2171845 : Blo 583288 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B1319885 : Blo 583288 1319885 := bbase (se 3 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 1319885 = 494957) (by norm_num)
theorem B2106389 : Blo 583288 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B2499605 : Blo 583288 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B10298389 : Blo 583288 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B1319957 : Blo 583288 1319957 := bbase (se 6 (by rfl) ⟨30936, by rfl⟩ : syracuseStep 1319957 = 61873) (by norm_num)
theorem B1483829 : Blo 583288 1483829 := bbase (se 5 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 1483829 = 139109) (by norm_num)
theorem B1320029 : Blo 583288 1320029 := bbase (se 3 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 1320029 = 495011) (by norm_num)
theorem B631973 : Blo 583288 631973 := bbase (se 4 (by rfl) ⟨59247, by rfl⟩ : syracuseStep 631973 = 118495) (by norm_num)
theorem B1320101 : Blo 583288 1320101 := bbase (se 4 (by rfl) ⟨123759, by rfl⟩ : syracuseStep 1320101 = 247519) (by norm_num)
theorem B1320173 : Blo 583288 1320173 := bbase (se 3 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 1320173 = 495065) (by norm_num)
theorem B1582325 : Blo 583288 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B1484021 : Blo 583288 1484021 := bbase (se 5 (by rfl) ⟨69563, by rfl⟩ : syracuseStep 1484021 = 139127) (by norm_num)
theorem B1975589 : Blo 583288 1975589 := bbase (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) (by norm_num)
theorem B1320245 : Blo 583288 1320245 := bbase (se 5 (by rfl) ⟨61886, by rfl⟩ : syracuseStep 1320245 = 123773) (by norm_num)
theorem B1123661 : Blo 583288 1123661 := bbase (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) (by norm_num)
theorem B1320317 : Blo 583288 1320317 := bbase (se 3 (by rfl) ⟨247559, by rfl⟩ : syracuseStep 1320317 = 495119) (by norm_num)
theorem B4760981 : Blo 583288 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B1582517 : Blo 583288 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1320389 : Blo 583288 1320389 := bbase (se 4 (by rfl) ⟨123786, by rfl⟩ : syracuseStep 1320389 = 247573) (by norm_num)
theorem B1058269 : Blo 583288 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B1320461 : Blo 583288 1320461 := bbase (se 3 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 1320461 = 495173) (by norm_num)
theorem B665161 : Blo 583288 665161 := bbase (se 2 (by rfl) ⟨249435, by rfl⟩ : syracuseStep 665161 = 498871) (by norm_num)
theorem B1484365 : Blo 583288 1484365 := bbase (se 3 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 1484365 = 556637) (by norm_num)
theorem B1320533 : Blo 583288 1320533 := bbase (se 8 (by rfl) ⟨7737, by rfl⟩ : syracuseStep 1320533 = 15475) (by norm_num)
theorem B1320605 : Blo 583288 1320605 := bbase (se 3 (by rfl) ⟨247613, by rfl⟩ : syracuseStep 1320605 = 495227) (by norm_num)
theorem B1484477 : Blo 583288 1484477 := bbase (se 3 (by rfl) ⟨278339, by rfl⟩ : syracuseStep 1484477 = 556679) (by norm_num)
theorem B665281 : Blo 583288 665281 := bbase (se 2 (by rfl) ⟨249480, by rfl⟩ : syracuseStep 665281 = 498961) (by norm_num)
theorem B1976021 : Blo 583288 1976021 := bbase (se 7 (by rfl) ⟨23156, by rfl⟩ : syracuseStep 1976021 = 46313) (by norm_num)
theorem B1320677 : Blo 583288 1320677 := bbase (se 4 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 1320677 = 247627) (by norm_num)
theorem B1320749 : Blo 583288 1320749 := bbase (se 3 (by rfl) ⟨247640, by rfl⟩ : syracuseStep 1320749 = 495281) (by norm_num)
theorem B1320821 : Blo 583288 1320821 := bbase (se 5 (by rfl) ⟨61913, by rfl⟩ : syracuseStep 1320821 = 123827) (by norm_num)
theorem B1484669 : Blo 583288 1484669 := bbase (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) (by norm_num)
theorem B2369429 : Blo 583288 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B2959253 : Blo 583288 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B1288109 : Blo 583288 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1320893 : Blo 583288 1320893 := bbase (se 3 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 1320893 = 495335) (by norm_num)
theorem B1320965 : Blo 583288 1320965 := bbase (se 4 (by rfl) ⟨123840, by rfl⟩ : syracuseStep 1320965 = 247681) (by norm_num)
theorem B1779749 : Blo 583288 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B4499509 : Blo 583288 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B1321037 : Blo 583288 1321037 := bbase (se 3 (by rfl) ⟨247694, by rfl⟩ : syracuseStep 1321037 = 495389) (by norm_num)
theorem B665705 : Blo 583288 665705 := bbase (se 2 (by rfl) ⟨249639, by rfl⟩ : syracuseStep 665705 = 499279) (by norm_num)
theorem B1976453 : Blo 583288 1976453 := bbase (se 4 (by rfl) ⟨185292, by rfl⟩ : syracuseStep 1976453 = 370585) (by norm_num)
theorem B1321109 : Blo 583288 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B1485013 : Blo 583288 1485013 := bbase (se 7 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 1485013 = 34805) (by norm_num)
theorem B1321181 : Blo 583288 1321181 := bbase (se 3 (by rfl) ⟨247721, by rfl⟩ : syracuseStep 1321181 = 495443) (by norm_num)
theorem B1321253 : Blo 583288 1321253 := bbase (se 4 (by rfl) ⟨123867, by rfl⟩ : syracuseStep 1321253 = 247735) (by norm_num)
theorem B1485125 : Blo 583288 1485125 := bbase (se 4 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 1485125 = 278461) (by norm_num)
theorem B1321325 : Blo 583288 1321325 := bbase (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) (by norm_num)
theorem B1321397 : Blo 583288 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B1485317 : Blo 583288 1485317 := bbase (se 4 (by rfl) ⟨139248, by rfl⟩ : syracuseStep 1485317 = 278497) (by norm_num)
theorem B1976885 : Blo 583288 1976885 := bbase (se 5 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 1976885 = 185333) (by norm_num)
theorem B1780309 : Blo 583288 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B2894453 : Blo 583288 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B666289 : Blo 583288 666289 := bbase (se 2 (by rfl) ⟨249858, by rfl⟩ : syracuseStep 666289 = 499717) (by norm_num)
theorem B2501381 : Blo 583288 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B1485661 : Blo 583288 1485661 := bbase (se 3 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 1485661 = 557123) (by norm_num)
theorem B1485773 : Blo 583288 1485773 := bbase (se 3 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 1485773 = 557165) (by norm_num)
theorem B1977317 : Blo 583288 1977317 := bbase (se 4 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 1977317 = 370747) (by norm_num)
theorem B666749 : Blo 583288 666749 := bbase (se 3 (by rfl) ⟨125015, by rfl⟩ : syracuseStep 666749 = 250031) (by norm_num)
theorem B1485965 : Blo 583288 1485965 := bbase (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) (by norm_num)
theorem B2960549 : Blo 583288 2960549 := bbase (se 4 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 2960549 = 555103) (by norm_num)
theorem B830741 : Blo 583288 830741 := bbase (se 6 (by rfl) ⟨19470, by rfl⟩ : syracuseStep 830741 = 38941) (by norm_num)
theorem B1977749 : Blo 583288 1977749 := bbase (se 6 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 1977749 = 92707) (by norm_num)
theorem B1486309 : Blo 583288 1486309 := bbase (se 4 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 1486309 = 278683) (by norm_num)
theorem B1486421 : Blo 583288 1486421 := bbase (se 8 (by rfl) ⟨8709, by rfl⟩ : syracuseStep 1486421 = 17419) (by norm_num)
theorem B667297 : Blo 583288 667297 := bbase (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) (by norm_num)
theorem B2502373 : Blo 583288 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B1978181 : Blo 583288 1978181 := bbase (se 4 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 1978181 = 370909) (by norm_num)
theorem B7515989 : Blo 583288 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B831493 : Blo 583288 831493 := bbase (se 4 (by rfl) ⟨77952, by rfl⟩ : syracuseStep 831493 = 155905) (by norm_num)
theorem B1159373 : Blo 583288 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1978613 : Blo 583288 1978613 := bbase (se 5 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 1978613 = 185495) (by norm_num)
theorem B2961845 : Blo 583288 2961845 := bbase (se 5 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 2961845 = 277673) (by norm_num)
theorem B1979045 : Blo 583288 1979045 := bbase (se 4 (by rfl) ⟨185535, by rfl⟩ : syracuseStep 1979045 = 371071) (by norm_num)
theorem B4436693 : Blo 583288 4436693 := bbase (se 7 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 4436693 = 103985) (by norm_num)
theorem B832285 : Blo 583288 832285 := bbase (se 3 (by rfl) ⟨156053, by rfl⟩ : syracuseStep 832285 = 312107) (by norm_num)
theorem B668701 : Blo 583288 668701 := bbase (se 3 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 668701 = 250763) (by norm_num)
theorem B1979477 : Blo 583288 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B832621 : Blo 583288 832621 := bbase (se 3 (by rfl) ⟨156116, by rfl⟩ : syracuseStep 832621 = 312233) (by norm_num)
theorem B4568309 : Blo 583288 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B2667797 : Blo 583288 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B832837 : Blo 583288 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B5354869 : Blo 583288 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B701957 : Blo 583288 701957 := bbase (se 4 (by rfl) ⟨65808, by rfl⟩ : syracuseStep 701957 = 131617) (by norm_num)
theorem B1979909 : Blo 583288 1979909 := bbase (se 4 (by rfl) ⟨185616, by rfl⟩ : syracuseStep 1979909 = 371233) (by norm_num)
theorem B833213 : Blo 583288 833213 := bbase (se 3 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 833213 = 312455) (by norm_num)
theorem B1128125 : Blo 583288 1128125 := bbase (se 3 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 1128125 = 423047) (by norm_num)
theorem B2963141 : Blo 583288 2963141 := bbase (se 4 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 2963141 = 555589) (by norm_num)
theorem B702217 : Blo 583288 702217 := bbase (se 2 (by rfl) ⟨263331, by rfl⟩ : syracuseStep 702217 = 526663) (by norm_num)
theorem B702265 : Blo 583288 702265 := bbase (se 2 (by rfl) ⟨263349, by rfl⟩ : syracuseStep 702265 = 526699) (by norm_num)
theorem B669541 : Blo 583288 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B1980341 : Blo 583288 1980341 := bbase (se 5 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 1980341 = 185657) (by norm_num)
theorem B3324149 : Blo 583288 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B1980773 : Blo 583288 1980773 := bbase (se 4 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 1980773 = 371395) (by norm_num)
theorem B1849717 : Blo 583288 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B702937 : Blo 583288 702937 := bbase (se 2 (by rfl) ⟨263601, by rfl⟩ : syracuseStep 702937 = 527203) (by norm_num)
theorem B2112101 : Blo 583288 2112101 := bbase (se 4 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 2112101 = 396019) (by norm_num)
theorem B1981205 : Blo 583288 1981205 := bbase (se 6 (by rfl) ⟨46434, by rfl⟩ : syracuseStep 1981205 = 92869) (by norm_num)
theorem B1424269 : Blo 583288 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B2702261 : Blo 583288 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B2964437 : Blo 583288 2964437 := bbase (se 7 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 2964437 = 69479) (by norm_num)
theorem B1621061 : Blo 583288 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B834637 : Blo 583288 834637 := bbase (se 3 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 834637 = 312989) (by norm_num)
theorem B1981637 : Blo 583288 1981637 := bbase (se 4 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 1981637 = 371557) (by norm_num)
theorem B3325333 : Blo 583288 3325333 := bbase (se 6 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 3325333 = 155875) (by norm_num)
theorem B703937 : Blo 583288 703937 := bbase (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) (by norm_num)
theorem B2112965 : Blo 583288 2112965 := bbase (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) (by norm_num)
theorem B2375173 : Blo 583288 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B704009 : Blo 583288 704009 := bbase (se 2 (by rfl) ⟨264003, by rfl⟩ : syracuseStep 704009 = 528007) (by norm_num)
theorem B1982069 : Blo 583288 1982069 := bbase (se 5 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 1982069 = 185819) (by norm_num)
theorem B835229 : Blo 583288 835229 := bbase (se 3 (by rfl) ⟨156605, by rfl⟩ : syracuseStep 835229 = 313211) (by norm_num)
theorem B2375333 : Blo 583288 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B2113253 : Blo 583288 2113253 := bbase (se 4 (by rfl) ⟨198117, by rfl⟩ : syracuseStep 2113253 = 396235) (by norm_num)
theorem B835309 : Blo 583288 835309 := bbase (se 3 (by rfl) ⟨156620, by rfl⟩ : syracuseStep 835309 = 313241) (by norm_num)
theorem B704317 : Blo 583288 704317 := bbase (se 3 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 704317 = 264119) (by norm_num)
theorem B835429 : Blo 583288 835429 := bbase (se 4 (by rfl) ⟨78321, by rfl⟩ : syracuseStep 835429 = 156643) (by norm_num)
theorem B835525 : Blo 583288 835525 := bbase (se 4 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 835525 = 156661) (by norm_num)
theorem B704485 : Blo 583288 704485 := bbase (se 4 (by rfl) ⟨66045, by rfl⟩ : syracuseStep 704485 = 132091) (by norm_num)
theorem B704533 : Blo 583288 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B704629 : Blo 583288 704629 := bbase (se 5 (by rfl) ⟨33029, by rfl⟩ : syracuseStep 704629 = 66059) (by norm_num)
theorem B2113685 : Blo 583288 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B2965733 : Blo 583288 2965733 := bbase (se 4 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 2965733 = 556075) (by norm_num)
theorem B3555701 : Blo 583288 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B836021 : Blo 583288 836021 := bbase (se 5 (by rfl) ⟨39188, by rfl⟩ : syracuseStep 836021 = 78377) (by norm_num)
theorem B10961365 : Blo 583288 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B934373 : Blo 583288 934373 := bbase (se 4 (by rfl) ⟨87597, by rfl⟩ : syracuseStep 934373 = 175195) (by norm_num)
theorem B2507381 : Blo 583288 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B705205 : Blo 583288 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B934789 : Blo 583288 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B1524629 : Blo 583288 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B2507669 : Blo 583288 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B738229 : Blo 583288 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B738325 : Blo 583288 738325 := bbase (se 6 (by rfl) ⟨17304, by rfl⟩ : syracuseStep 738325 = 34609) (by norm_num)
theorem B1000549 : Blo 583288 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B738497 : Blo 583288 738497 := bbase (se 2 (by rfl) ⟨276936, by rfl⟩ : syracuseStep 738497 = 553873) (by norm_num)
theorem B1262837 : Blo 583288 1262837 := bbase (se 5 (by rfl) ⟨59195, by rfl⟩ : syracuseStep 1262837 = 118391) (by norm_num)
theorem B738553 : Blo 583288 738553 := bbase (se 2 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 738553 = 553915) (by norm_num)
theorem B3327317 : Blo 583288 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B738649 : Blo 583288 738649 := bbase (se 2 (by rfl) ⟨276993, by rfl⟩ : syracuseStep 738649 = 553987) (by norm_num)
theorem B2967029 : Blo 583288 2967029 := bbase (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) (by norm_num)
theorem B738821 : Blo 583288 738821 := bbase (se 4 (by rfl) ⟨69264, by rfl⟩ : syracuseStep 738821 = 138529) (by norm_num)
theorem B738877 : Blo 583288 738877 := bbase (se 3 (by rfl) ⟨138539, by rfl⟩ : syracuseStep 738877 = 277079) (by norm_num)
theorem B2508421 : Blo 583288 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B738973 : Blo 583288 738973 := bbase (se 3 (by rfl) ⟨138557, by rfl⟩ : syracuseStep 738973 = 277115) (by norm_num)
theorem B935725 : Blo 583288 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B739145 : Blo 583288 739145 := bbase (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) (by norm_num)
theorem B739201 : Blo 583288 739201 := bbase (se 2 (by rfl) ⟨277200, by rfl⟩ : syracuseStep 739201 = 554401) (by norm_num)
theorem B739297 : Blo 583288 739297 := bbase (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) (by norm_num)
theorem B739469 : Blo 583288 739469 := bbase (se 3 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 739469 = 277301) (by norm_num)
theorem B739525 : Blo 583288 739525 := bbase (se 4 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 739525 = 138661) (by norm_num)
theorem B739621 : Blo 583288 739621 := bbase (se 4 (by rfl) ⟨69339, by rfl⟩ : syracuseStep 739621 = 138679) (by norm_num)
theorem B2115877 : Blo 583288 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B739793 : Blo 583288 739793 := bbase (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) (by norm_num)
theorem B2804213 : Blo 583288 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B739849 : Blo 583288 739849 := bbase (se 2 (by rfl) ⟨277443, by rfl⟩ : syracuseStep 739849 = 554887) (by norm_num)
theorem B1526293 : Blo 583288 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B739945 : Blo 583288 739945 := bbase (se 2 (by rfl) ⟨277479, by rfl⟩ : syracuseStep 739945 = 554959) (by norm_num)
theorem B2968325 : Blo 583288 2968325 := bbase (se 4 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 2968325 = 556561) (by norm_num)
theorem B740117 : Blo 583288 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B740173 : Blo 583288 740173 := bbase (se 3 (by rfl) ⟨138782, by rfl⟩ : syracuseStep 740173 = 277565) (by norm_num)
theorem B1002341 : Blo 583288 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B740269 : Blo 583288 740269 := bbase (se 3 (by rfl) ⟨138800, by rfl⟩ : syracuseStep 740269 = 277601) (by norm_num)
theorem B936917 : Blo 583288 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B3754997 : Blo 583288 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B740441 : Blo 583288 740441 := bbase (se 2 (by rfl) ⟨277665, by rfl⟩ : syracuseStep 740441 = 555331) (by norm_num)
theorem B740497 : Blo 583288 740497 := bbase (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) (by norm_num)
theorem B937109 : Blo 583288 937109 := bbase (se 6 (by rfl) ⟨21963, by rfl⟩ : syracuseStep 937109 = 43927) (by norm_num)
theorem B740593 : Blo 583288 740593 := bbase (se 2 (by rfl) ⟨277722, by rfl⟩ : syracuseStep 740593 = 555445) (by norm_num)
theorem B2379029 : Blo 583288 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B10833301 : Blo 583288 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B740765 : Blo 583288 740765 := bbase (se 3 (by rfl) ⟨138893, by rfl⟩ : syracuseStep 740765 = 277787) (by norm_num)
theorem B1527229 : Blo 583288 1527229 := bbase (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) (by norm_num)
theorem B740821 : Blo 583288 740821 := bbase (se 7 (by rfl) ⟨8681, by rfl⟩ : syracuseStep 740821 = 17363) (by norm_num)
theorem B3329525 : Blo 583288 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B740917 : Blo 583288 740917 := bbase (se 5 (by rfl) ⟨34730, by rfl⟩ : syracuseStep 740917 = 69461) (by norm_num)
theorem B675541 : Blo 583288 675541 := bbase (se 7 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 675541 = 15833) (by norm_num)
theorem B8113877 : Blo 583288 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B741089 : Blo 583288 741089 := bbase (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) (by norm_num)
theorem B741145 : Blo 583288 741145 := bbase (se 2 (by rfl) ⟨277929, by rfl⟩ : syracuseStep 741145 = 555859) (by norm_num)
theorem B642853 : Blo 583288 642853 := bbase (se 4 (by rfl) ⟨60267, by rfl⟩ : syracuseStep 642853 = 120535) (by norm_num)
theorem B2215781 : Blo 583288 2215781 := bbase (se 4 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 2215781 = 415459) (by norm_num)
theorem B741241 : Blo 583288 741241 := bbase (se 2 (by rfl) ⟨277965, by rfl⟩ : syracuseStep 741241 = 555931) (by norm_num)
theorem B2805637 : Blo 583288 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B2969621 : Blo 583288 2969621 := bbase (se 6 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 2969621 = 139201) (by norm_num)
theorem B741413 : Blo 583288 741413 := bbase (se 4 (by rfl) ⟨69507, by rfl⟩ : syracuseStep 741413 = 139015) (by norm_num)
theorem B741469 : Blo 583288 741469 := bbase (se 3 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 741469 = 278051) (by norm_num)
theorem B2216069 : Blo 583288 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B741565 : Blo 583288 741565 := bbase (se 3 (by rfl) ⟨139043, by rfl⟩ : syracuseStep 741565 = 278087) (by norm_num)
theorem B1331437 : Blo 583288 1331437 := bbase (se 3 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 1331437 = 499289) (by norm_num)
theorem B2674949 : Blo 583288 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B4444469 : Blo 583288 4444469 := bbase (se 5 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 4444469 = 416669) (by norm_num)
theorem B741737 : Blo 583288 741737 := bbase (se 2 (by rfl) ⟨278151, by rfl⟩ : syracuseStep 741737 = 556303) (by norm_num)
theorem B741793 : Blo 583288 741793 := bbase (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) (by norm_num)
theorem B741889 : Blo 583288 741889 := bbase (se 2 (by rfl) ⟨278208, by rfl⟩ : syracuseStep 741889 = 556417) (by norm_num)
theorem B938557 : Blo 583288 938557 := bbase (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) (by norm_num)
theorem B742061 : Blo 583288 742061 := bbase (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) (by norm_num)
theorem B742117 : Blo 583288 742117 := bbase (se 4 (by rfl) ⟨69573, by rfl⟩ : syracuseStep 742117 = 139147) (by norm_num)
theorem B2577125 : Blo 583288 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B742213 : Blo 583288 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B1004365 : Blo 583288 1004365 := bbase (se 3 (by rfl) ⟨188318, by rfl⟩ : syracuseStep 1004365 = 376637) (by norm_num)
theorem B7131989 : Blo 583288 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B742385 : Blo 583288 742385 := bbase (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) (by norm_num)
theorem B2675717 : Blo 583288 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B742441 : Blo 583288 742441 := bbase (se 2 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 742441 = 556831) (by norm_num)
theorem B2249845 : Blo 583288 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B742537 : Blo 583288 742537 := bbase (se 2 (by rfl) ⟨278451, by rfl⟩ : syracuseStep 742537 = 556903) (by norm_num)
theorem B2217253 : Blo 583288 2217253 := bbase (se 4 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 2217253 = 415735) (by norm_num)
theorem B2970917 : Blo 583288 2970917 := bbase (se 4 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 2970917 = 557047) (by norm_num)
theorem B742709 : Blo 583288 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B742765 : Blo 583288 742765 := bbase (se 3 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 742765 = 278537) (by norm_num)
theorem B677233 : Blo 583288 677233 := bbase (se 2 (by rfl) ⟨253962, by rfl⟩ : syracuseStep 677233 = 507925) (by norm_num)
theorem B742861 : Blo 583288 742861 := bbase (se 3 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 742861 = 278573) (by norm_num)
theorem B2217557 : Blo 583288 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B743033 : Blo 583288 743033 := bbase (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) (by norm_num)
theorem B743089 : Blo 583288 743089 := bbase (se 2 (by rfl) ⟨278658, by rfl⟩ : syracuseStep 743089 = 557317) (by norm_num)
theorem B743185 : Blo 583288 743185 := bbase (se 2 (by rfl) ⟨278694, by rfl⟩ : syracuseStep 743185 = 557389) (by norm_num)
theorem B939941 : Blo 583288 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B22763477 : Blo 583288 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B940133 : Blo 583288 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B1661141 : Blo 583288 1661141 := bbase (se 7 (by rfl) ⟨19466, by rfl⟩ : syracuseStep 1661141 = 38933) (by norm_num)
theorem B874949 : Blo 583288 874949 := bbase (se 4 (by rfl) ⟨82026, by rfl⟩ : syracuseStep 874949 = 164053) (by norm_num)
theorem B1661381 : Blo 583288 1661381 := bbase (se 4 (by rfl) ⟨155754, by rfl⟩ : syracuseStep 1661381 = 311509) (by norm_num)
theorem B874973 : Blo 583288 874973 := bbase (se 3 (by rfl) ⟨164057, by rfl⟩ : syracuseStep 874973 = 328115) (by norm_num)
theorem B874997 : Blo 583288 874997 := bbase (se 5 (by rfl) ⟨41015, by rfl⟩ : syracuseStep 874997 = 82031) (by norm_num)
theorem B875021 : Blo 583288 875021 := bbase (se 3 (by rfl) ⟨164066, by rfl⟩ : syracuseStep 875021 = 328133) (by norm_num)
theorem B875045 : Blo 583288 875045 := bbase (se 4 (by rfl) ⟨82035, by rfl⟩ : syracuseStep 875045 = 164071) (by norm_num)
theorem B5626421 : Blo 583288 5626421 := bbase (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) (by norm_num)
theorem B2972213 : Blo 583288 2972213 := bbase (se 5 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 2972213 = 278645) (by norm_num)
theorem B875069 : Blo 583288 875069 := bbase (se 3 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 875069 = 328151) (by norm_num)
theorem B875093 : Blo 583288 875093 := bbase (se 8 (by rfl) ⟨5127, by rfl⟩ : syracuseStep 875093 = 10255) (by norm_num)
theorem B875117 : Blo 583288 875117 := bbase (se 3 (by rfl) ⟨164084, by rfl⟩ : syracuseStep 875117 = 328169) (by norm_num)
theorem B875141 : Blo 583288 875141 := bbase (se 4 (by rfl) ⟨82044, by rfl⟩ : syracuseStep 875141 = 164089) (by norm_num)
theorem B1661573 : Blo 583288 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B875165 : Blo 583288 875165 := bbase (se 3 (by rfl) ⟨164093, by rfl⟩ : syracuseStep 875165 = 328187) (by norm_num)
theorem B875189 : Blo 583288 875189 := bbase (se 5 (by rfl) ⟨41024, by rfl⟩ : syracuseStep 875189 = 82049) (by norm_num)
theorem B875213 : Blo 583288 875213 := bbase (se 3 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 875213 = 328205) (by norm_num)
theorem B875237 : Blo 583288 875237 := bbase (se 4 (by rfl) ⟨82053, by rfl⟩ : syracuseStep 875237 = 164107) (by norm_num)
theorem B875261 : Blo 583288 875261 := bbase (se 3 (by rfl) ⟨164111, by rfl⟩ : syracuseStep 875261 = 328223) (by norm_num)
theorem B875285 : Blo 583288 875285 := bbase (se 6 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 875285 = 41029) (by norm_num)
theorem B875309 : Blo 583288 875309 := bbase (se 3 (by rfl) ⟨164120, by rfl⟩ : syracuseStep 875309 = 328241) (by norm_num)
theorem B875333 : Blo 583288 875333 := bbase (se 4 (by rfl) ⟨82062, by rfl⟩ : syracuseStep 875333 = 164125) (by norm_num)
theorem B875357 : Blo 583288 875357 := bbase (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) (by norm_num)
theorem B875381 : Blo 583288 875381 := bbase (se 5 (by rfl) ⟨41033, by rfl⟩ : syracuseStep 875381 = 82067) (by norm_num)
theorem B875405 : Blo 583288 875405 := bbase (se 3 (by rfl) ⟨164138, by rfl⟩ : syracuseStep 875405 = 328277) (by norm_num)
theorem B875429 : Blo 583288 875429 := bbase (se 4 (by rfl) ⟨82071, by rfl⟩ : syracuseStep 875429 = 164143) (by norm_num)
theorem B875453 : Blo 583288 875453 := bbase (se 3 (by rfl) ⟨164147, by rfl⟩ : syracuseStep 875453 = 328295) (by norm_num)
theorem B875477 : Blo 583288 875477 := bbase (se 7 (by rfl) ⟨10259, by rfl⟩ : syracuseStep 875477 = 20519) (by norm_num)
theorem B875501 : Blo 583288 875501 := bbase (se 3 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 875501 = 328313) (by norm_num)
theorem B875525 : Blo 583288 875525 := bbase (se 4 (by rfl) ⟨82080, by rfl⟩ : syracuseStep 875525 = 164161) (by norm_num)
theorem B875549 : Blo 583288 875549 := bbase (se 3 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 875549 = 328331) (by norm_num)
theorem B875573 : Blo 583288 875573 := bbase (se 5 (by rfl) ⟨41042, by rfl⟩ : syracuseStep 875573 = 82085) (by norm_num)
theorem B875597 : Blo 583288 875597 := bbase (se 3 (by rfl) ⟨164174, by rfl⟩ : syracuseStep 875597 = 328349) (by norm_num)
theorem B5069909 : Blo 583288 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B875621 : Blo 583288 875621 := bbase (se 4 (by rfl) ⟨82089, by rfl⟩ : syracuseStep 875621 = 164179) (by norm_num)
theorem B3562613 : Blo 583288 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B875645 : Blo 583288 875645 := bbase (se 3 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 875645 = 328367) (by norm_num)
theorem B875669 : Blo 583288 875669 := bbase (se 6 (by rfl) ⟨20523, by rfl⟩ : syracuseStep 875669 = 41047) (by norm_num)
theorem B875693 : Blo 583288 875693 := bbase (se 3 (by rfl) ⟨164192, by rfl⟩ : syracuseStep 875693 = 328385) (by norm_num)
theorem B875717 : Blo 583288 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B875741 : Blo 583288 875741 := bbase (se 3 (by rfl) ⟨164201, by rfl⟩ : syracuseStep 875741 = 328403) (by norm_num)
theorem B875765 : Blo 583288 875765 := bbase (se 5 (by rfl) ⟨41051, by rfl⟩ : syracuseStep 875765 = 82103) (by norm_num)
theorem B875789 : Blo 583288 875789 := bbase (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) (by norm_num)
theorem B875813 : Blo 583288 875813 := bbase (se 4 (by rfl) ⟨82107, by rfl⟩ : syracuseStep 875813 = 164215) (by norm_num)
theorem B875837 : Blo 583288 875837 := bbase (se 3 (by rfl) ⟨164219, by rfl⟩ : syracuseStep 875837 = 328439) (by norm_num)
theorem B875861 : Blo 583288 875861 := bbase (se 11 (by rfl) ⟨641, by rfl⟩ : syracuseStep 875861 = 1283) (by norm_num)
theorem B875885 : Blo 583288 875885 := bbase (se 3 (by rfl) ⟨164228, by rfl⟩ : syracuseStep 875885 = 328457) (by norm_num)
theorem B875909 : Blo 583288 875909 := bbase (se 4 (by rfl) ⟨82116, by rfl⟩ : syracuseStep 875909 = 164233) (by norm_num)
theorem B875933 : Blo 583288 875933 := bbase (se 3 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 875933 = 328475) (by norm_num)
theorem B1334701 : Blo 583288 1334701 := bbase (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) (by norm_num)
theorem B875957 : Blo 583288 875957 := bbase (se 5 (by rfl) ⟨41060, by rfl⟩ : syracuseStep 875957 = 82121) (by norm_num)
theorem B875981 : Blo 583288 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B876005 : Blo 583288 876005 := bbase (se 4 (by rfl) ⟨82125, by rfl⟩ : syracuseStep 876005 = 164251) (by norm_num)
theorem B876029 : Blo 583288 876029 := bbase (se 3 (by rfl) ⟨164255, by rfl⟩ : syracuseStep 876029 = 328511) (by norm_num)
theorem B876053 : Blo 583288 876053 := bbase (se 6 (by rfl) ⟨20532, by rfl⟩ : syracuseStep 876053 = 41065) (by norm_num)
theorem B876077 : Blo 583288 876077 := bbase (se 3 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 876077 = 328529) (by norm_num)
theorem B876101 : Blo 583288 876101 := bbase (se 4 (by rfl) ⟨82134, by rfl⟩ : syracuseStep 876101 = 164269) (by norm_num)
theorem B876125 : Blo 583288 876125 := bbase (se 3 (by rfl) ⟨164273, by rfl⟩ : syracuseStep 876125 = 328547) (by norm_num)
theorem B1662565 : Blo 583288 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B876149 : Blo 583288 876149 := bbase (se 5 (by rfl) ⟨41069, by rfl⟩ : syracuseStep 876149 = 82139) (by norm_num)
theorem B876173 : Blo 583288 876173 := bbase (se 3 (by rfl) ⟨164282, by rfl⟩ : syracuseStep 876173 = 328565) (by norm_num)
theorem B2219669 : Blo 583288 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B5004949 : Blo 583288 5004949 := bbase (se 6 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 5004949 = 234607) (by norm_num)
theorem B876197 : Blo 583288 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B876221 : Blo 583288 876221 := bbase (se 3 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 876221 = 328583) (by norm_num)
theorem B876245 : Blo 583288 876245 := bbase (se 7 (by rfl) ⟨10268, by rfl⟩ : syracuseStep 876245 = 20537) (by norm_num)
theorem B6676181 : Blo 583288 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B876269 : Blo 583288 876269 := bbase (se 3 (by rfl) ⟨164300, by rfl⟩ : syracuseStep 876269 = 328601) (by norm_num)
theorem B876293 : Blo 583288 876293 := bbase (se 4 (by rfl) ⟨82152, by rfl⟩ : syracuseStep 876293 = 164305) (by norm_num)
theorem B876317 : Blo 583288 876317 := bbase (se 3 (by rfl) ⟨164309, by rfl⟩ : syracuseStep 876317 = 328619) (by norm_num)
theorem B876341 : Blo 583288 876341 := bbase (se 5 (by rfl) ⟨41078, by rfl⟩ : syracuseStep 876341 = 82157) (by norm_num)
theorem B876365 : Blo 583288 876365 := bbase (se 3 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 876365 = 328637) (by norm_num)
theorem B876389 : Blo 583288 876389 := bbase (se 4 (by rfl) ⟨82161, by rfl⟩ : syracuseStep 876389 = 164323) (by norm_num)
theorem B876413 : Blo 583288 876413 := bbase (se 3 (by rfl) ⟨164327, by rfl⟩ : syracuseStep 876413 = 328655) (by norm_num)
theorem B876437 : Blo 583288 876437 := bbase (se 6 (by rfl) ⟨20541, by rfl⟩ : syracuseStep 876437 = 41083) (by norm_num)
theorem B1269661 : Blo 583288 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B876461 : Blo 583288 876461 := bbase (se 3 (by rfl) ⟨164336, by rfl⟩ : syracuseStep 876461 = 328673) (by norm_num)
theorem B2219957 : Blo 583288 2219957 := bbase (se 5 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 2219957 = 208121) (by norm_num)
theorem B876485 : Blo 583288 876485 := bbase (se 4 (by rfl) ⟨82170, by rfl⟩ : syracuseStep 876485 = 164341) (by norm_num)
theorem B876509 : Blo 583288 876509 := bbase (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) (by norm_num)
theorem B876533 : Blo 583288 876533 := bbase (se 5 (by rfl) ⟨41087, by rfl⟩ : syracuseStep 876533 = 82175) (by norm_num)
theorem B876557 : Blo 583288 876557 := bbase (se 3 (by rfl) ⟨164354, by rfl⟩ : syracuseStep 876557 = 328709) (by norm_num)
theorem B876581 : Blo 583288 876581 := bbase (se 4 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 876581 = 164359) (by norm_num)
theorem B876605 : Blo 583288 876605 := bbase (se 3 (by rfl) ⟨164363, by rfl⟩ : syracuseStep 876605 = 328727) (by norm_num)
theorem B876629 : Blo 583288 876629 := bbase (se 8 (by rfl) ⟨5136, by rfl⟩ : syracuseStep 876629 = 10273) (by norm_num)
theorem B712801 : Blo 583288 712801 := bbase (se 2 (by rfl) ⟨267300, by rfl⟩ : syracuseStep 712801 = 534601) (by norm_num)
theorem B876653 : Blo 583288 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B876677 : Blo 583288 876677 := bbase (se 4 (by rfl) ⟨82188, by rfl⟩ : syracuseStep 876677 = 164377) (by norm_num)
theorem B712837 : Blo 583288 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B876701 : Blo 583288 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B876725 : Blo 583288 876725 := bbase (se 5 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 876725 = 82193) (by norm_num)
theorem B876749 : Blo 583288 876749 := bbase (se 3 (by rfl) ⟨164390, by rfl⟩ : syracuseStep 876749 = 328781) (by norm_num)
theorem B876773 : Blo 583288 876773 := bbase (se 4 (by rfl) ⟨82197, by rfl⟩ : syracuseStep 876773 = 164395) (by norm_num)
theorem B876797 : Blo 583288 876797 := bbase (se 3 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 876797 = 328799) (by norm_num)
theorem B876821 : Blo 583288 876821 := bbase (se 6 (by rfl) ⟨20550, by rfl⟩ : syracuseStep 876821 = 41101) (by norm_num)
theorem B876845 : Blo 583288 876845 := bbase (se 3 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 876845 = 328817) (by norm_num)
theorem B876869 : Blo 583288 876869 := bbase (se 4 (by rfl) ⟨82206, by rfl⟩ : syracuseStep 876869 = 164413) (by norm_num)
theorem B876893 : Blo 583288 876893 := bbase (se 3 (by rfl) ⟨164417, by rfl⟩ : syracuseStep 876893 = 328835) (by norm_num)
theorem B876917 : Blo 583288 876917 := bbase (se 5 (by rfl) ⟨41105, by rfl⟩ : syracuseStep 876917 = 82211) (by norm_num)
theorem B876941 : Blo 583288 876941 := bbase (se 3 (by rfl) ⟨164426, by rfl⟩ : syracuseStep 876941 = 328853) (by norm_num)
theorem B876965 : Blo 583288 876965 := bbase (se 4 (by rfl) ⟨82215, by rfl⟩ : syracuseStep 876965 = 164431) (by norm_num)
theorem B876989 : Blo 583288 876989 := bbase (se 3 (by rfl) ⟨164435, by rfl⟩ : syracuseStep 876989 = 328871) (by norm_num)
theorem B877013 : Blo 583288 877013 := bbase (se 7 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 877013 = 20555) (by norm_num)
theorem B877037 : Blo 583288 877037 := bbase (se 3 (by rfl) ⟨164444, by rfl⟩ : syracuseStep 877037 = 328889) (by norm_num)
theorem B877061 : Blo 583288 877061 := bbase (se 4 (by rfl) ⟨82224, by rfl⟩ : syracuseStep 877061 = 164449) (by norm_num)
theorem B877085 : Blo 583288 877085 := bbase (se 3 (by rfl) ⟨164453, by rfl⟩ : syracuseStep 877085 = 328907) (by norm_num)
theorem B877109 : Blo 583288 877109 := bbase (se 5 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 877109 = 82229) (by norm_num)
theorem B877133 : Blo 583288 877133 := bbase (se 3 (by rfl) ⟨164462, by rfl⟩ : syracuseStep 877133 = 328925) (by norm_num)
theorem B877157 : Blo 583288 877157 := bbase (se 4 (by rfl) ⟨82233, by rfl⟩ : syracuseStep 877157 = 164467) (by norm_num)
theorem B877181 : Blo 583288 877181 := bbase (se 3 (by rfl) ⟨164471, by rfl⟩ : syracuseStep 877181 = 328943) (by norm_num)
theorem B2810501 : Blo 583288 2810501 := bbase (se 4 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 2810501 = 526969) (by norm_num)
theorem B877205 : Blo 583288 877205 := bbase (se 6 (by rfl) ⟨20559, by rfl⟩ : syracuseStep 877205 = 41119) (by norm_num)
theorem B877229 : Blo 583288 877229 := bbase (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) (by norm_num)
theorem B1663669 : Blo 583288 1663669 := bbase (se 5 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 1663669 = 155969) (by norm_num)
theorem B877253 : Blo 583288 877253 := bbase (se 4 (by rfl) ⟨82242, by rfl⟩ : syracuseStep 877253 = 164485) (by norm_num)
theorem B877277 : Blo 583288 877277 := bbase (se 3 (by rfl) ⟨164489, by rfl⟩ : syracuseStep 877277 = 328979) (by norm_num)
theorem B877301 : Blo 583288 877301 := bbase (se 5 (by rfl) ⟨41123, by rfl⟩ : syracuseStep 877301 = 82247) (by norm_num)
theorem B877325 : Blo 583288 877325 := bbase (se 3 (by rfl) ⟨164498, by rfl⟩ : syracuseStep 877325 = 328997) (by norm_num)
theorem B877349 : Blo 583288 877349 := bbase (se 4 (by rfl) ⟨82251, by rfl⟩ : syracuseStep 877349 = 164503) (by norm_num)
theorem B877373 : Blo 583288 877373 := bbase (se 3 (by rfl) ⟨164507, by rfl⟩ : syracuseStep 877373 = 329015) (by norm_num)
theorem B877397 : Blo 583288 877397 := bbase (se 9 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 877397 = 5141) (by norm_num)
theorem B2253653 : Blo 583288 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B877421 : Blo 583288 877421 := bbase (se 3 (by rfl) ⟨164516, by rfl⟩ : syracuseStep 877421 = 329033) (by norm_num)
theorem B877445 : Blo 583288 877445 := bbase (se 4 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 877445 = 164521) (by norm_num)
theorem B877469 : Blo 583288 877469 := bbase (se 3 (by rfl) ⟨164525, by rfl⟩ : syracuseStep 877469 = 329051) (by norm_num)
theorem B877493 : Blo 583288 877493 := bbase (se 5 (by rfl) ⟨41132, by rfl⟩ : syracuseStep 877493 = 82265) (by norm_num)
theorem B877517 : Blo 583288 877517 := bbase (se 3 (by rfl) ⟨164534, by rfl⟩ : syracuseStep 877517 = 329069) (by norm_num)
theorem B877541 : Blo 583288 877541 := bbase (se 4 (by rfl) ⟨82269, by rfl⟩ : syracuseStep 877541 = 164539) (by norm_num)
theorem B877565 : Blo 583288 877565 := bbase (se 3 (by rfl) ⟨164543, by rfl⟩ : syracuseStep 877565 = 329087) (by norm_num)
theorem B877589 : Blo 583288 877589 := bbase (se 6 (by rfl) ⟨20568, by rfl⟩ : syracuseStep 877589 = 41137) (by norm_num)
theorem B877613 : Blo 583288 877613 := bbase (se 3 (by rfl) ⟨164552, by rfl⟩ : syracuseStep 877613 = 329105) (by norm_num)
theorem B877637 : Blo 583288 877637 := bbase (se 4 (by rfl) ⟨82278, by rfl⟩ : syracuseStep 877637 = 164557) (by norm_num)
theorem B2221141 : Blo 583288 2221141 := bbase (se 8 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 2221141 = 26029) (by norm_num)
theorem B877661 : Blo 583288 877661 := bbase (se 3 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 877661 = 329123) (by norm_num)
theorem B877685 : Blo 583288 877685 := bbase (se 5 (by rfl) ⟨41141, by rfl⟩ : syracuseStep 877685 = 82283) (by norm_num)
theorem B1270909 : Blo 583288 1270909 := bbase (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) (by norm_num)
theorem B877709 : Blo 583288 877709 := bbase (se 3 (by rfl) ⟨164570, by rfl⟩ : syracuseStep 877709 = 329141) (by norm_num)
theorem B877733 : Blo 583288 877733 := bbase (se 4 (by rfl) ⟨82287, by rfl⟩ : syracuseStep 877733 = 164575) (by norm_num)
theorem B877757 : Blo 583288 877757 := bbase (se 3 (by rfl) ⟨164579, by rfl⟩ : syracuseStep 877757 = 329159) (by norm_num)
theorem B1402069 : Blo 583288 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B877781 : Blo 583288 877781 := bbase (se 7 (by rfl) ⟨10286, by rfl⟩ : syracuseStep 877781 = 20573) (by norm_num)
theorem B877805 : Blo 583288 877805 := bbase (se 3 (by rfl) ⟨164588, by rfl⟩ : syracuseStep 877805 = 329177) (by norm_num)
theorem B877829 : Blo 583288 877829 := bbase (se 4 (by rfl) ⟨82296, by rfl⟩ : syracuseStep 877829 = 164593) (by norm_num)
theorem B877853 : Blo 583288 877853 := bbase (se 3 (by rfl) ⟨164597, by rfl⟩ : syracuseStep 877853 = 329195) (by norm_num)
theorem B877877 : Blo 583288 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B1500493 : Blo 583288 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B877901 : Blo 583288 877901 := bbase (se 3 (by rfl) ⟨164606, by rfl⟩ : syracuseStep 877901 = 329213) (by norm_num)
theorem B877925 : Blo 583288 877925 := bbase (se 4 (by rfl) ⟨82305, by rfl⟩ : syracuseStep 877925 = 164611) (by norm_num)
theorem B877949 : Blo 583288 877949 := bbase (se 3 (by rfl) ⟨164615, by rfl⟩ : syracuseStep 877949 = 329231) (by norm_num)
theorem B2221445 : Blo 583288 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B877973 : Blo 583288 877973 := bbase (se 6 (by rfl) ⟨20577, by rfl⟩ : syracuseStep 877973 = 41155) (by norm_num)
theorem B877997 : Blo 583288 877997 := bbase (se 3 (by rfl) ⟨164624, by rfl⟩ : syracuseStep 877997 = 329249) (by norm_num)
theorem B878021 : Blo 583288 878021 := bbase (se 4 (by rfl) ⟨82314, by rfl⟩ : syracuseStep 878021 = 164629) (by norm_num)
theorem B878045 : Blo 583288 878045 := bbase (se 3 (by rfl) ⟨164633, by rfl⟩ : syracuseStep 878045 = 329267) (by norm_num)
theorem B878069 : Blo 583288 878069 := bbase (se 5 (by rfl) ⟨41159, by rfl⟩ : syracuseStep 878069 = 82319) (by norm_num)
theorem B878093 : Blo 583288 878093 := bbase (se 3 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 878093 = 329285) (by norm_num)
theorem B878117 : Blo 583288 878117 := bbase (se 4 (by rfl) ⟨82323, by rfl⟩ : syracuseStep 878117 = 164647) (by norm_num)
theorem B878141 : Blo 583288 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B1107533 : Blo 583288 1107533 := bbase (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) (by norm_num)
theorem B878165 : Blo 583288 878165 := bbase (se 8 (by rfl) ⟨5145, by rfl⟩ : syracuseStep 878165 = 10291) (by norm_num)
theorem B5006933 : Blo 583288 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B878189 : Blo 583288 878189 := bbase (se 3 (by rfl) ⟨164660, by rfl⟩ : syracuseStep 878189 = 329321) (by norm_num)
theorem B878213 : Blo 583288 878213 := bbase (se 4 (by rfl) ⟨82332, by rfl⟩ : syracuseStep 878213 = 164665) (by norm_num)
theorem B878237 : Blo 583288 878237 := bbase (se 3 (by rfl) ⟨164669, by rfl⟩ : syracuseStep 878237 = 329339) (by norm_num)
theorem B878261 : Blo 583288 878261 := bbase (se 5 (by rfl) ⟨41168, by rfl⟩ : syracuseStep 878261 = 82337) (by norm_num)
theorem B878285 : Blo 583288 878285 := bbase (se 3 (by rfl) ⟨164678, by rfl⟩ : syracuseStep 878285 = 329357) (by norm_num)
theorem B1402589 : Blo 583288 1402589 := bbase (se 3 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 1402589 = 525971) (by norm_num)
theorem B1107685 : Blo 583288 1107685 := bbase (se 4 (by rfl) ⟨103845, by rfl⟩ : syracuseStep 1107685 = 207691) (by norm_num)
theorem B878309 : Blo 583288 878309 := bbase (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) (by norm_num)
theorem B1042157 : Blo 583288 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B878333 : Blo 583288 878333 := bbase (se 3 (by rfl) ⟨164687, by rfl⟩ : syracuseStep 878333 = 329375) (by norm_num)
theorem B878357 : Blo 583288 878357 := bbase (se 6 (by rfl) ⟨20586, by rfl⟩ : syracuseStep 878357 = 41173) (by norm_num)
theorem B878381 : Blo 583288 878381 := bbase (se 3 (by rfl) ⟨164696, by rfl⟩ : syracuseStep 878381 = 329393) (by norm_num)
theorem B878405 : Blo 583288 878405 := bbase (se 4 (by rfl) ⟨82350, by rfl⟩ : syracuseStep 878405 = 164701) (by norm_num)
theorem B878429 : Blo 583288 878429 := bbase (se 3 (by rfl) ⟨164705, by rfl⟩ : syracuseStep 878429 = 329411) (by norm_num)
theorem B878453 : Blo 583288 878453 := bbase (se 5 (by rfl) ⟨41177, by rfl⟩ : syracuseStep 878453 = 82355) (by norm_num)
theorem B3172213 : Blo 583288 3172213 := bbase (se 5 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 3172213 = 297395) (by norm_num)
theorem B714629 : Blo 583288 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B878477 : Blo 583288 878477 := bbase (se 3 (by rfl) ⟨164714, by rfl⟩ : syracuseStep 878477 = 329429) (by norm_num)
theorem B878501 : Blo 583288 878501 := bbase (se 4 (by rfl) ⟨82359, by rfl⟩ : syracuseStep 878501 = 164719) (by norm_num)
theorem B878525 : Blo 583288 878525 := bbase (se 3 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 878525 = 329447) (by norm_num)
theorem B878549 : Blo 583288 878549 := bbase (se 7 (by rfl) ⟨10295, by rfl⟩ : syracuseStep 878549 = 20591) (by norm_num)
theorem B878573 : Blo 583288 878573 := bbase (se 3 (by rfl) ⟨164732, by rfl⟩ : syracuseStep 878573 = 329465) (by norm_num)
theorem B878597 : Blo 583288 878597 := bbase (se 4 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 878597 = 164737) (by norm_num)
theorem B1107989 : Blo 583288 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B878621 : Blo 583288 878621 := bbase (se 3 (by rfl) ⟨164741, by rfl⟩ : syracuseStep 878621 = 329483) (by norm_num)
theorem B878645 : Blo 583288 878645 := bbase (se 5 (by rfl) ⟨41186, by rfl⟩ : syracuseStep 878645 = 82373) (by norm_num)
theorem B878669 : Blo 583288 878669 := bbase (se 3 (by rfl) ⟨164750, by rfl⟩ : syracuseStep 878669 = 329501) (by norm_num)
theorem B1402973 : Blo 583288 1402973 := bbase (se 3 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 1402973 = 526115) (by norm_num)
theorem B878693 : Blo 583288 878693 := bbase (se 4 (by rfl) ⟨82377, by rfl⟩ : syracuseStep 878693 = 164755) (by norm_num)
theorem B878717 : Blo 583288 878717 := bbase (se 3 (by rfl) ⟨164759, by rfl⟩ : syracuseStep 878717 = 329519) (by norm_num)
theorem B1403021 : Blo 583288 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B1403029 : Blo 583288 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B1665173 : Blo 583288 1665173 := bbase (se 6 (by rfl) ⟨39027, by rfl⟩ : syracuseStep 1665173 = 78055) (by norm_num)
theorem B878741 : Blo 583288 878741 := bbase (se 6 (by rfl) ⟨20595, by rfl⟩ : syracuseStep 878741 = 41191) (by norm_num)
theorem B878765 : Blo 583288 878765 := bbase (se 3 (by rfl) ⟨164768, by rfl⟩ : syracuseStep 878765 = 329537) (by norm_num)
theorem B878789 : Blo 583288 878789 := bbase (se 4 (by rfl) ⟨82386, by rfl⟩ : syracuseStep 878789 = 164773) (by norm_num)
theorem B878813 : Blo 583288 878813 := bbase (se 3 (by rfl) ⟨164777, by rfl⟩ : syracuseStep 878813 = 329555) (by norm_num)
theorem B2812133 : Blo 583288 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B878837 : Blo 583288 878837 := bbase (se 5 (by rfl) ⟨41195, by rfl⟩ : syracuseStep 878837 = 82391) (by norm_num)
theorem B1894661 : Blo 583288 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B878861 : Blo 583288 878861 := bbase (se 3 (by rfl) ⟨164786, by rfl⟩ : syracuseStep 878861 = 329573) (by norm_num)
theorem B878885 : Blo 583288 878885 := bbase (se 4 (by rfl) ⟨82395, by rfl⟩ : syracuseStep 878885 = 164791) (by norm_num)
theorem B878909 : Blo 583288 878909 := bbase (se 3 (by rfl) ⟨164795, by rfl⟩ : syracuseStep 878909 = 329591) (by norm_num)
theorem B878933 : Blo 583288 878933 := bbase (se 10 (by rfl) ⟨1287, by rfl⟩ : syracuseStep 878933 = 2575) (by norm_num)
theorem B878957 : Blo 583288 878957 := bbase (se 3 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 878957 = 329609) (by norm_num)
theorem B878981 : Blo 583288 878981 := bbase (se 4 (by rfl) ⟨82404, by rfl⟩ : syracuseStep 878981 = 164809) (by norm_num)
theorem B879005 : Blo 583288 879005 := bbase (se 3 (by rfl) ⟨164813, by rfl⟩ : syracuseStep 879005 = 329627) (by norm_num)
theorem B879029 : Blo 583288 879029 := bbase (se 5 (by rfl) ⟨41204, by rfl⟩ : syracuseStep 879029 = 82409) (by norm_num)
theorem B879053 : Blo 583288 879053 := bbase (se 3 (by rfl) ⟨164822, by rfl⟩ : syracuseStep 879053 = 329645) (by norm_num)
theorem B879077 : Blo 583288 879077 := bbase (se 4 (by rfl) ⟨82413, by rfl⟩ : syracuseStep 879077 = 164827) (by norm_num)
theorem B879101 : Blo 583288 879101 := bbase (se 3 (by rfl) ⟨164831, by rfl⟩ : syracuseStep 879101 = 329663) (by norm_num)
theorem B879125 : Blo 583288 879125 := bbase (se 6 (by rfl) ⟨20604, by rfl⟩ : syracuseStep 879125 = 41209) (by norm_num)
theorem B879149 : Blo 583288 879149 := bbase (se 3 (by rfl) ⟨164840, by rfl⟩ : syracuseStep 879149 = 329681) (by norm_num)
theorem B879173 : Blo 583288 879173 := bbase (se 4 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 879173 = 164845) (by norm_num)
theorem B879197 : Blo 583288 879197 := bbase (se 3 (by rfl) ⟨164849, by rfl⟩ : syracuseStep 879197 = 329699) (by norm_num)
theorem B879221 : Blo 583288 879221 := bbase (se 5 (by rfl) ⟨41213, by rfl⟩ : syracuseStep 879221 = 82427) (by norm_num)
theorem B1501829 : Blo 583288 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B879245 : Blo 583288 879245 := bbase (se 3 (by rfl) ⟨164858, by rfl⟩ : syracuseStep 879245 = 329717) (by norm_num)
theorem B879269 : Blo 583288 879269 := bbase (se 4 (by rfl) ⟨82431, by rfl⟩ : syracuseStep 879269 = 164863) (by norm_num)
theorem B879293 : Blo 583288 879293 := bbase (se 3 (by rfl) ⟨164867, by rfl⟩ : syracuseStep 879293 = 329735) (by norm_num)
theorem B879317 : Blo 583288 879317 := bbase (se 7 (by rfl) ⟨10304, by rfl⟩ : syracuseStep 879317 = 20609) (by norm_num)
theorem B879341 : Blo 583288 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B1108741 : Blo 583288 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B879365 : Blo 583288 879365 := bbase (se 4 (by rfl) ⟨82440, by rfl⟩ : syracuseStep 879365 = 164881) (by norm_num)
theorem B1338133 : Blo 583288 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B879389 : Blo 583288 879389 := bbase (se 3 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 879389 = 329771) (by norm_num)
theorem B879413 : Blo 583288 879413 := bbase (se 5 (by rfl) ⟨41222, by rfl⟩ : syracuseStep 879413 = 82445) (by norm_num)
theorem B4516661 : Blo 583288 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B879437 : Blo 583288 879437 := bbase (se 3 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 879437 = 329789) (by norm_num)
theorem B879461 : Blo 583288 879461 := bbase (se 4 (by rfl) ⟨82449, by rfl⟩ : syracuseStep 879461 = 164899) (by norm_num)
theorem B879485 : Blo 583288 879485 := bbase (se 3 (by rfl) ⟨164903, by rfl⟩ : syracuseStep 879485 = 329807) (by norm_num)
theorem B1108885 : Blo 583288 1108885 := bbase (se 6 (by rfl) ⟨25989, by rfl⟩ : syracuseStep 1108885 = 51979) (by norm_num)
theorem B2845589 : Blo 583288 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B879509 : Blo 583288 879509 := bbase (se 6 (by rfl) ⟨20613, by rfl⟩ : syracuseStep 879509 = 41227) (by norm_num)
theorem B879533 : Blo 583288 879533 := bbase (se 3 (by rfl) ⟨164912, by rfl⟩ : syracuseStep 879533 = 329825) (by norm_num)
theorem B879557 : Blo 583288 879557 := bbase (se 4 (by rfl) ⟨82458, by rfl⟩ : syracuseStep 879557 = 164917) (by norm_num)
theorem B879581 : Blo 583288 879581 := bbase (se 3 (by rfl) ⟨164921, by rfl⟩ : syracuseStep 879581 = 329843) (by norm_num)
theorem B879605 : Blo 583288 879605 := bbase (se 5 (by rfl) ⟨41231, by rfl⟩ : syracuseStep 879605 = 82463) (by norm_num)
theorem B879629 : Blo 583288 879629 := bbase (se 3 (by rfl) ⟨164930, by rfl⟩ : syracuseStep 879629 = 329861) (by norm_num)
theorem B879653 : Blo 583288 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B1109045 : Blo 583288 1109045 := bbase (se 5 (by rfl) ⟨51986, by rfl⟩ : syracuseStep 1109045 = 103973) (by norm_num)
theorem B879677 : Blo 583288 879677 := bbase (se 3 (by rfl) ⟨164939, by rfl⟩ : syracuseStep 879677 = 329879) (by norm_num)
theorem B879701 : Blo 583288 879701 := bbase (se 8 (by rfl) ⟨5154, by rfl⟩ : syracuseStep 879701 = 10309) (by norm_num)
theorem B912493 : Blo 583288 912493 := bbase (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) (by norm_num)
theorem B879725 : Blo 583288 879725 := bbase (se 3 (by rfl) ⟨164948, by rfl⟩ : syracuseStep 879725 = 329897) (by norm_num)
theorem B1404029 : Blo 583288 1404029 := bbase (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) (by norm_num)
theorem B2256005 : Blo 583288 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B879749 : Blo 583288 879749 := bbase (se 4 (by rfl) ⟨82476, by rfl⟩ : syracuseStep 879749 = 164953) (by norm_num)
theorem B879773 : Blo 583288 879773 := bbase (se 3 (by rfl) ⟨164957, by rfl⟩ : syracuseStep 879773 = 329915) (by norm_num)
theorem B879797 : Blo 583288 879797 := bbase (se 5 (by rfl) ⟨41240, by rfl⟩ : syracuseStep 879797 = 82481) (by norm_num)
theorem B1109189 : Blo 583288 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B879821 : Blo 583288 879821 := bbase (se 3 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 879821 = 329933) (by norm_num)
theorem B879845 : Blo 583288 879845 := bbase (se 4 (by rfl) ⟨82485, by rfl⟩ : syracuseStep 879845 = 164971) (by norm_num)
theorem B879869 : Blo 583288 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B879893 : Blo 583288 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B879917 : Blo 583288 879917 := bbase (se 3 (by rfl) ⟨164984, by rfl⟩ : syracuseStep 879917 = 329969) (by norm_num)
theorem B1404221 : Blo 583288 1404221 := bbase (se 3 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 1404221 = 526583) (by norm_num)
theorem B879941 : Blo 583288 879941 := bbase (se 4 (by rfl) ⟨82494, by rfl⟩ : syracuseStep 879941 = 164989) (by norm_num)
theorem B879965 : Blo 583288 879965 := bbase (se 3 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 879965 = 329987) (by norm_num)
theorem B879989 : Blo 583288 879989 := bbase (se 5 (by rfl) ⟨41249, by rfl⟩ : syracuseStep 879989 = 82499) (by norm_num)
theorem B880013 : Blo 583288 880013 := bbase (se 3 (by rfl) ⟨165002, by rfl⟩ : syracuseStep 880013 = 330005) (by norm_num)
theorem B880037 : Blo 583288 880037 := bbase (se 4 (by rfl) ⟨82503, by rfl⟩ : syracuseStep 880037 = 165007) (by norm_num)
theorem B880061 : Blo 583288 880061 := bbase (se 3 (by rfl) ⟨165011, by rfl⟩ : syracuseStep 880061 = 330023) (by norm_num)
theorem B2223557 : Blo 583288 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B880085 : Blo 583288 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B1109477 : Blo 583288 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B1338853 : Blo 583288 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B880109 : Blo 583288 880109 := bbase (se 3 (by rfl) ⟨165020, by rfl⟩ : syracuseStep 880109 = 330041) (by norm_num)
theorem B880133 : Blo 583288 880133 := bbase (se 4 (by rfl) ⟨82512, by rfl⟩ : syracuseStep 880133 = 165025) (by norm_num)
theorem B880157 : Blo 583288 880157 := bbase (se 3 (by rfl) ⟨165029, by rfl⟩ : syracuseStep 880157 = 330059) (by norm_num)
theorem B880181 : Blo 583288 880181 := bbase (se 5 (by rfl) ⟨41258, by rfl⟩ : syracuseStep 880181 = 82517) (by norm_num)
theorem B880205 : Blo 583288 880205 := bbase (se 3 (by rfl) ⟨165038, by rfl⟩ : syracuseStep 880205 = 330077) (by norm_num)
theorem B880229 : Blo 583288 880229 := bbase (se 4 (by rfl) ⟨82521, by rfl⟩ : syracuseStep 880229 = 165043) (by norm_num)
theorem B1109629 : Blo 583288 1109629 := bbase (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) (by norm_num)
theorem B880253 : Blo 583288 880253 := bbase (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) (by norm_num)
theorem B880277 : Blo 583288 880277 := bbase (se 6 (by rfl) ⟨20631, by rfl⟩ : syracuseStep 880277 = 41263) (by norm_num)
theorem B880301 : Blo 583288 880301 := bbase (se 3 (by rfl) ⟨165056, by rfl⟩ : syracuseStep 880301 = 330113) (by norm_num)
theorem B1666757 : Blo 583288 1666757 := bbase (se 4 (by rfl) ⟨156258, by rfl⟩ : syracuseStep 1666757 = 312517) (by norm_num)
theorem B880325 : Blo 583288 880325 := bbase (se 4 (by rfl) ⟨82530, by rfl⟩ : syracuseStep 880325 = 165061) (by norm_num)
theorem B880349 : Blo 583288 880349 := bbase (se 3 (by rfl) ⟨165065, by rfl⟩ : syracuseStep 880349 = 330131) (by norm_num)
theorem B2223845 : Blo 583288 2223845 := bbase (se 4 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 2223845 = 416971) (by norm_num)
theorem B880373 : Blo 583288 880373 := bbase (se 5 (by rfl) ⟨41267, by rfl⟩ : syracuseStep 880373 = 82535) (by norm_num)
theorem B880397 : Blo 583288 880397 := bbase (se 3 (by rfl) ⟨165074, by rfl⟩ : syracuseStep 880397 = 330149) (by norm_num)
theorem B880421 : Blo 583288 880421 := bbase (se 4 (by rfl) ⟨82539, by rfl⟩ : syracuseStep 880421 = 165079) (by norm_num)
theorem B880445 : Blo 583288 880445 := bbase (se 3 (by rfl) ⟨165083, by rfl⟩ : syracuseStep 880445 = 330167) (by norm_num)
theorem B880469 : Blo 583288 880469 := bbase (se 9 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 880469 = 5159) (by norm_num)
theorem B880493 : Blo 583288 880493 := bbase (se 3 (by rfl) ⟨165092, by rfl⟩ : syracuseStep 880493 = 330185) (by norm_num)
theorem B880517 : Blo 583288 880517 := bbase (se 4 (by rfl) ⟨82548, by rfl⟩ : syracuseStep 880517 = 165097) (by norm_num)
theorem B4452245 : Blo 583288 4452245 := bbase (se 6 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 4452245 = 208699) (by norm_num)
theorem B880541 : Blo 583288 880541 := bbase (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) (by norm_num)
theorem B1109933 : Blo 583288 1109933 := bbase (se 3 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 1109933 = 416225) (by norm_num)
theorem B880565 : Blo 583288 880565 := bbase (se 5 (by rfl) ⟨41276, by rfl⟩ : syracuseStep 880565 = 82553) (by norm_num)
theorem B880589 : Blo 583288 880589 := bbase (se 3 (by rfl) ⟨165110, by rfl⟩ : syracuseStep 880589 = 330221) (by norm_num)
theorem B880613 : Blo 583288 880613 := bbase (se 4 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 880613 = 165115) (by norm_num)
theorem B880637 : Blo 583288 880637 := bbase (se 3 (by rfl) ⟨165119, by rfl⟩ : syracuseStep 880637 = 330239) (by norm_num)
theorem B880661 : Blo 583288 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B880685 : Blo 583288 880685 := bbase (se 3 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 880685 = 330257) (by norm_num)
theorem B880709 : Blo 583288 880709 := bbase (se 4 (by rfl) ⟨82566, by rfl⟩ : syracuseStep 880709 = 165133) (by norm_num)
theorem B880733 : Blo 583288 880733 := bbase (se 3 (by rfl) ⟨165137, by rfl⟩ : syracuseStep 880733 = 330275) (by norm_num)
theorem B880757 : Blo 583288 880757 := bbase (se 5 (by rfl) ⟨41285, by rfl⟩ : syracuseStep 880757 = 82571) (by norm_num)
theorem B880781 : Blo 583288 880781 := bbase (se 3 (by rfl) ⟨165146, by rfl⟩ : syracuseStep 880781 = 330293) (by norm_num)
theorem B880805 : Blo 583288 880805 := bbase (se 4 (by rfl) ⟨82575, by rfl⟩ : syracuseStep 880805 = 165151) (by norm_num)
theorem B880829 : Blo 583288 880829 := bbase (se 3 (by rfl) ⟨165155, by rfl⟩ : syracuseStep 880829 = 330311) (by norm_num)
theorem B880853 : Blo 583288 880853 := bbase (se 7 (by rfl) ⟨10322, by rfl⟩ : syracuseStep 880853 = 20645) (by norm_num)
theorem B1503469 : Blo 583288 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B880877 : Blo 583288 880877 := bbase (se 3 (by rfl) ⟨165164, by rfl⟩ : syracuseStep 880877 = 330329) (by norm_num)
theorem B749821 : Blo 583288 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B880901 : Blo 583288 880901 := bbase (se 4 (by rfl) ⟨82584, by rfl⟩ : syracuseStep 880901 = 165169) (by norm_num)
theorem B880925 : Blo 583288 880925 := bbase (se 3 (by rfl) ⟨165173, by rfl⟩ : syracuseStep 880925 = 330347) (by norm_num)
theorem B1667429 : Blo 583288 1667429 := bbase (se 4 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 1667429 = 312643) (by norm_num)
theorem B1896853 : Blo 583288 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B1110685 : Blo 583288 1110685 := bbase (se 3 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 1110685 = 416507) (by norm_num)
theorem B750277 : Blo 583288 750277 := bbase (se 4 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 750277 = 140677) (by norm_num)
theorem B1667861 : Blo 583288 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B1110829 : Blo 583288 1110829 := bbase (se 3 (by rfl) ⟨208280, by rfl⟩ : syracuseStep 1110829 = 416561) (by norm_num)
theorem B750421 : Blo 583288 750421 := bbase (se 9 (by rfl) ⟨2198, by rfl⟩ : syracuseStep 750421 = 4397) (by norm_num)
theorem B2225029 : Blo 583288 2225029 := bbase (se 4 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 2225029 = 417193) (by norm_num)
theorem B1110989 : Blo 583288 1110989 := bbase (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) (by norm_num)
theorem B1111133 : Blo 583288 1111133 := bbase (se 3 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 1111133 = 416675) (by norm_num)
theorem B3339413 : Blo 583288 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B2225333 : Blo 583288 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1406173 : Blo 583288 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B1111421 : Blo 583288 1111421 := bbase (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) (by norm_num)
theorem B1668613 : Blo 583288 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B1111573 : Blo 583288 1111573 := bbase (se 6 (by rfl) ⟨26052, by rfl⟩ : syracuseStep 1111573 = 52105) (by norm_num)
theorem B751141 : Blo 583288 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B1898101 : Blo 583288 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B1373885 : Blo 583288 1373885 := bbase (se 3 (by rfl) ⟨257603, by rfl⟩ : syracuseStep 1373885 = 515207) (by norm_num)
theorem B1111877 : Blo 583288 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B2258837 : Blo 583288 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1505317 : Blo 583288 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B1407125 : Blo 583288 1407125 := bbase (se 6 (by rfl) ⟨32979, by rfl⟩ : syracuseStep 1407125 = 65959) (by norm_num)
theorem B8124565 : Blo 583288 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B1407181 : Blo 583288 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B751961 : Blo 583288 751961 := bbase (se 2 (by rfl) ⟨281985, by rfl⟩ : syracuseStep 751961 = 563971) (by norm_num)
theorem B1997237 : Blo 583288 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B1112629 : Blo 583288 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B1407557 : Blo 583288 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1112773 : Blo 583288 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B1407797 : Blo 583288 1407797 := bbase (se 5 (by rfl) ⟨65990, by rfl⟩ : syracuseStep 1407797 = 131981) (by norm_num)
theorem B1604437 : Blo 583288 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B1112933 : Blo 583288 1112933 := bbase (se 4 (by rfl) ⟨104337, by rfl⟩ : syracuseStep 1112933 = 208675) (by norm_num)
theorem B11369429 : Blo 583288 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B1113077 : Blo 583288 1113077 := bbase (se 5 (by rfl) ⟨52175, by rfl⟩ : syracuseStep 1113077 = 104351) (by norm_num)
theorem B1997893 : Blo 583288 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B2227445 : Blo 583288 2227445 := bbase (se 5 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 2227445 = 208823) (by norm_num)
theorem B752905 : Blo 583288 752905 := bbase (se 2 (by rfl) ⟨282339, by rfl⟩ : syracuseStep 752905 = 564679) (by norm_num)
theorem B1113365 : Blo 583288 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B949637 : Blo 583288 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B1113517 : Blo 583288 1113517 := bbase (se 3 (by rfl) ⟨208784, by rfl⟩ : syracuseStep 1113517 = 417569) (by norm_num)
theorem B2227733 : Blo 583288 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B1113821 : Blo 583288 1113821 := bbase (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) (by norm_num)
theorem B3211093 : Blo 583288 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1409123 : Blo 583288 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B950401 : Blo 583288 950401 := bstep (se 2 (by rfl) ⟨356400, by rfl⟩ : syracuseStep 950401 = 712801) B712801
theorem B1671313 : Blo 583288 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B950449 : Blo 583288 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B1114307 : Blo 583288 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B1671587 : Blo 583288 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B1671779 : Blo 583288 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B14615153 : Blo 583288 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B656275 : Blo 583288 656275 := bstep (se 1 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 656275 = 984413) B984413
theorem B6652853 : Blo 583288 6652853 := bstep (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) B623705
theorem B1410065 : Blo 583288 1410065 := bstep (se 2 (by rfl) ⟨528774, by rfl⟩ : syracuseStep 1410065 = 1057549) B1057549
theorem B656419 : Blo 583288 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B2229389 : Blo 583288 2229389 := bstep (se 3 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 2229389 = 836021) B836021
theorem B1246385 : Blo 583288 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B656563 : Blo 583288 656563 := bstep (se 1 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 656563 = 984845) B984845
theorem B1246403 : Blo 583288 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B1410257 : Blo 583288 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B984305 : Blo 583288 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B2491661 : Blo 583288 2491661 := bstep (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) B934373
theorem B656707 : Blo 583288 656707 := bstep (se 1 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 656707 = 985061) B985061
theorem B984433 : Blo 583288 984433 := bstep (se 2 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 984433 = 738325) B738325
theorem B13731185 : Blo 583288 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B984467 : Blo 583288 984467 := bstep (se 1 (by rfl) ⟨738350, by rfl⟩ : syracuseStep 984467 = 1476701) B1476701
theorem B656851 : Blo 583288 656851 := bstep (se 1 (by rfl) ⟨492638, by rfl⟩ : syracuseStep 656851 = 985277) B985277
theorem B984595 : Blo 583288 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B656995 : Blo 583288 656995 := bstep (se 1 (by rfl) ⟨492746, by rfl⟩ : syracuseStep 656995 = 985493) B985493
theorem B1869425 : Blo 583288 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B984737 : Blo 583288 984737 := bstep (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) B738553
theorem B1869475 : Blo 583288 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B1312433 : Blo 583288 1312433 := bstep (se 2 (by rfl) ⟨492162, by rfl⟩ : syracuseStep 1312433 = 984325) B984325
theorem B1312451 : Blo 583288 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B657139 : Blo 583288 657139 := bstep (se 1 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 657139 = 985709) B985709
theorem B2000657 : Blo 583288 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B984865 : Blo 583288 984865 := bstep (se 2 (by rfl) ⟨369324, by rfl⟩ : syracuseStep 984865 = 738649) B738649
theorem B984899 : Blo 583288 984899 := bstep (se 1 (by rfl) ⟨738674, by rfl⟩ : syracuseStep 984899 = 1477349) B1477349
theorem B657283 : Blo 583288 657283 := bstep (se 1 (by rfl) ⟨492962, by rfl⟩ : syracuseStep 657283 = 985925) B985925
theorem B985027 : Blo 583288 985027 := bstep (se 1 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 985027 = 1477541) B1477541
theorem B1312721 : Blo 583288 1312721 := bstep (se 2 (by rfl) ⟨492270, by rfl⟩ : syracuseStep 1312721 = 984541) B984541
theorem B1411025 : Blo 583288 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B1312739 : Blo 583288 1312739 := bstep (se 1 (by rfl) ⟨984554, by rfl⟩ : syracuseStep 1312739 = 1969109) B1969109
theorem B624611 : Blo 583288 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B657427 : Blo 583288 657427 := bstep (se 1 (by rfl) ⟨493070, by rfl⟩ : syracuseStep 657427 = 986141) B986141
theorem B985169 : Blo 583288 985169 := bstep (se 2 (by rfl) ⟨369438, by rfl⟩ : syracuseStep 985169 = 738877) B738877
theorem B788611 : Blo 583288 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B657571 : Blo 583288 657571 := bstep (se 1 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 657571 = 986357) B986357
theorem B3344561 : Blo 583288 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B985297 : Blo 583288 985297 := bstep (se 2 (by rfl) ⟨369486, by rfl⟩ : syracuseStep 985297 = 738973) B738973
theorem B1313009 : Blo 583288 1313009 := bstep (se 2 (by rfl) ⟨492378, by rfl⟩ : syracuseStep 1313009 = 984757) B984757
theorem B985331 : Blo 583288 985331 := bstep (se 1 (by rfl) ⟨738998, by rfl⟩ : syracuseStep 985331 = 1477997) B1477997
theorem B592115 : Blo 583288 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B887041 : Blo 583288 887041 := bstep (se 2 (by rfl) ⟨332640, by rfl⟩ : syracuseStep 887041 = 665281) B665281
theorem B1313027 : Blo 583288 1313027 := bstep (se 1 (by rfl) ⟨984770, by rfl⟩ : syracuseStep 1313027 = 1969541) B1969541
theorem B592147 : Blo 583288 592147 := bstep (se 1 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 592147 = 888221) B888221
theorem B1476913 : Blo 583288 1476913 := bstep (se 2 (by rfl) ⟨553842, by rfl⟩ : syracuseStep 1476913 = 1107685) B1107685
theorem B657715 : Blo 583288 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B985459 : Blo 583288 985459 := bstep (se 1 (by rfl) ⟨739094, by rfl⟩ : syracuseStep 985459 = 1478189) B1478189
theorem B4065677 : Blo 583288 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B1247633 : Blo 583288 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B657859 : Blo 583288 657859 := bstep (se 1 (by rfl) ⟨493394, by rfl⟩ : syracuseStep 657859 = 986789) B986789
theorem B723395 : Blo 583288 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B788945 : Blo 583288 788945 := bstep (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) B591709
theorem B5409251 : Blo 583288 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B4229617 : Blo 583288 4229617 := bstep (se 2 (by rfl) ⟨1586106, by rfl⟩ : syracuseStep 4229617 = 3172213) B3172213
theorem B985601 : Blo 583288 985601 := bstep (se 2 (by rfl) ⟨369600, by rfl⟩ : syracuseStep 985601 = 739201) B739201
theorem B1313297 : Blo 583288 1313297 := bstep (se 2 (by rfl) ⟨492486, by rfl⟩ : syracuseStep 1313297 = 984973) B984973
theorem B1313315 : Blo 583288 1313315 := bstep (se 1 (by rfl) ⟨984986, by rfl⟩ : syracuseStep 1313315 = 1969973) B1969973
theorem B1477187 : Blo 583288 1477187 := bstep (se 1 (by rfl) ⟨1107890, by rfl⟩ : syracuseStep 1477187 = 2215781) B2215781
theorem B658003 : Blo 583288 658003 := bstep (se 1 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 658003 = 987005) B987005
theorem B2820707 : Blo 583288 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B985729 : Blo 583288 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B1968785 : Blo 583288 1968785 := bstep (se 2 (by rfl) ⟨738294, by rfl⟩ : syracuseStep 1968785 = 1476589) B1476589
theorem B985763 : Blo 583288 985763 := bstep (se 1 (by rfl) ⟨739322, by rfl⟩ : syracuseStep 985763 = 1478645) B1478645
theorem B658147 : Blo 583288 658147 := bstep (se 1 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 658147 = 987221) B987221
theorem B5999345 : Blo 583288 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B1477379 : Blo 583288 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B985891 : Blo 583288 985891 := bstep (se 1 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 985891 = 1478837) B1478837
theorem B1313585 : Blo 583288 1313585 := bstep (se 2 (by rfl) ⟨492594, by rfl⟩ : syracuseStep 1313585 = 985189) B985189
theorem B1313603 : Blo 583288 1313603 := bstep (se 1 (by rfl) ⟨985202, by rfl⟩ : syracuseStep 1313603 = 1970405) B1970405
theorem B1870705 : Blo 583288 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B658291 : Blo 583288 658291 := bstep (se 1 (by rfl) ⟨493718, by rfl⟩ : syracuseStep 658291 = 987437) B987437
theorem B986033 : Blo 583288 986033 := bstep (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) B739525
theorem B658435 : Blo 583288 658435 := bstep (se 1 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 658435 = 987653) B987653
theorem B1182737 : Blo 583288 1182737 := bstep (se 2 (by rfl) ⟨443526, by rfl⟩ : syracuseStep 1182737 = 887053) B887053
theorem B986161 : Blo 583288 986161 := bstep (se 2 (by rfl) ⟨369810, by rfl⟩ : syracuseStep 986161 = 739621) B739621
theorem B2821169 : Blo 583288 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B1313873 : Blo 583288 1313873 := bstep (se 2 (by rfl) ⟨492702, by rfl⟩ : syracuseStep 1313873 = 985405) B985405
theorem B986195 : Blo 583288 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B1313891 : Blo 583288 1313891 := bstep (se 1 (by rfl) ⟨985418, by rfl⟩ : syracuseStep 1313891 = 1970837) B1970837
theorem B658579 : Blo 583288 658579 := bstep (se 1 (by rfl) ⟨493934, by rfl⟩ : syracuseStep 658579 = 987869) B987869
theorem B1969325 : Blo 583288 1969325 := bstep (se 3 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 1969325 = 738497) B738497
theorem B986323 : Blo 583288 986323 := bstep (se 1 (by rfl) ⟨739742, by rfl⟩ : syracuseStep 986323 = 1479485) B1479485
theorem B1969379 : Blo 583288 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B4754659 : Blo 583288 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B658723 : Blo 583288 658723 := bstep (se 1 (by rfl) ⟨494042, by rfl⟩ : syracuseStep 658723 = 988085) B988085
theorem B986465 : Blo 583288 986465 := bstep (se 2 (by rfl) ⟨369924, by rfl⟩ : syracuseStep 986465 = 739849) B739849
theorem B1314161 : Blo 583288 1314161 := bstep (se 2 (by rfl) ⟨492810, by rfl⟩ : syracuseStep 1314161 = 985621) B985621
theorem B2035057 : Blo 583288 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B1314179 : Blo 583288 1314179 := bstep (se 1 (by rfl) ⟨985634, by rfl⟩ : syracuseStep 1314179 = 1971269) B1971269
theorem B658867 : Blo 583288 658867 := bstep (se 1 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 658867 = 988301) B988301
theorem B593363 : Blo 583288 593363 := bstep (se 1 (by rfl) ⟨445022, by rfl⟩ : syracuseStep 593363 = 890045) B890045
theorem B986593 : Blo 583288 986593 := bstep (se 2 (by rfl) ⟨369972, by rfl⟩ : syracuseStep 986593 = 739945) B739945
theorem B1969649 : Blo 583288 1969649 := bstep (se 2 (by rfl) ⟨738618, by rfl⟩ : syracuseStep 1969649 = 1477237) B1477237
theorem B986627 : Blo 583288 986627 := bstep (se 1 (by rfl) ⟨739970, by rfl⟩ : syracuseStep 986627 = 1479941) B1479941
theorem B659011 : Blo 583288 659011 := bstep (se 1 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 659011 = 988517) B988517
theorem B986755 : Blo 583288 986755 := bstep (se 1 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 986755 = 1480133) B1480133
theorem B13471373 : Blo 583288 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1314449 : Blo 583288 1314449 := bstep (se 2 (by rfl) ⟨492918, by rfl⟩ : syracuseStep 1314449 = 985837) B985837
theorem B1314467 : Blo 583288 1314467 := bstep (se 1 (by rfl) ⟨985850, by rfl⟩ : syracuseStep 1314467 = 1971701) B1971701
theorem B1478321 : Blo 583288 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B659155 : Blo 583288 659155 := bstep (se 1 (by rfl) ⟨494366, by rfl⟩ : syracuseStep 659155 = 988733) B988733
theorem B1478371 : Blo 583288 1478371 := bstep (se 1 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 1478371 = 2217557) B2217557
theorem B986897 : Blo 583288 986897 := bstep (se 2 (by rfl) ⟨370086, by rfl⟩ : syracuseStep 986897 = 740173) B740173
theorem B659299 : Blo 583288 659299 := bstep (se 1 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 659299 = 988949) B988949
theorem B1478513 : Blo 583288 1478513 := bstep (se 2 (by rfl) ⟨554442, by rfl⟩ : syracuseStep 1478513 = 1108885) B1108885
theorem B1052561 : Blo 583288 1052561 := bstep (se 2 (by rfl) ⟨394710, by rfl⟩ : syracuseStep 1052561 = 789421) B789421
theorem B987025 : Blo 583288 987025 := bstep (se 2 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 987025 = 740269) B740269
theorem B1249187 : Blo 583288 1249187 := bstep (se 1 (by rfl) ⟨936890, by rfl⟩ : syracuseStep 1249187 = 1873781) B1873781
theorem B1314737 : Blo 583288 1314737 := bstep (se 2 (by rfl) ⟨493026, by rfl⟩ : syracuseStep 1314737 = 986053) B986053
theorem B987059 : Blo 583288 987059 := bstep (se 1 (by rfl) ⟨740294, by rfl⟩ : syracuseStep 987059 = 1480589) B1480589
theorem B1314755 : Blo 583288 1314755 := bstep (se 1 (by rfl) ⟨986066, by rfl⟩ : syracuseStep 1314755 = 1972133) B1972133
theorem B626627 : Blo 583288 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B659443 : Blo 583288 659443 := bstep (se 1 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 659443 = 989165) B989165
theorem B1970189 : Blo 583288 1970189 := bstep (se 3 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 1970189 = 738821) B738821
theorem B1871885 : Blo 583288 1871885 := bstep (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) B701957
theorem B987187 : Blo 583288 987187 := bstep (se 1 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 987187 = 1480781) B1480781
theorem B1970243 : Blo 583288 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B659587 : Blo 583288 659587 := bstep (se 1 (by rfl) ⟨494690, by rfl⟩ : syracuseStep 659587 = 989381) B989381
theorem B1216657 : Blo 583288 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B987329 : Blo 583288 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B2953421 : Blo 583288 2953421 := bstep (se 3 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 2953421 = 1107533) B1107533
theorem B1315025 : Blo 583288 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B1315043 : Blo 583288 1315043 := bstep (se 1 (by rfl) ⟨986282, by rfl⟩ : syracuseStep 1315043 = 1972565) B1972565
theorem B659731 : Blo 583288 659731 := bstep (se 1 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 659731 = 989597) B989597
theorem B987457 : Blo 583288 987457 := bstep (se 2 (by rfl) ⟨370296, by rfl⟩ : syracuseStep 987457 = 740593) B740593
theorem B1970513 : Blo 583288 1970513 := bstep (se 2 (by rfl) ⟨738942, by rfl⟩ : syracuseStep 1970513 = 1477885) B1477885
theorem B987491 : Blo 583288 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B659875 : Blo 583288 659875 := bstep (se 1 (by rfl) ⟨494906, by rfl⟩ : syracuseStep 659875 = 989813) B989813
theorem B8556997 : Blo 583288 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B987619 : Blo 583288 987619 := bstep (se 1 (by rfl) ⟨740714, by rfl⟩ : syracuseStep 987619 = 1481429) B1481429
theorem B1315313 : Blo 583288 1315313 := bstep (se 2 (by rfl) ⟨493242, by rfl⟩ : syracuseStep 1315313 = 986485) B986485
theorem B1315331 : Blo 583288 1315331 := bstep (se 1 (by rfl) ⟨986498, by rfl⟩ : syracuseStep 1315331 = 1972997) B1972997
theorem B660019 : Blo 583288 660019 := bstep (se 1 (by rfl) ⟨495014, by rfl⟩ : syracuseStep 660019 = 990029) B990029
theorem B2036305 : Blo 583288 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B987761 : Blo 583288 987761 := bstep (se 2 (by rfl) ⟨370410, by rfl⟩ : syracuseStep 987761 = 740821) B740821
theorem B660163 : Blo 583288 660163 := bstep (se 1 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 660163 = 990245) B990245
theorem B987889 : Blo 583288 987889 := bstep (se 2 (by rfl) ⟨370458, by rfl⟩ : syracuseStep 987889 = 740917) B740917
theorem B1315601 : Blo 583288 1315601 := bstep (se 2 (by rfl) ⟨493350, by rfl⟩ : syracuseStep 1315601 = 986701) B986701
theorem B987923 : Blo 583288 987923 := bstep (se 1 (by rfl) ⟨740942, by rfl⟩ : syracuseStep 987923 = 1481885) B1481885
theorem B1315619 : Blo 583288 1315619 := bstep (se 1 (by rfl) ⟨986714, by rfl⟩ : syracuseStep 1315619 = 1973429) B1973429
theorem B1479505 : Blo 583288 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B660307 : Blo 583288 660307 := bstep (se 1 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 660307 = 990461) B990461
theorem B1971053 : Blo 583288 1971053 := bstep (se 3 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 1971053 = 739145) B739145
theorem B988051 : Blo 583288 988051 := bstep (se 1 (by rfl) ⟨741038, by rfl⟩ : syracuseStep 988051 = 1482077) B1482077
theorem B1971107 : Blo 583288 1971107 := bstep (se 1 (by rfl) ⟨1478330, by rfl⟩ : syracuseStep 1971107 = 2956661) B2956661
theorem B660451 : Blo 583288 660451 := bstep (se 1 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 660451 = 990677) B990677
theorem B1905677 : Blo 583288 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B988193 : Blo 583288 988193 := bstep (se 2 (by rfl) ⟨370572, by rfl⟩ : syracuseStep 988193 = 741145) B741145
theorem B1315889 : Blo 583288 1315889 := bstep (se 2 (by rfl) ⟨493458, by rfl⟩ : syracuseStep 1315889 = 986917) B986917
theorem B857137 : Blo 583288 857137 := bstep (se 2 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 857137 = 642853) B642853
theorem B1315907 : Blo 583288 1315907 := bstep (se 1 (by rfl) ⟨986930, by rfl⟩ : syracuseStep 1315907 = 1973861) B1973861
theorem B1479779 : Blo 583288 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B660595 : Blo 583288 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B988321 : Blo 583288 988321 := bstep (se 2 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 988321 = 741241) B741241
theorem B3740849 : Blo 583288 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1971377 : Blo 583288 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B988355 : Blo 583288 988355 := bstep (se 1 (by rfl) ⟨741266, by rfl⟩ : syracuseStep 988355 = 1482533) B1482533
theorem B1479971 : Blo 583288 1479971 := bstep (se 1 (by rfl) ⟨1109978, by rfl⟩ : syracuseStep 1479971 = 2219957) B2219957
theorem B988483 : Blo 583288 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B1316177 : Blo 583288 1316177 := bstep (se 2 (by rfl) ⟨493566, by rfl⟩ : syracuseStep 1316177 = 987133) B987133
theorem B1316195 : Blo 583288 1316195 := bstep (se 1 (by rfl) ⟨987146, by rfl⟩ : syracuseStep 1316195 = 1974293) B1974293
theorem B1185187 : Blo 583288 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B988625 : Blo 583288 988625 := bstep (se 2 (by rfl) ⟨370734, by rfl⟩ : syracuseStep 988625 = 741469) B741469
theorem B2496035 : Blo 583288 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B988753 : Blo 583288 988753 := bstep (se 2 (by rfl) ⟨370782, by rfl⟩ : syracuseStep 988753 = 741565) B741565
theorem B1775213 : Blo 583288 1775213 := bstep (se 3 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 1775213 = 665705) B665705
theorem B1316465 : Blo 583288 1316465 := bstep (se 2 (by rfl) ⟨493674, by rfl⟩ : syracuseStep 1316465 = 987349) B987349
theorem B988787 : Blo 583288 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B1316483 : Blo 583288 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B1775249 : Blo 583288 1775249 := bstep (se 2 (by rfl) ⟨665718, by rfl⟩ : syracuseStep 1775249 = 1331437) B1331437
theorem B2004625 : Blo 583288 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B3741389 : Blo 583288 3741389 := bstep (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) B1403021
theorem B1971917 : Blo 583288 1971917 := bstep (se 3 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 1971917 = 739469) B739469
theorem B792275 : Blo 583288 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B988915 : Blo 583288 988915 := bstep (se 1 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 988915 = 1483373) B1483373
theorem B1971971 : Blo 583288 1971971 := bstep (se 1 (by rfl) ⟨1478978, by rfl⟩ : syracuseStep 1971971 = 2957957) B2957957
theorem B1873667 : Blo 583288 1873667 := bstep (se 1 (by rfl) ⟨1405250, by rfl⟩ : syracuseStep 1873667 = 2810501) B2810501
theorem B2529137 : Blo 583288 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B989057 : Blo 583288 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B1316753 : Blo 583288 1316753 := bstep (se 2 (by rfl) ⟨493782, by rfl⟩ : syracuseStep 1316753 = 987565) B987565
theorem B1316771 : Blo 583288 1316771 := bstep (se 1 (by rfl) ⟨987578, by rfl⟩ : syracuseStep 1316771 = 1975157) B1975157
theorem B11999173 : Blo 583288 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B989185 : Blo 583288 989185 := bstep (se 2 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 989185 = 741889) B741889
theorem B1972241 : Blo 583288 1972241 := bstep (se 2 (by rfl) ⟨739590, by rfl⟩ : syracuseStep 1972241 = 1479181) B1479181
theorem B989219 : Blo 583288 989219 := bstep (se 1 (by rfl) ⟨741914, by rfl⟩ : syracuseStep 989219 = 1483829) B1483829
theorem B1251409 : Blo 583288 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B1054883 : Blo 583288 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B989347 : Blo 583288 989347 := bstep (se 1 (by rfl) ⟨742010, by rfl⟩ : syracuseStep 989347 = 1484021) B1484021
theorem B1317041 : Blo 583288 1317041 := bstep (se 2 (by rfl) ⟨493890, by rfl⟩ : syracuseStep 1317041 = 987781) B987781
theorem B1317059 : Blo 583288 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B1480913 : Blo 583288 1480913 := bstep (se 2 (by rfl) ⟨555342, by rfl⟩ : syracuseStep 1480913 = 1110685) B1110685
theorem B2005229 : Blo 583288 2005229 := bstep (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) B751961
theorem B1480963 : Blo 583288 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B989489 : Blo 583288 989489 := bstep (se 2 (by rfl) ⟨371058, by rfl⟩ : syracuseStep 989489 = 742117) B742117
theorem B1481105 : Blo 583288 1481105 := bstep (se 2 (by rfl) ⟨555414, by rfl⟩ : syracuseStep 1481105 = 1110829) B1110829
theorem B989617 : Blo 583288 989617 := bstep (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) B742213
theorem B1317329 : Blo 583288 1317329 := bstep (se 2 (by rfl) ⟨493998, by rfl⟩ : syracuseStep 1317329 = 987997) B987997
theorem B989651 : Blo 583288 989651 := bstep (se 1 (by rfl) ⟨742238, by rfl⟩ : syracuseStep 989651 = 1484477) B1484477
theorem B1317347 : Blo 583288 1317347 := bstep (se 1 (by rfl) ⟨988010, by rfl⟩ : syracuseStep 1317347 = 1976021) B1976021
theorem B1972781 : Blo 583288 1972781 := bstep (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) B739793
theorem B989779 : Blo 583288 989779 := bstep (se 1 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 989779 = 1484669) B1484669
theorem B1579619 : Blo 583288 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1972835 : Blo 583288 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B1186499 : Blo 583288 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B989921 : Blo 583288 989921 := bstep (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) B742441
theorem B1317617 : Blo 583288 1317617 := bstep (se 2 (by rfl) ⟨494106, by rfl⟩ : syracuseStep 1317617 = 988213) B988213
theorem B1317635 : Blo 583288 1317635 := bstep (se 1 (by rfl) ⟨988226, by rfl⟩ : syracuseStep 1317635 = 1976453) B1976453
theorem B1874755 : Blo 583288 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B990049 : Blo 583288 990049 := bstep (se 2 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 990049 = 742537) B742537
theorem B1973105 : Blo 583288 1973105 := bstep (se 2 (by rfl) ⟨739914, by rfl⟩ : syracuseStep 1973105 = 1479829) B1479829
theorem B990083 : Blo 583288 990083 := bstep (se 1 (by rfl) ⟨742562, by rfl⟩ : syracuseStep 990083 = 1485125) B1485125
theorem B1874897 : Blo 583288 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B990211 : Blo 583288 990211 := bstep (se 1 (by rfl) ⟨742658, by rfl⟩ : syracuseStep 990211 = 1485317) B1485317
theorem B4430861 : Blo 583288 4430861 := bstep (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) B1661573
theorem B1317905 : Blo 583288 1317905 := bstep (se 2 (by rfl) ⟨494214, by rfl⟩ : syracuseStep 1317905 = 988429) B988429
theorem B1317923 : Blo 583288 1317923 := bstep (se 1 (by rfl) ⟨988442, by rfl⟩ : syracuseStep 1317923 = 1976885) B1976885
theorem B2956337 : Blo 583288 2956337 := bstep (se 2 (by rfl) ⟨1108626, by rfl⟩ : syracuseStep 2956337 = 2217253) B2217253
theorem B990353 : Blo 583288 990353 := bstep (se 2 (by rfl) ⟨371382, by rfl⟩ : syracuseStep 990353 = 742765) B742765
theorem B990481 : Blo 583288 990481 := bstep (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) B742861
theorem B1318193 : Blo 583288 1318193 := bstep (se 2 (by rfl) ⟨494322, by rfl⟩ : syracuseStep 1318193 = 988645) B988645
theorem B990515 : Blo 583288 990515 := bstep (se 1 (by rfl) ⟨742886, by rfl⟩ : syracuseStep 990515 = 1485773) B1485773
theorem B1318211 : Blo 583288 1318211 := bstep (se 1 (by rfl) ⟨988658, by rfl⟩ : syracuseStep 1318211 = 1977317) B1977317
theorem B1482097 : Blo 583288 1482097 := bstep (se 2 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 1482097 = 1111573) B1111573
theorem B1973645 : Blo 583288 1973645 := bstep (se 3 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 1973645 = 740117) B740117
theorem B990643 : Blo 583288 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B1973699 : Blo 583288 1973699 := bstep (se 1 (by rfl) ⟨1480274, by rfl⟩ : syracuseStep 1973699 = 2960549) B2960549
theorem B2530801 : Blo 583288 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B2498033 : Blo 583288 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B1580561 : Blo 583288 1580561 := bstep (se 2 (by rfl) ⟨592710, by rfl⟩ : syracuseStep 1580561 = 1185421) B1185421
theorem B11214389 : Blo 583288 11214389 := bstep (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) B1051349
theorem B990785 : Blo 583288 990785 := bstep (se 2 (by rfl) ⟨371544, by rfl⟩ : syracuseStep 990785 = 743089) B743089
theorem B7118405 : Blo 583288 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1318481 : Blo 583288 1318481 := bstep (se 2 (by rfl) ⟨494430, by rfl⟩ : syracuseStep 1318481 = 988861) B988861
theorem B1318499 : Blo 583288 1318499 := bstep (se 1 (by rfl) ⟨988874, by rfl⟩ : syracuseStep 1318499 = 1977749) B1977749
theorem B1482371 : Blo 583288 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B990913 : Blo 583288 990913 := bstep (se 2 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 990913 = 743185) B743185
theorem B1973969 : Blo 583288 1973969 := bstep (se 2 (by rfl) ⟨740238, by rfl⟩ : syracuseStep 1973969 = 1480477) B1480477
theorem B990947 : Blo 583288 990947 := bstep (se 1 (by rfl) ⟨743210, by rfl⟩ : syracuseStep 990947 = 1486421) B1486421
theorem B892721 : Blo 583288 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B1482563 : Blo 583288 1482563 := bstep (se 1 (by rfl) ⟨1111922, by rfl⟩ : syracuseStep 1482563 = 2223845) B2223845
theorem B1318769 : Blo 583288 1318769 := bstep (se 2 (by rfl) ⟨494538, by rfl⟩ : syracuseStep 1318769 = 989077) B989077
theorem B1318787 : Blo 583288 1318787 := bstep (se 1 (by rfl) ⟨989090, by rfl⟩ : syracuseStep 1318787 = 1978181) B1978181
theorem B2007089 : Blo 583288 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B1319057 : Blo 583288 1319057 := bstep (se 2 (by rfl) ⟨494646, by rfl⟩ : syracuseStep 1319057 = 989293) B989293
theorem B1319075 : Blo 583288 1319075 := bstep (se 1 (by rfl) ⟨989306, by rfl⟩ : syracuseStep 1319075 = 1978613) B1978613
theorem B1974509 : Blo 583288 1974509 := bstep (se 3 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 1974509 = 740441) B740441
theorem B1876241 : Blo 583288 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1974563 : Blo 583288 1974563 := bstep (se 1 (by rfl) ⟨1480922, by rfl⟩ : syracuseStep 1974563 = 2961845) B2961845
theorem B1777997 : Blo 583288 1777997 := bstep (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) B666749
theorem B3547525 : Blo 583288 3547525 := bstep (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) B665161
theorem B2498957 : Blo 583288 2498957 := bstep (se 3 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 2498957 = 937109) B937109
theorem B1319345 : Blo 583288 1319345 := bstep (se 2 (by rfl) ⟨494754, by rfl⟩ : syracuseStep 1319345 = 989509) B989509
theorem B1319363 : Blo 583288 1319363 := bstep (se 1 (by rfl) ⟨989522, by rfl⟩ : syracuseStep 1319363 = 1979045) B1979045
theorem B2957795 : Blo 583288 2957795 := bstep (se 1 (by rfl) ⟨2218346, by rfl⟩ : syracuseStep 2957795 = 4436693) B4436693
theorem B2466289 : Blo 583288 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B1974833 : Blo 583288 1974833 := bstep (se 2 (by rfl) ⟨740562, by rfl⟩ : syracuseStep 1974833 = 1481125) B1481125
theorem B1319633 : Blo 583288 1319633 := bstep (se 2 (by rfl) ⟨494862, by rfl⟩ : syracuseStep 1319633 = 989725) B989725
theorem B1319651 : Blo 583288 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B1483505 : Blo 583288 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B1483555 : Blo 583288 1483555 := bstep (se 1 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 1483555 = 2225333) B2225333
theorem B3744589 : Blo 583288 3744589 := bstep (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) B1404221
theorem B1778531 : Blo 583288 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B1483697 : Blo 583288 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B1319921 : Blo 583288 1319921 := bstep (se 2 (by rfl) ⟨494970, by rfl⟩ : syracuseStep 1319921 = 989941) B989941
theorem B1319939 : Blo 583288 1319939 := bstep (se 1 (by rfl) ⟨989954, by rfl⟩ : syracuseStep 1319939 = 1979909) B1979909
theorem B1975373 : Blo 583288 1975373 := bstep (se 3 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 1975373 = 740765) B740765
theorem B1975427 : Blo 583288 1975427 := bstep (se 1 (by rfl) ⟨1481570, by rfl⟩ : syracuseStep 1975427 = 2963141) B2963141
theorem B1877165 : Blo 583288 1877165 := bstep (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) B703937
theorem B5612813 : Blo 583288 5612813 := bstep (se 3 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 5612813 = 2104805) B2104805
theorem B2958605 : Blo 583288 2958605 := bstep (se 3 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 2958605 = 1109477) B1109477
theorem B1320209 : Blo 583288 1320209 := bstep (se 2 (by rfl) ⟨495078, by rfl⟩ : syracuseStep 1320209 = 990157) B990157
theorem B1320227 : Blo 583288 1320227 := bstep (se 1 (by rfl) ⟨990170, by rfl⟩ : syracuseStep 1320227 = 1980341) B1980341
theorem B1877357 : Blo 583288 1877357 := bstep (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) B704009
theorem B1975697 : Blo 583288 1975697 := bstep (se 2 (by rfl) ⟨740886, by rfl⟩ : syracuseStep 1975697 = 1481773) B1481773
theorem B2663857 : Blo 583288 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B1320497 : Blo 583288 1320497 := bstep (se 2 (by rfl) ⟨495186, by rfl⟩ : syracuseStep 1320497 = 990373) B990373
theorem B1320515 : Blo 583288 1320515 := bstep (se 1 (by rfl) ⟨990386, by rfl⟩ : syracuseStep 1320515 = 1980773) B1980773
theorem B1582865 : Blo 583288 1582865 := bstep (se 2 (by rfl) ⟨593574, by rfl⟩ : syracuseStep 1582865 = 1187149) B1187149
theorem B1320785 : Blo 583288 1320785 := bstep (se 2 (by rfl) ⟨495294, by rfl⟩ : syracuseStep 1320785 = 990589) B990589
theorem B1320803 : Blo 583288 1320803 := bstep (se 1 (by rfl) ⟨990602, by rfl⟩ : syracuseStep 1320803 = 1981205) B1981205
theorem B4433777 : Blo 583288 4433777 := bstep (se 2 (by rfl) ⟨1662666, by rfl⟩ : syracuseStep 4433777 = 3325333) B3325333
theorem B1582993 : Blo 583288 1582993 := bstep (se 2 (by rfl) ⟨593622, by rfl⟩ : syracuseStep 1582993 = 1187245) B1187245
theorem B1484689 : Blo 583288 1484689 := bstep (se 2 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 1484689 = 1113517) B1113517
theorem B1976237 : Blo 583288 1976237 := bstep (se 3 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 1976237 = 741089) B741089
theorem B7579619 : Blo 583288 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B1976291 : Blo 583288 1976291 := bstep (se 1 (by rfl) ⟨1482218, by rfl⟩ : syracuseStep 1976291 = 2964437) B2964437
theorem B1321073 : Blo 583288 1321073 := bstep (se 2 (by rfl) ⟨495402, by rfl⟩ : syracuseStep 1321073 = 990805) B990805
theorem B1321091 : Blo 583288 1321091 := bstep (se 1 (by rfl) ⟨990818, by rfl⟩ : syracuseStep 1321091 = 1981637) B1981637
theorem B1484963 : Blo 583288 1484963 := bstep (se 1 (by rfl) ⟨1113722, by rfl⟩ : syracuseStep 1484963 = 2227445) B2227445
theorem B1976561 : Blo 583288 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B633091 : Blo 583288 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B1485155 : Blo 583288 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B1321361 : Blo 583288 1321361 := bstep (se 2 (by rfl) ⟨495510, by rfl⟩ : syracuseStep 1321361 = 991021) B991021
theorem B1321379 : Blo 583288 1321379 := bstep (se 1 (by rfl) ⟨991034, by rfl⟩ : syracuseStep 1321379 = 1982069) B1982069
theorem B1583555 : Blo 583288 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B8006129 : Blo 583288 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B1977101 : Blo 583288 1977101 := bstep (se 3 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 1977101 = 741413) B741413
theorem B1977155 : Blo 583288 1977155 := bstep (se 1 (by rfl) ⟨1482866, by rfl⟩ : syracuseStep 1977155 = 2965733) B2965733
theorem B2665315 : Blo 583288 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B2370467 : Blo 583288 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B1977425 : Blo 583288 1977425 := bstep (se 2 (by rfl) ⟨741534, by rfl⟩ : syracuseStep 1977425 = 1483069) B1483069
theorem B1879139 : Blo 583288 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B1486097 : Blo 583288 1486097 := bstep (se 2 (by rfl) ⟨557286, by rfl⟩ : syracuseStep 1486097 = 1114573) B1114573
theorem B1486147 : Blo 583288 1486147 := bstep (se 1 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 1486147 = 2229221) B2229221
theorem B2502065 : Blo 583288 2502065 := bstep (se 2 (by rfl) ⟨938274, by rfl⟩ : syracuseStep 2502065 = 1876549) B1876549
theorem B1486289 : Blo 583288 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B1977965 : Blo 583288 1977965 := bstep (se 3 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 1977965 = 741737) B741737
theorem B1978019 : Blo 583288 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B831379 : Blo 583288 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B1978289 : Blo 583288 1978289 := bstep (se 2 (by rfl) ⟨741858, by rfl⟩ : syracuseStep 1978289 = 1483717) B1483717
theorem B2895793 : Blo 583288 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B2961521 : Blo 583288 2961521 := bstep (se 2 (by rfl) ⟨1110570, by rfl⟩ : syracuseStep 2961521 = 2221141) B2221141
theorem B6664517 : Blo 583288 6664517 := bstep (se 4 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 6664517 = 1249597) B1249597
theorem B1978829 : Blo 583288 1978829 := bstep (se 3 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 1978829 = 742061) B742061
theorem B1978883 : Blo 583288 1978883 := bstep (se 1 (by rfl) ⟨1484162, by rfl⟩ : syracuseStep 1978883 = 2968325) B2968325
theorem B3322417 : Blo 583288 3322417 := bstep (se 2 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 3322417 = 2491813) B2491813
theorem B701011 : Blo 583288 701011 := bstep (se 1 (by rfl) ⟨525758, by rfl⟩ : syracuseStep 701011 = 1051517) B1051517
theorem B2503331 : Blo 583288 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B1979153 : Blo 583288 1979153 := bstep (se 2 (by rfl) ⟨742182, by rfl⟩ : syracuseStep 1979153 = 1484365) B1484365
theorem B832513 : Blo 583288 832513 := bstep (se 2 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 832513 = 624385) B624385
theorem B832609 : Blo 583288 832609 := bstep (se 2 (by rfl) ⟨312228, by rfl⟩ : syracuseStep 832609 = 624457) B624457
theorem B3748997 : Blo 583288 3748997 := bstep (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) B702937
theorem B1881265 : Blo 583288 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1979693 : Blo 583288 1979693 := bstep (se 3 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 1979693 = 742385) B742385
theorem B1979747 : Blo 583288 1979747 := bstep (se 1 (by rfl) ⟨1484810, by rfl⟩ : syracuseStep 1979747 = 2969621) B2969621
theorem B2962979 : Blo 583288 2962979 := bstep (se 1 (by rfl) ⟨2222234, by rfl⟩ : syracuseStep 2962979 = 4444469) B4444469
theorem B833105 : Blo 583288 833105 := bstep (se 2 (by rfl) ⟨312414, by rfl⟩ : syracuseStep 833105 = 624829) B624829
theorem B1980017 : Blo 583288 1980017 := bstep (se 2 (by rfl) ⟨742506, by rfl⟩ : syracuseStep 1980017 = 1485013) B1485013
theorem B1685261 : Blo 583288 1685261 := bstep (se 3 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 1685261 = 631973) B631973
theorem B1718083 : Blo 583288 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B3323875 : Blo 583288 3323875 := bstep (se 1 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 3323875 = 4985813) B4985813
theorem B1783811 : Blo 583288 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B2373745 : Blo 583288 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B1980557 : Blo 583288 1980557 := bstep (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) B742709
theorem B1980611 : Blo 583288 1980611 := bstep (se 1 (by rfl) ⟨1485458, by rfl⟩ : syracuseStep 1980611 = 2970917) B2970917
theorem B3553541 : Blo 583288 3553541 := bstep (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) B666289
theorem B2963789 : Blo 583288 2963789 := bstep (se 3 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 2963789 = 1111421) B1111421
theorem B702803 : Blo 583288 702803 := bstep (se 1 (by rfl) ⟨527102, by rfl⟩ : syracuseStep 702803 = 1054205) B1054205
theorem B1784177 : Blo 583288 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B833971 : Blo 583288 833971 := bstep (se 1 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 833971 = 1250957) B1250957
theorem B1980881 : Blo 583288 1980881 := bstep (se 2 (by rfl) ⟨742830, by rfl⟩ : syracuseStep 1980881 = 1485661) B1485661
theorem B3324401 : Blo 583288 3324401 := bstep (se 2 (by rfl) ⟨1246650, by rfl⟩ : syracuseStep 3324401 = 2493301) B2493301
theorem B834067 : Blo 583288 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B703091 : Blo 583288 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B703283 : Blo 583288 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B1981421 : Blo 583288 1981421 := bstep (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) B743033
theorem B834563 : Blo 583288 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B3750947 : Blo 583288 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B1981475 : Blo 583288 1981475 := bstep (se 1 (by rfl) ⟨1486106, by rfl⟩ : syracuseStep 1981475 = 2972213) B2972213
theorem B5356613 : Blo 583288 5356613 := bstep (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) B1004365
theorem B1785137 : Blo 583288 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B1981745 : Blo 583288 1981745 := bstep (se 2 (by rfl) ⟨743154, by rfl⟩ : syracuseStep 1981745 = 1486309) B1486309
theorem B2375075 : Blo 583288 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B900721 : Blo 583288 900721 := bstep (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) B675541
theorem B835201 : Blo 583288 835201 := bstep (se 2 (by rfl) ⟨313200, by rfl⟩ : syracuseStep 835201 = 626401) B626401
theorem B60702605 : Blo 583288 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B3325859 : Blo 583288 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B835537 : Blo 583288 835537 := bstep (se 2 (by rfl) ⟨313326, by rfl⟩ : syracuseStep 835537 = 626653) B626653
theorem B2507021 : Blo 583288 2507021 := bstep (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) B940133
theorem B999761 : Blo 583288 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B836129 : Blo 583288 836129 := bstep (se 2 (by rfl) ⟨313548, by rfl⟩ : syracuseStep 836129 = 627097) B627097
theorem B1000369 : Blo 583288 1000369 := bstep (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) B750277
theorem B1000561 : Blo 583288 1000561 := bstep (se 2 (by rfl) ⟨375210, by rfl⟩ : syracuseStep 1000561 = 750421) B750421
theorem B935059 : Blo 583288 935059 := bstep (se 1 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 935059 = 1402589) B1402589
theorem B2966705 : Blo 583288 2966705 := bstep (se 2 (by rfl) ⟨1112514, by rfl⟩ : syracuseStep 2966705 = 2225029) B2225029
theorem B738659 : Blo 583288 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B4015493 : Blo 583288 4015493 := bstep (se 4 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 4015493 = 752905) B752905
theorem B935315 : Blo 583288 935315 := bstep (se 1 (by rfl) ⟨701486, by rfl⟩ : syracuseStep 935315 = 1402973) B1402973
theorem B1263107 : Blo 583288 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B3753485 : Blo 583288 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B1001219 : Blo 583288 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B3327749 : Blo 583288 3327749 := bstep (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) B623953
theorem B902977 : Blo 583288 902977 := bstep (se 2 (by rfl) ⟨338616, by rfl⟩ : syracuseStep 902977 = 677233) B677233
theorem B6670349 : Blo 583288 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B739363 : Blo 583288 739363 := bstep (se 1 (by rfl) ⟨554522, by rfl⟩ : syracuseStep 739363 = 1109045) B1109045
theorem B1001521 : Blo 583288 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B936019 : Blo 583288 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B739459 : Blo 583288 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B5621957 : Blo 583288 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B2672909 : Blo 583288 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B936289 : Blo 583288 936289 := bstep (se 2 (by rfl) ⟨351108, by rfl⟩ : syracuseStep 936289 = 702217) B702217
theorem B7588237 : Blo 583288 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B936353 : Blo 583288 936353 := bstep (se 2 (by rfl) ⟨351132, by rfl⟩ : syracuseStep 936353 = 702265) B702265
theorem B2968163 : Blo 583288 2968163 := bstep (se 1 (by rfl) ⟨2226122, by rfl⟩ : syracuseStep 2968163 = 4452245) B4452245
theorem B739955 : Blo 583288 739955 := bstep (se 1 (by rfl) ⟨554966, by rfl⟩ : syracuseStep 739955 = 1109933) B1109933
theorem B772915 : Blo 583288 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B10832753 : Blo 583288 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B13519757 : Blo 583288 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B2804813 : Blo 583288 2804813 := bstep (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) B1051805
theorem B740659 : Blo 583288 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B2215309 : Blo 583288 2215309 := bstep (se 3 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 2215309 = 830741) B830741
theorem B2968973 : Blo 583288 2968973 := bstep (se 3 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 2968973 = 1113365) B1113365
theorem B6344077 : Blo 583288 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B740755 : Blo 583288 740755 := bstep (se 1 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 740755 = 1111133) B1111133
theorem B3558917 : Blo 583288 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B741251 : Blo 583288 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B938083 : Blo 583288 938083 := bstep (se 1 (by rfl) ⟨703562, by rfl⟩ : syracuseStep 938083 = 1407125) B1407125
theorem B6312077 : Blo 583288 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B2216099 : Blo 583288 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B1331491 : Blo 583288 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B17125829 : Blo 583288 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B938531 : Blo 583288 938531 := bstep (se 1 (by rfl) ⟨703898, by rfl⟩ : syracuseStep 938531 = 1407797) B1407797
theorem B741955 : Blo 583288 741955 := bstep (se 1 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 741955 = 1112933) B1112933
theorem B742051 : Blo 583288 742051 := bstep (se 1 (by rfl) ⟨556538, by rfl⟩ : syracuseStep 742051 = 1113077) B1113077
theorem B3166897 : Blo 583288 3166897 := bstep (se 2 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 3166897 = 2375173) B2375173
theorem B2216753 : Blo 583288 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B6673265 : Blo 583288 6673265 := bstep (se 2 (by rfl) ⟨2502474, by rfl⟩ : syracuseStep 6673265 = 5004949) B5004949
theorem B939089 : Blo 583288 939089 := bstep (se 2 (by rfl) ⟨352158, by rfl⟩ : syracuseStep 939089 = 704317) B704317
theorem B742547 : Blo 583288 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B1692881 : Blo 583288 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B939313 : Blo 583288 939313 := bstep (se 2 (by rfl) ⟨352242, by rfl⟩ : syracuseStep 939313 = 704485) B704485
theorem B939377 : Blo 583288 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B939505 : Blo 583288 939505 := bstep (se 2 (by rfl) ⟨352314, by rfl⟩ : syracuseStep 939505 = 704629) B704629
theorem B743251 : Blo 583288 743251 := bstep (se 1 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 743251 = 1114877) B1114877
theorem B7133197 : Blo 583288 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B4216931 : Blo 583288 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2218211 : Blo 583288 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B2218225 : Blo 583288 2218225 := bstep (se 2 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 2218225 = 1663669) B1663669
theorem B2971889 : Blo 583288 2971889 := bstep (se 2 (by rfl) ⟨1114458, by rfl⟩ : syracuseStep 2971889 = 2228917) B2228917
theorem B874961 : Blo 583288 874961 := bstep (se 2 (by rfl) ⟨328110, by rfl⟩ : syracuseStep 874961 = 656221) B656221
theorem B874979 : Blo 583288 874979 := bstep (se 1 (by rfl) ⟨656234, by rfl⟩ : syracuseStep 874979 = 1312469) B1312469
theorem B875009 : Blo 583288 875009 := bstep (se 2 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 875009 = 656257) B656257
theorem B875027 : Blo 583288 875027 := bstep (se 1 (by rfl) ⟨656270, by rfl⟩ : syracuseStep 875027 = 1312541) B1312541
theorem B875057 : Blo 583288 875057 := bstep (se 2 (by rfl) ⟨328146, by rfl⟩ : syracuseStep 875057 = 656293) B656293
theorem B875075 : Blo 583288 875075 := bstep (se 1 (by rfl) ⟨656306, by rfl⟩ : syracuseStep 875075 = 1312613) B1312613
theorem B875105 : Blo 583288 875105 := bstep (se 2 (by rfl) ⟨328164, by rfl⟩ : syracuseStep 875105 = 656329) B656329
theorem B875123 : Blo 583288 875123 := bstep (se 1 (by rfl) ⟨656342, by rfl⟩ : syracuseStep 875123 = 1312685) B1312685
theorem B875153 : Blo 583288 875153 := bstep (se 2 (by rfl) ⟨328182, by rfl⟩ : syracuseStep 875153 = 656365) B656365
theorem B875171 : Blo 583288 875171 := bstep (se 1 (by rfl) ⟨656378, by rfl⟩ : syracuseStep 875171 = 1312757) B1312757
theorem B875201 : Blo 583288 875201 := bstep (se 2 (by rfl) ⟨328200, by rfl⟩ : syracuseStep 875201 = 656401) B656401
theorem B875219 : Blo 583288 875219 := bstep (se 1 (by rfl) ⟨656414, by rfl⟩ : syracuseStep 875219 = 1312829) B1312829
theorem B875249 : Blo 583288 875249 := bstep (se 2 (by rfl) ⟨328218, by rfl⟩ : syracuseStep 875249 = 656437) B656437
theorem B875267 : Blo 583288 875267 := bstep (se 1 (by rfl) ⟨656450, by rfl⟩ : syracuseStep 875267 = 1312901) B1312901
theorem B875297 : Blo 583288 875297 := bstep (se 2 (by rfl) ⟨328236, by rfl⟩ : syracuseStep 875297 = 656473) B656473
theorem B1334065 : Blo 583288 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B875315 : Blo 583288 875315 := bstep (se 1 (by rfl) ⟨656486, by rfl⟩ : syracuseStep 875315 = 1312973) B1312973
theorem B875345 : Blo 583288 875345 := bstep (se 2 (by rfl) ⟨328254, by rfl⟩ : syracuseStep 875345 = 656509) B656509
theorem B875363 : Blo 583288 875363 := bstep (se 1 (by rfl) ⟨656522, by rfl⟩ : syracuseStep 875363 = 1313045) B1313045
theorem B875393 : Blo 583288 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B875411 : Blo 583288 875411 := bstep (se 1 (by rfl) ⟨656558, by rfl⟩ : syracuseStep 875411 = 1313117) B1313117
theorem B875441 : Blo 583288 875441 := bstep (se 2 (by rfl) ⟨328290, by rfl⟩ : syracuseStep 875441 = 656581) B656581
theorem B875459 : Blo 583288 875459 := bstep (se 1 (by rfl) ⟨656594, by rfl⟩ : syracuseStep 875459 = 1313189) B1313189
theorem B875489 : Blo 583288 875489 := bstep (se 2 (by rfl) ⟨328308, by rfl⟩ : syracuseStep 875489 = 656617) B656617
theorem B875507 : Blo 583288 875507 := bstep (se 1 (by rfl) ⟨656630, by rfl⟩ : syracuseStep 875507 = 1313261) B1313261
theorem B875537 : Blo 583288 875537 := bstep (se 2 (by rfl) ⟨328326, by rfl⟩ : syracuseStep 875537 = 656653) B656653
theorem B875555 : Blo 583288 875555 := bstep (se 1 (by rfl) ⟨656666, by rfl⟩ : syracuseStep 875555 = 1313333) B1313333
theorem B875585 : Blo 583288 875585 := bstep (se 2 (by rfl) ⟨328344, by rfl⟩ : syracuseStep 875585 = 656689) B656689
theorem B1662029 : Blo 583288 1662029 := bstep (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) B623261
theorem B875603 : Blo 583288 875603 := bstep (se 1 (by rfl) ⟨656702, by rfl⟩ : syracuseStep 875603 = 1313405) B1313405
theorem B875633 : Blo 583288 875633 := bstep (se 2 (by rfl) ⟨328362, by rfl⟩ : syracuseStep 875633 = 656725) B656725
theorem B875651 : Blo 583288 875651 := bstep (se 1 (by rfl) ⟨656738, by rfl⟩ : syracuseStep 875651 = 1313477) B1313477
theorem B875681 : Blo 583288 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B875699 : Blo 583288 875699 := bstep (se 1 (by rfl) ⟨656774, by rfl⟩ : syracuseStep 875699 = 1313549) B1313549
theorem B875729 : Blo 583288 875729 := bstep (se 2 (by rfl) ⟨328398, by rfl⟩ : syracuseStep 875729 = 656797) B656797
theorem B875747 : Blo 583288 875747 := bstep (se 1 (by rfl) ⟨656810, by rfl⟩ : syracuseStep 875747 = 1313621) B1313621
theorem B875777 : Blo 583288 875777 := bstep (se 2 (by rfl) ⟨328416, by rfl⟩ : syracuseStep 875777 = 656833) B656833
theorem B1662211 : Blo 583288 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B875795 : Blo 583288 875795 := bstep (se 1 (by rfl) ⟨656846, by rfl⟩ : syracuseStep 875795 = 1313693) B1313693
theorem B1662257 : Blo 583288 1662257 := bstep (se 2 (by rfl) ⟨623346, by rfl⟩ : syracuseStep 1662257 = 1246693) B1246693
theorem B875825 : Blo 583288 875825 := bstep (se 2 (by rfl) ⟨328434, by rfl⟩ : syracuseStep 875825 = 656869) B656869
theorem B875843 : Blo 583288 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B875873 : Blo 583288 875873 := bstep (se 2 (by rfl) ⟨328452, by rfl⟩ : syracuseStep 875873 = 656905) B656905
theorem B875891 : Blo 583288 875891 := bstep (se 1 (by rfl) ⟨656918, by rfl⟩ : syracuseStep 875891 = 1313837) B1313837
theorem B875921 : Blo 583288 875921 := bstep (se 2 (by rfl) ⟨328470, by rfl⟩ : syracuseStep 875921 = 656941) B656941
theorem B875939 : Blo 583288 875939 := bstep (se 1 (by rfl) ⟨656954, by rfl⟩ : syracuseStep 875939 = 1313909) B1313909
theorem B875969 : Blo 583288 875969 := bstep (se 2 (by rfl) ⟨328488, by rfl⟩ : syracuseStep 875969 = 656977) B656977
theorem B3333581 : Blo 583288 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B875987 : Blo 583288 875987 := bstep (se 1 (by rfl) ⟨656990, by rfl⟩ : syracuseStep 875987 = 1313981) B1313981
theorem B876017 : Blo 583288 876017 := bstep (se 2 (by rfl) ⟨328506, by rfl⟩ : syracuseStep 876017 = 657013) B657013
theorem B876035 : Blo 583288 876035 := bstep (se 1 (by rfl) ⟨657026, by rfl⟩ : syracuseStep 876035 = 1314053) B1314053
theorem B876065 : Blo 583288 876065 := bstep (se 2 (by rfl) ⟨328524, by rfl⟩ : syracuseStep 876065 = 657049) B657049
theorem B876083 : Blo 583288 876083 := bstep (se 1 (by rfl) ⟨657062, by rfl⟩ : syracuseStep 876083 = 1314125) B1314125
theorem B876113 : Blo 583288 876113 := bstep (se 2 (by rfl) ⟨328542, by rfl⟩ : syracuseStep 876113 = 657085) B657085
theorem B876131 : Blo 583288 876131 := bstep (se 1 (by rfl) ⟨657098, by rfl⟩ : syracuseStep 876131 = 1314197) B1314197
theorem B876161 : Blo 583288 876161 := bstep (se 2 (by rfl) ⟨328560, by rfl⟩ : syracuseStep 876161 = 657121) B657121
theorem B876179 : Blo 583288 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B2219683 : Blo 583288 2219683 := bstep (se 1 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 2219683 = 3329525) B3329525
theorem B876209 : Blo 583288 876209 := bstep (se 2 (by rfl) ⟨328578, by rfl⟩ : syracuseStep 876209 = 657157) B657157
theorem B876227 : Blo 583288 876227 := bstep (se 1 (by rfl) ⟨657170, by rfl⟩ : syracuseStep 876227 = 1314341) B1314341
theorem B876257 : Blo 583288 876257 := bstep (se 2 (by rfl) ⟨328596, by rfl⟩ : syracuseStep 876257 = 657193) B657193
theorem B876275 : Blo 583288 876275 := bstep (se 1 (by rfl) ⟨657206, by rfl⟩ : syracuseStep 876275 = 1314413) B1314413
theorem B876305 : Blo 583288 876305 := bstep (se 2 (by rfl) ⟨328614, by rfl⟩ : syracuseStep 876305 = 657229) B657229
theorem B876323 : Blo 583288 876323 := bstep (se 1 (by rfl) ⟨657242, by rfl⟩ : syracuseStep 876323 = 1314485) B1314485
theorem B876353 : Blo 583288 876353 := bstep (se 2 (by rfl) ⟨328632, by rfl⟩ : syracuseStep 876353 = 657265) B657265
theorem B3170117 : Blo 583288 3170117 := bstep (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) B594397
theorem B876371 : Blo 583288 876371 := bstep (se 1 (by rfl) ⟨657278, by rfl⟩ : syracuseStep 876371 = 1314557) B1314557
theorem B876401 : Blo 583288 876401 := bstep (se 2 (by rfl) ⟨328650, by rfl⟩ : syracuseStep 876401 = 657301) B657301
theorem B876419 : Blo 583288 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B876449 : Blo 583288 876449 := bstep (se 2 (by rfl) ⟨328668, by rfl⟩ : syracuseStep 876449 = 657337) B657337
theorem B876467 : Blo 583288 876467 := bstep (se 1 (by rfl) ⟨657350, by rfl⟩ : syracuseStep 876467 = 1314701) B1314701
theorem B876497 : Blo 583288 876497 := bstep (se 2 (by rfl) ⟨328686, by rfl⟩ : syracuseStep 876497 = 657373) B657373
theorem B876515 : Blo 583288 876515 := bstep (se 1 (by rfl) ⟨657386, by rfl⟩ : syracuseStep 876515 = 1314773) B1314773
theorem B876545 : Blo 583288 876545 := bstep (se 2 (by rfl) ⟨328704, by rfl⟩ : syracuseStep 876545 = 657409) B657409
theorem B876563 : Blo 583288 876563 := bstep (se 1 (by rfl) ⟨657422, by rfl⟩ : syracuseStep 876563 = 1314845) B1314845
theorem B876593 : Blo 583288 876593 := bstep (se 2 (by rfl) ⟨328722, by rfl⟩ : syracuseStep 876593 = 657445) B657445
theorem B876611 : Blo 583288 876611 := bstep (se 1 (by rfl) ⟨657458, by rfl⟩ : syracuseStep 876611 = 1314917) B1314917
theorem B876641 : Blo 583288 876641 := bstep (se 2 (by rfl) ⟨328740, by rfl⟩ : syracuseStep 876641 = 657481) B657481
theorem B876659 : Blo 583288 876659 := bstep (se 1 (by rfl) ⟨657494, by rfl⟩ : syracuseStep 876659 = 1314989) B1314989
theorem B876689 : Blo 583288 876689 := bstep (se 2 (by rfl) ⟨328758, by rfl⟩ : syracuseStep 876689 = 657517) B657517
theorem B876707 : Blo 583288 876707 := bstep (se 1 (by rfl) ⟨657530, by rfl⟩ : syracuseStep 876707 = 1315061) B1315061
theorem B876737 : Blo 583288 876737 := bstep (se 2 (by rfl) ⟨328776, by rfl⟩ : syracuseStep 876737 = 657553) B657553
theorem B876755 : Blo 583288 876755 := bstep (se 1 (by rfl) ⟨657566, by rfl⟩ : syracuseStep 876755 = 1315133) B1315133
theorem B876785 : Blo 583288 876785 := bstep (se 2 (by rfl) ⟨328794, by rfl⟩ : syracuseStep 876785 = 657589) B657589
theorem B876803 : Blo 583288 876803 := bstep (se 1 (by rfl) ⟨657602, by rfl⟩ : syracuseStep 876803 = 1315205) B1315205
theorem B876833 : Blo 583288 876833 := bstep (se 2 (by rfl) ⟨328812, by rfl⟩ : syracuseStep 876833 = 657625) B657625
theorem B876851 : Blo 583288 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B876881 : Blo 583288 876881 := bstep (se 2 (by rfl) ⟨328830, by rfl⟩ : syracuseStep 876881 = 657661) B657661
theorem B876899 : Blo 583288 876899 := bstep (se 1 (by rfl) ⟨657674, by rfl⟩ : syracuseStep 876899 = 1315349) B1315349
theorem B876929 : Blo 583288 876929 := bstep (se 2 (by rfl) ⟨328848, by rfl⟩ : syracuseStep 876929 = 657697) B657697
theorem B876947 : Blo 583288 876947 := bstep (se 1 (by rfl) ⟨657710, by rfl⟩ : syracuseStep 876947 = 1315421) B1315421
theorem B876977 : Blo 583288 876977 := bstep (se 2 (by rfl) ⟨328866, by rfl⟩ : syracuseStep 876977 = 657733) B657733
theorem B876995 : Blo 583288 876995 := bstep (se 1 (by rfl) ⟨657746, by rfl⟩ : syracuseStep 876995 = 1315493) B1315493
theorem B877025 : Blo 583288 877025 := bstep (se 2 (by rfl) ⟨328884, by rfl⟩ : syracuseStep 877025 = 657769) B657769
theorem B877043 : Blo 583288 877043 := bstep (se 1 (by rfl) ⟨657782, by rfl⟩ : syracuseStep 877043 = 1315565) B1315565
theorem B877073 : Blo 583288 877073 := bstep (se 2 (by rfl) ⟨328902, by rfl⟩ : syracuseStep 877073 = 657805) B657805
theorem B877091 : Blo 583288 877091 := bstep (se 1 (by rfl) ⟨657818, by rfl⟩ : syracuseStep 877091 = 1315637) B1315637
theorem B877121 : Blo 583288 877121 := bstep (se 2 (by rfl) ⟨328920, by rfl⟩ : syracuseStep 877121 = 657841) B657841
theorem B877139 : Blo 583288 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B877169 : Blo 583288 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B877187 : Blo 583288 877187 := bstep (se 1 (by rfl) ⟨657890, by rfl⟩ : syracuseStep 877187 = 1315781) B1315781
theorem B3367565 : Blo 583288 3367565 := bstep (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) B1262837
theorem B877217 : Blo 583288 877217 := bstep (se 2 (by rfl) ⟨328956, by rfl⟩ : syracuseStep 877217 = 657913) B657913
theorem B877235 : Blo 583288 877235 := bstep (se 1 (by rfl) ⟨657926, by rfl⟩ : syracuseStep 877235 = 1315853) B1315853
theorem B877265 : Blo 583288 877265 := bstep (se 2 (by rfl) ⟨328974, by rfl⟩ : syracuseStep 877265 = 657949) B657949
theorem B1663715 : Blo 583288 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B877283 : Blo 583288 877283 := bstep (se 1 (by rfl) ⟨657962, by rfl⟩ : syracuseStep 877283 = 1315925) B1315925
theorem B877313 : Blo 583288 877313 := bstep (se 2 (by rfl) ⟨328992, by rfl⟩ : syracuseStep 877313 = 657985) B657985
theorem B877331 : Blo 583288 877331 := bstep (se 1 (by rfl) ⟨657998, by rfl⟩ : syracuseStep 877331 = 1315997) B1315997
theorem B877361 : Blo 583288 877361 := bstep (se 2 (by rfl) ⟨329010, by rfl⟩ : syracuseStep 877361 = 658021) B658021
theorem B877379 : Blo 583288 877379 := bstep (se 1 (by rfl) ⟨658034, by rfl⟩ : syracuseStep 877379 = 1316069) B1316069
theorem B877409 : Blo 583288 877409 := bstep (se 2 (by rfl) ⟨329028, by rfl⟩ : syracuseStep 877409 = 658057) B658057
theorem B877427 : Blo 583288 877427 := bstep (se 1 (by rfl) ⟨658070, by rfl⟩ : syracuseStep 877427 = 1316141) B1316141
theorem B877457 : Blo 583288 877457 := bstep (se 2 (by rfl) ⟨329046, by rfl⟩ : syracuseStep 877457 = 658093) B658093
theorem B877475 : Blo 583288 877475 := bstep (se 1 (by rfl) ⟨658106, by rfl⟩ : syracuseStep 877475 = 1316213) B1316213
theorem B877505 : Blo 583288 877505 := bstep (se 2 (by rfl) ⟨329064, by rfl⟩ : syracuseStep 877505 = 658129) B658129
theorem B3761093 : Blo 583288 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B877523 : Blo 583288 877523 := bstep (se 1 (by rfl) ⟨658142, by rfl⟩ : syracuseStep 877523 = 1316285) B1316285
theorem B877553 : Blo 583288 877553 := bstep (se 2 (by rfl) ⟨329082, by rfl⟩ : syracuseStep 877553 = 658165) B658165
theorem B877571 : Blo 583288 877571 := bstep (se 1 (by rfl) ⟨658178, by rfl⟩ : syracuseStep 877571 = 1316357) B1316357
theorem B877601 : Blo 583288 877601 := bstep (se 2 (by rfl) ⟨329100, by rfl⟩ : syracuseStep 877601 = 658201) B658201
theorem B877619 : Blo 583288 877619 := bstep (se 1 (by rfl) ⟨658214, by rfl⟩ : syracuseStep 877619 = 1316429) B1316429
theorem B877649 : Blo 583288 877649 := bstep (se 2 (by rfl) ⟨329118, by rfl⟩ : syracuseStep 877649 = 658237) B658237
theorem B877667 : Blo 583288 877667 := bstep (se 1 (by rfl) ⟨658250, by rfl⟩ : syracuseStep 877667 = 1316501) B1316501
theorem B4809827 : Blo 583288 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B877697 : Blo 583288 877697 := bstep (se 2 (by rfl) ⟨329136, by rfl⟩ : syracuseStep 877697 = 658273) B658273
theorem B4220045 : Blo 583288 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B877715 : Blo 583288 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B877745 : Blo 583288 877745 := bstep (se 2 (by rfl) ⟨329154, by rfl⟩ : syracuseStep 877745 = 658309) B658309
theorem B877763 : Blo 583288 877763 := bstep (se 1 (by rfl) ⟨658322, by rfl⟩ : syracuseStep 877763 = 1316645) B1316645
theorem B877793 : Blo 583288 877793 := bstep (se 2 (by rfl) ⟨329172, by rfl⟩ : syracuseStep 877793 = 658345) B658345
theorem B877811 : Blo 583288 877811 := bstep (se 1 (by rfl) ⟨658358, by rfl⟩ : syracuseStep 877811 = 1316717) B1316717
theorem B877841 : Blo 583288 877841 := bstep (se 2 (by rfl) ⟨329190, by rfl⟩ : syracuseStep 877841 = 658381) B658381
theorem B877859 : Blo 583288 877859 := bstep (se 1 (by rfl) ⟨658394, by rfl⟩ : syracuseStep 877859 = 1316789) B1316789
theorem B877889 : Blo 583288 877889 := bstep (se 2 (by rfl) ⟨329208, by rfl⟩ : syracuseStep 877889 = 658417) B658417
theorem B877907 : Blo 583288 877907 := bstep (se 1 (by rfl) ⟨658430, by rfl⟩ : syracuseStep 877907 = 1316861) B1316861
theorem B877937 : Blo 583288 877937 := bstep (se 2 (by rfl) ⟨329226, by rfl⟩ : syracuseStep 877937 = 658453) B658453
theorem B877955 : Blo 583288 877955 := bstep (se 1 (by rfl) ⟨658466, by rfl⟩ : syracuseStep 877955 = 1316933) B1316933
theorem B877985 : Blo 583288 877985 := bstep (se 2 (by rfl) ⟨329244, by rfl⟩ : syracuseStep 877985 = 658489) B658489
theorem B878003 : Blo 583288 878003 := bstep (se 1 (by rfl) ⟨658502, by rfl⟩ : syracuseStep 878003 = 1317005) B1317005
theorem B878033 : Blo 583288 878033 := bstep (se 2 (by rfl) ⟨329262, by rfl⟩ : syracuseStep 878033 = 658525) B658525
theorem B1107427 : Blo 583288 1107427 := bstep (se 1 (by rfl) ⟨830570, by rfl⟩ : syracuseStep 1107427 = 1661141) B1661141
theorem B878051 : Blo 583288 878051 := bstep (se 1 (by rfl) ⟨658538, by rfl⟩ : syracuseStep 878051 = 1317077) B1317077
theorem B878081 : Blo 583288 878081 := bstep (se 2 (by rfl) ⟨329280, by rfl⟩ : syracuseStep 878081 = 658561) B658561
theorem B878099 : Blo 583288 878099 := bstep (se 1 (by rfl) ⟨658574, by rfl⟩ : syracuseStep 878099 = 1317149) B1317149
theorem B878129 : Blo 583288 878129 := bstep (se 2 (by rfl) ⟨329298, by rfl⟩ : syracuseStep 878129 = 658597) B658597
theorem B878147 : Blo 583288 878147 := bstep (se 1 (by rfl) ⟨658610, by rfl⟩ : syracuseStep 878147 = 1317221) B1317221
theorem B878177 : Blo 583288 878177 := bstep (se 2 (by rfl) ⟨329316, by rfl⟩ : syracuseStep 878177 = 658633) B658633
theorem B878195 : Blo 583288 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B583299 : Blo 583288 583299 := bstep (se 1 (by rfl) ⟨437474, by rfl⟩ : syracuseStep 583299 = 874949) B874949
theorem B1107587 : Blo 583288 1107587 := bstep (se 1 (by rfl) ⟨830690, by rfl⟩ : syracuseStep 1107587 = 1661381) B1661381
theorem B3335813 : Blo 583288 3335813 := bstep (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) B625465
theorem B878225 : Blo 583288 878225 := bstep (se 2 (by rfl) ⟨329334, by rfl⟩ : syracuseStep 878225 = 658669) B658669
theorem B583315 : Blo 583288 583315 := bstep (se 1 (by rfl) ⟨437486, by rfl⟩ : syracuseStep 583315 = 874973) B874973
theorem B583331 : Blo 583288 583331 := bstep (se 1 (by rfl) ⟨437498, by rfl⟩ : syracuseStep 583331 = 874997) B874997
theorem B878243 : Blo 583288 878243 := bstep (se 1 (by rfl) ⟨658682, by rfl⟩ : syracuseStep 878243 = 1317365) B1317365
theorem B583347 : Blo 583288 583347 := bstep (se 1 (by rfl) ⟨437510, by rfl⟩ : syracuseStep 583347 = 875021) B875021
theorem B878273 : Blo 583288 878273 := bstep (se 2 (by rfl) ⟨329352, by rfl⟩ : syracuseStep 878273 = 658705) B658705
theorem B583363 : Blo 583288 583363 := bstep (se 1 (by rfl) ⟨437522, by rfl⟩ : syracuseStep 583363 = 875045) B875045
theorem B583379 : Blo 583288 583379 := bstep (se 1 (by rfl) ⟨437534, by rfl⟩ : syracuseStep 583379 = 875069) B875069
theorem B878291 : Blo 583288 878291 := bstep (se 1 (by rfl) ⟨658718, by rfl⟩ : syracuseStep 878291 = 1317437) B1317437
theorem B583395 : Blo 583288 583395 := bstep (se 1 (by rfl) ⟨437546, by rfl⟩ : syracuseStep 583395 = 875093) B875093
theorem B878321 : Blo 583288 878321 := bstep (se 2 (by rfl) ⟨329370, by rfl⟩ : syracuseStep 878321 = 658741) B658741
theorem B583411 : Blo 583288 583411 := bstep (se 1 (by rfl) ⟨437558, by rfl⟩ : syracuseStep 583411 = 875117) B875117
theorem B583427 : Blo 583288 583427 := bstep (se 1 (by rfl) ⟨437570, by rfl⟩ : syracuseStep 583427 = 875141) B875141
theorem B878339 : Blo 583288 878339 := bstep (se 1 (by rfl) ⟨658754, by rfl⟩ : syracuseStep 878339 = 1317509) B1317509
theorem B583443 : Blo 583288 583443 := bstep (se 1 (by rfl) ⟨437582, by rfl⟩ : syracuseStep 583443 = 875165) B875165
theorem B878369 : Blo 583288 878369 := bstep (se 2 (by rfl) ⟨329388, by rfl⟩ : syracuseStep 878369 = 658777) B658777
theorem B583459 : Blo 583288 583459 := bstep (se 1 (by rfl) ⟨437594, by rfl⟩ : syracuseStep 583459 = 875189) B875189
theorem B583475 : Blo 583288 583475 := bstep (se 1 (by rfl) ⟨437606, by rfl⟩ : syracuseStep 583475 = 875213) B875213
theorem B878387 : Blo 583288 878387 := bstep (se 1 (by rfl) ⟨658790, by rfl⟩ : syracuseStep 878387 = 1317581) B1317581
theorem B583491 : Blo 583288 583491 := bstep (se 1 (by rfl) ⟨437618, by rfl⟩ : syracuseStep 583491 = 875237) B875237
theorem B2221901 : Blo 583288 2221901 := bstep (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) B833213
theorem B3008333 : Blo 583288 3008333 := bstep (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) B1128125
theorem B878417 : Blo 583288 878417 := bstep (se 2 (by rfl) ⟨329406, by rfl⟩ : syracuseStep 878417 = 658813) B658813
theorem B583507 : Blo 583288 583507 := bstep (se 1 (by rfl) ⟨437630, by rfl⟩ : syracuseStep 583507 = 875261) B875261
theorem B583523 : Blo 583288 583523 := bstep (se 1 (by rfl) ⟨437642, by rfl⟩ : syracuseStep 583523 = 875285) B875285
theorem B878435 : Blo 583288 878435 := bstep (se 1 (by rfl) ⟨658826, by rfl⟩ : syracuseStep 878435 = 1317653) B1317653
theorem B14444401 : Blo 583288 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B583539 : Blo 583288 583539 := bstep (se 1 (by rfl) ⟨437654, by rfl⟩ : syracuseStep 583539 = 875309) B875309
theorem B878465 : Blo 583288 878465 := bstep (se 2 (by rfl) ⟨329424, by rfl⟩ : syracuseStep 878465 = 658849) B658849
theorem B583555 : Blo 583288 583555 := bstep (se 1 (by rfl) ⟨437666, by rfl⟩ : syracuseStep 583555 = 875333) B875333
theorem B583571 : Blo 583288 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B878483 : Blo 583288 878483 := bstep (se 1 (by rfl) ⟨658862, by rfl⟩ : syracuseStep 878483 = 1317725) B1317725
theorem B583587 : Blo 583288 583587 := bstep (se 1 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 583587 = 875381) B875381
theorem B1664945 : Blo 583288 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B878513 : Blo 583288 878513 := bstep (se 2 (by rfl) ⟨329442, by rfl⟩ : syracuseStep 878513 = 658885) B658885
theorem B583603 : Blo 583288 583603 := bstep (se 1 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 583603 = 875405) B875405
theorem B583619 : Blo 583288 583619 := bstep (se 1 (by rfl) ⟨437714, by rfl⟩ : syracuseStep 583619 = 875429) B875429
theorem B878531 : Blo 583288 878531 := bstep (se 1 (by rfl) ⟨658898, by rfl⟩ : syracuseStep 878531 = 1317797) B1317797
theorem B2779085 : Blo 583288 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B583635 : Blo 583288 583635 := bstep (se 1 (by rfl) ⟨437726, by rfl⟩ : syracuseStep 583635 = 875453) B875453
theorem B878561 : Blo 583288 878561 := bstep (se 2 (by rfl) ⟨329460, by rfl⟩ : syracuseStep 878561 = 658921) B658921
theorem B583651 : Blo 583288 583651 := bstep (se 1 (by rfl) ⟨437738, by rfl⟩ : syracuseStep 583651 = 875477) B875477
theorem B583667 : Blo 583288 583667 := bstep (se 1 (by rfl) ⟨437750, by rfl⟩ : syracuseStep 583667 = 875501) B875501
theorem B878579 : Blo 583288 878579 := bstep (se 1 (by rfl) ⟨658934, by rfl⟩ : syracuseStep 878579 = 1317869) B1317869
theorem B583683 : Blo 583288 583683 := bstep (se 1 (by rfl) ⟨437762, by rfl⟩ : syracuseStep 583683 = 875525) B875525
theorem B878609 : Blo 583288 878609 := bstep (se 2 (by rfl) ⟨329478, by rfl⟩ : syracuseStep 878609 = 658957) B658957
theorem B583699 : Blo 583288 583699 := bstep (se 1 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 583699 = 875549) B875549
theorem B583715 : Blo 583288 583715 := bstep (se 1 (by rfl) ⟨437786, by rfl⟩ : syracuseStep 583715 = 875573) B875573
theorem B1402915 : Blo 583288 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B878627 : Blo 583288 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B583731 : Blo 583288 583731 := bstep (se 1 (by rfl) ⟨437798, by rfl⟩ : syracuseStep 583731 = 875597) B875597
theorem B878657 : Blo 583288 878657 := bstep (se 2 (by rfl) ⟨329496, by rfl⟩ : syracuseStep 878657 = 658993) B658993
theorem B583747 : Blo 583288 583747 := bstep (se 1 (by rfl) ⟨437810, by rfl⟩ : syracuseStep 583747 = 875621) B875621
theorem B7596101 : Blo 583288 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B583763 : Blo 583288 583763 := bstep (se 1 (by rfl) ⟨437822, by rfl⟩ : syracuseStep 583763 = 875645) B875645
theorem B878675 : Blo 583288 878675 := bstep (se 1 (by rfl) ⟨659006, by rfl⟩ : syracuseStep 878675 = 1318013) B1318013
theorem B583779 : Blo 583288 583779 := bstep (se 1 (by rfl) ⟨437834, by rfl⟩ : syracuseStep 583779 = 875669) B875669
theorem B878705 : Blo 583288 878705 := bstep (se 2 (by rfl) ⟨329514, by rfl⟩ : syracuseStep 878705 = 659029) B659029
theorem B583795 : Blo 583288 583795 := bstep (se 1 (by rfl) ⟨437846, by rfl⟩ : syracuseStep 583795 = 875693) B875693
theorem B583811 : Blo 583288 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B878723 : Blo 583288 878723 := bstep (se 1 (by rfl) ⟨659042, by rfl⟩ : syracuseStep 878723 = 1318085) B1318085
theorem B583827 : Blo 583288 583827 := bstep (se 1 (by rfl) ⟨437870, by rfl⟩ : syracuseStep 583827 = 875741) B875741
theorem B878753 : Blo 583288 878753 := bstep (se 2 (by rfl) ⟨329532, by rfl⟩ : syracuseStep 878753 = 659065) B659065
theorem B583843 : Blo 583288 583843 := bstep (se 1 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 583843 = 875765) B875765
theorem B583859 : Blo 583288 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B878771 : Blo 583288 878771 := bstep (se 1 (by rfl) ⟨659078, by rfl⟩ : syracuseStep 878771 = 1318157) B1318157
theorem B583875 : Blo 583288 583875 := bstep (se 1 (by rfl) ⟨437906, by rfl⟩ : syracuseStep 583875 = 875813) B875813
theorem B878801 : Blo 583288 878801 := bstep (se 2 (by rfl) ⟨329550, by rfl⟩ : syracuseStep 878801 = 659101) B659101
theorem B583891 : Blo 583288 583891 := bstep (se 1 (by rfl) ⟨437918, by rfl⟩ : syracuseStep 583891 = 875837) B875837
theorem B583907 : Blo 583288 583907 := bstep (se 1 (by rfl) ⟨437930, by rfl⟩ : syracuseStep 583907 = 875861) B875861
theorem B878819 : Blo 583288 878819 := bstep (se 1 (by rfl) ⟨659114, by rfl⟩ : syracuseStep 878819 = 1318229) B1318229
theorem B583923 : Blo 583288 583923 := bstep (se 1 (by rfl) ⟨437942, by rfl⟩ : syracuseStep 583923 = 875885) B875885
theorem B878849 : Blo 583288 878849 := bstep (se 2 (by rfl) ⟨329568, by rfl⟩ : syracuseStep 878849 = 659137) B659137
theorem B583939 : Blo 583288 583939 := bstep (se 1 (by rfl) ⟨437954, by rfl⟩ : syracuseStep 583939 = 875909) B875909
theorem B583955 : Blo 583288 583955 := bstep (se 1 (by rfl) ⟨437966, by rfl⟩ : syracuseStep 583955 = 875933) B875933
theorem B878867 : Blo 583288 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B583971 : Blo 583288 583971 := bstep (se 1 (by rfl) ⟨437978, by rfl⟩ : syracuseStep 583971 = 875957) B875957
theorem B3336497 : Blo 583288 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B878897 : Blo 583288 878897 := bstep (se 2 (by rfl) ⟨329586, by rfl⟩ : syracuseStep 878897 = 659173) B659173
theorem B583987 : Blo 583288 583987 := bstep (se 1 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 583987 = 875981) B875981
theorem B584003 : Blo 583288 584003 := bstep (se 1 (by rfl) ⟨438002, by rfl⟩ : syracuseStep 584003 = 876005) B876005
theorem B878915 : Blo 583288 878915 := bstep (se 1 (by rfl) ⟨659186, by rfl⟩ : syracuseStep 878915 = 1318373) B1318373
theorem B584019 : Blo 583288 584019 := bstep (se 1 (by rfl) ⟨438014, by rfl⟩ : syracuseStep 584019 = 876029) B876029
theorem B878945 : Blo 583288 878945 := bstep (se 2 (by rfl) ⟨329604, by rfl⟩ : syracuseStep 878945 = 659209) B659209
theorem B584035 : Blo 583288 584035 := bstep (se 1 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 584035 = 876053) B876053
theorem B584051 : Blo 583288 584051 := bstep (se 1 (by rfl) ⟨438038, by rfl⟩ : syracuseStep 584051 = 876077) B876077
theorem B878963 : Blo 583288 878963 := bstep (se 1 (by rfl) ⟨659222, by rfl⟩ : syracuseStep 878963 = 1318445) B1318445
theorem B584067 : Blo 583288 584067 := bstep (se 1 (by rfl) ⟨438050, by rfl⟩ : syracuseStep 584067 = 876101) B876101
theorem B878993 : Blo 583288 878993 := bstep (se 2 (by rfl) ⟨329622, by rfl⟩ : syracuseStep 878993 = 659245) B659245
theorem B584083 : Blo 583288 584083 := bstep (se 1 (by rfl) ⟨438062, by rfl⟩ : syracuseStep 584083 = 876125) B876125
theorem B584099 : Blo 583288 584099 := bstep (se 1 (by rfl) ⟨438074, by rfl⟩ : syracuseStep 584099 = 876149) B876149
theorem B879011 : Blo 583288 879011 := bstep (se 1 (by rfl) ⟨659258, by rfl⟩ : syracuseStep 879011 = 1318517) B1318517
theorem B584115 : Blo 583288 584115 := bstep (se 1 (by rfl) ⟨438086, by rfl⟩ : syracuseStep 584115 = 876173) B876173
theorem B879041 : Blo 583288 879041 := bstep (se 2 (by rfl) ⟨329640, by rfl⟩ : syracuseStep 879041 = 659281) B659281
theorem B584131 : Blo 583288 584131 := bstep (se 1 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 584131 = 876197) B876197
theorem B3434957 : Blo 583288 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B584147 : Blo 583288 584147 := bstep (se 1 (by rfl) ⟨438110, by rfl⟩ : syracuseStep 584147 = 876221) B876221
theorem B879059 : Blo 583288 879059 := bstep (se 1 (by rfl) ⟨659294, by rfl⟩ : syracuseStep 879059 = 1318589) B1318589
theorem B584163 : Blo 583288 584163 := bstep (se 1 (by rfl) ⟨438122, by rfl⟩ : syracuseStep 584163 = 876245) B876245
theorem B4450787 : Blo 583288 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B879089 : Blo 583288 879089 := bstep (se 2 (by rfl) ⟨329658, by rfl⟩ : syracuseStep 879089 = 659317) B659317
theorem B584179 : Blo 583288 584179 := bstep (se 1 (by rfl) ⟨438134, by rfl⟩ : syracuseStep 584179 = 876269) B876269
theorem B584195 : Blo 583288 584195 := bstep (se 1 (by rfl) ⟨438146, by rfl⟩ : syracuseStep 584195 = 876293) B876293
theorem B879107 : Blo 583288 879107 := bstep (se 1 (by rfl) ⟨659330, by rfl⟩ : syracuseStep 879107 = 1318661) B1318661
theorem B584211 : Blo 583288 584211 := bstep (se 1 (by rfl) ⟨438158, by rfl⟩ : syracuseStep 584211 = 876317) B876317
theorem B879137 : Blo 583288 879137 := bstep (se 2 (by rfl) ⟨329676, by rfl⟩ : syracuseStep 879137 = 659353) B659353
theorem B584227 : Blo 583288 584227 := bstep (se 1 (by rfl) ⟨438170, by rfl⟩ : syracuseStep 584227 = 876341) B876341
theorem B584243 : Blo 583288 584243 := bstep (se 1 (by rfl) ⟨438182, by rfl⟩ : syracuseStep 584243 = 876365) B876365
theorem B879155 : Blo 583288 879155 := bstep (se 1 (by rfl) ⟨659366, by rfl⟩ : syracuseStep 879155 = 1318733) B1318733
theorem B584259 : Blo 583288 584259 := bstep (se 1 (by rfl) ⟨438194, by rfl⟩ : syracuseStep 584259 = 876389) B876389
theorem B879185 : Blo 583288 879185 := bstep (se 2 (by rfl) ⟨329694, by rfl⟩ : syracuseStep 879185 = 659389) B659389
theorem B584275 : Blo 583288 584275 := bstep (se 1 (by rfl) ⟨438206, by rfl⟩ : syracuseStep 584275 = 876413) B876413
theorem B584291 : Blo 583288 584291 := bstep (se 1 (by rfl) ⟨438218, by rfl⟩ : syracuseStep 584291 = 876437) B876437
theorem B879203 : Blo 583288 879203 := bstep (se 1 (by rfl) ⟨659402, by rfl⟩ : syracuseStep 879203 = 1318805) B1318805
theorem B584307 : Blo 583288 584307 := bstep (se 1 (by rfl) ⟨438230, by rfl⟩ : syracuseStep 584307 = 876461) B876461
theorem B879233 : Blo 583288 879233 := bstep (se 2 (by rfl) ⟨329712, by rfl⟩ : syracuseStep 879233 = 659425) B659425
theorem B584323 : Blo 583288 584323 := bstep (se 1 (by rfl) ⟨438242, by rfl⟩ : syracuseStep 584323 = 876485) B876485
theorem B584339 : Blo 583288 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B879251 : Blo 583288 879251 := bstep (se 1 (by rfl) ⟨659438, by rfl⟩ : syracuseStep 879251 = 1318877) B1318877
theorem B584355 : Blo 583288 584355 := bstep (se 1 (by rfl) ⟨438266, by rfl⟩ : syracuseStep 584355 = 876533) B876533
theorem B1108657 : Blo 583288 1108657 := bstep (se 2 (by rfl) ⟨415746, by rfl⟩ : syracuseStep 1108657 = 831493) B831493
theorem B879281 : Blo 583288 879281 := bstep (se 2 (by rfl) ⟨329730, by rfl⟩ : syracuseStep 879281 = 659461) B659461
theorem B584371 : Blo 583288 584371 := bstep (se 1 (by rfl) ⟨438278, by rfl⟩ : syracuseStep 584371 = 876557) B876557
theorem B584387 : Blo 583288 584387 := bstep (se 1 (by rfl) ⟨438290, by rfl⟩ : syracuseStep 584387 = 876581) B876581
theorem B879299 : Blo 583288 879299 := bstep (se 1 (by rfl) ⟨659474, by rfl⟩ : syracuseStep 879299 = 1318949) B1318949
theorem B584403 : Blo 583288 584403 := bstep (se 1 (by rfl) ⟨438302, by rfl⟩ : syracuseStep 584403 = 876605) B876605
theorem B879329 : Blo 583288 879329 := bstep (se 2 (by rfl) ⟨329748, by rfl⟩ : syracuseStep 879329 = 659497) B659497
theorem B584419 : Blo 583288 584419 := bstep (se 1 (by rfl) ⟨438314, by rfl⟩ : syracuseStep 584419 = 876629) B876629
theorem B584435 : Blo 583288 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B879347 : Blo 583288 879347 := bstep (se 1 (by rfl) ⟨659510, by rfl⟩ : syracuseStep 879347 = 1319021) B1319021
theorem B584451 : Blo 583288 584451 := bstep (se 1 (by rfl) ⟨438338, by rfl⟩ : syracuseStep 584451 = 876677) B876677
theorem B879377 : Blo 583288 879377 := bstep (se 2 (by rfl) ⟨329766, by rfl⟩ : syracuseStep 879377 = 659533) B659533
theorem B584467 : Blo 583288 584467 := bstep (se 1 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 584467 = 876701) B876701
theorem B584483 : Blo 583288 584483 := bstep (se 1 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 584483 = 876725) B876725
theorem B879395 : Blo 583288 879395 := bstep (se 1 (by rfl) ⟨659546, by rfl⟩ : syracuseStep 879395 = 1319093) B1319093
theorem B584499 : Blo 583288 584499 := bstep (se 1 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 584499 = 876749) B876749
theorem B879425 : Blo 583288 879425 := bstep (se 2 (by rfl) ⟨329784, by rfl⟩ : syracuseStep 879425 = 659569) B659569
theorem B584515 : Blo 583288 584515 := bstep (se 1 (by rfl) ⟨438386, by rfl⟩ : syracuseStep 584515 = 876773) B876773
theorem B3566405 : Blo 583288 3566405 := bstep (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) B668701
theorem B584531 : Blo 583288 584531 := bstep (se 1 (by rfl) ⟨438398, by rfl⟩ : syracuseStep 584531 = 876797) B876797
theorem B879443 : Blo 583288 879443 := bstep (se 1 (by rfl) ⟨659582, by rfl⟩ : syracuseStep 879443 = 1319165) B1319165
theorem B584547 : Blo 583288 584547 := bstep (se 1 (by rfl) ⟨438410, by rfl⟩ : syracuseStep 584547 = 876821) B876821
theorem B879473 : Blo 583288 879473 := bstep (se 2 (by rfl) ⟨329802, by rfl⟩ : syracuseStep 879473 = 659605) B659605
theorem B584563 : Blo 583288 584563 := bstep (se 1 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 584563 = 876845) B876845
theorem B584579 : Blo 583288 584579 := bstep (se 1 (by rfl) ⟨438434, by rfl⟩ : syracuseStep 584579 = 876869) B876869
theorem B879491 : Blo 583288 879491 := bstep (se 1 (by rfl) ⟨659618, by rfl⟩ : syracuseStep 879491 = 1319237) B1319237
theorem B584595 : Blo 583288 584595 := bstep (se 1 (by rfl) ⟨438446, by rfl⟩ : syracuseStep 584595 = 876893) B876893
theorem B879521 : Blo 583288 879521 := bstep (se 2 (by rfl) ⟨329820, by rfl⟩ : syracuseStep 879521 = 659641) B659641
theorem B584611 : Blo 583288 584611 := bstep (se 1 (by rfl) ⟨438458, by rfl⟩ : syracuseStep 584611 = 876917) B876917
theorem B584627 : Blo 583288 584627 := bstep (se 1 (by rfl) ⟨438470, by rfl⟩ : syracuseStep 584627 = 876941) B876941
theorem B879539 : Blo 583288 879539 := bstep (se 1 (by rfl) ⟨659654, by rfl⟩ : syracuseStep 879539 = 1319309) B1319309
theorem B584643 : Blo 583288 584643 := bstep (se 1 (by rfl) ⟨438482, by rfl⟩ : syracuseStep 584643 = 876965) B876965
theorem B879569 : Blo 583288 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B584659 : Blo 583288 584659 := bstep (se 1 (by rfl) ⟨438494, by rfl⟩ : syracuseStep 584659 = 876989) B876989
theorem B584675 : Blo 583288 584675 := bstep (se 1 (by rfl) ⟨438506, by rfl⟩ : syracuseStep 584675 = 877013) B877013
theorem B879587 : Blo 583288 879587 := bstep (se 1 (by rfl) ⟨659690, by rfl⟩ : syracuseStep 879587 = 1319381) B1319381
theorem B584691 : Blo 583288 584691 := bstep (se 1 (by rfl) ⟨438518, by rfl⟩ : syracuseStep 584691 = 877037) B877037
theorem B879617 : Blo 583288 879617 := bstep (se 2 (by rfl) ⟨329856, by rfl⟩ : syracuseStep 879617 = 659713) B659713
theorem B584707 : Blo 583288 584707 := bstep (se 1 (by rfl) ⟨438530, by rfl⟩ : syracuseStep 584707 = 877061) B877061
theorem B584723 : Blo 583288 584723 := bstep (se 1 (by rfl) ⟨438542, by rfl⟩ : syracuseStep 584723 = 877085) B877085
theorem B879635 : Blo 583288 879635 := bstep (se 1 (by rfl) ⟨659726, by rfl⟩ : syracuseStep 879635 = 1319453) B1319453
theorem B584739 : Blo 583288 584739 := bstep (se 1 (by rfl) ⟨438554, by rfl⟩ : syracuseStep 584739 = 877109) B877109
theorem B879665 : Blo 583288 879665 := bstep (se 2 (by rfl) ⟨329874, by rfl⟩ : syracuseStep 879665 = 659749) B659749
theorem B584755 : Blo 583288 584755 := bstep (se 1 (by rfl) ⟨438566, by rfl⟩ : syracuseStep 584755 = 877133) B877133
theorem B584771 : Blo 583288 584771 := bstep (se 1 (by rfl) ⟨438578, by rfl⟩ : syracuseStep 584771 = 877157) B877157
theorem B879683 : Blo 583288 879683 := bstep (se 1 (by rfl) ⟨659762, by rfl⟩ : syracuseStep 879683 = 1319525) B1319525
theorem B584787 : Blo 583288 584787 := bstep (se 1 (by rfl) ⟨438590, by rfl⟩ : syracuseStep 584787 = 877181) B877181
theorem B879713 : Blo 583288 879713 := bstep (se 2 (by rfl) ⟨329892, by rfl⟩ : syracuseStep 879713 = 659785) B659785
theorem B584803 : Blo 583288 584803 := bstep (se 1 (by rfl) ⟨438602, by rfl⟩ : syracuseStep 584803 = 877205) B877205
theorem B584819 : Blo 583288 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B879731 : Blo 583288 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B584835 : Blo 583288 584835 := bstep (se 1 (by rfl) ⟨438626, by rfl⟩ : syracuseStep 584835 = 877253) B877253
theorem B1404049 : Blo 583288 1404049 := bstep (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) B1053037
theorem B879761 : Blo 583288 879761 := bstep (se 2 (by rfl) ⟨329910, by rfl⟩ : syracuseStep 879761 = 659821) B659821
theorem B584851 : Blo 583288 584851 := bstep (se 1 (by rfl) ⟨438638, by rfl⟩ : syracuseStep 584851 = 877277) B877277
theorem B584867 : Blo 583288 584867 := bstep (se 1 (by rfl) ⟨438650, by rfl⟩ : syracuseStep 584867 = 877301) B877301
theorem B879779 : Blo 583288 879779 := bstep (se 1 (by rfl) ⟨659834, by rfl⟩ : syracuseStep 879779 = 1319669) B1319669
theorem B584883 : Blo 583288 584883 := bstep (se 1 (by rfl) ⟨438662, by rfl⟩ : syracuseStep 584883 = 877325) B877325
theorem B879809 : Blo 583288 879809 := bstep (se 2 (by rfl) ⟨329928, by rfl⟩ : syracuseStep 879809 = 659857) B659857
theorem B584899 : Blo 583288 584899 := bstep (se 1 (by rfl) ⟨438674, by rfl⟩ : syracuseStep 584899 = 877349) B877349
theorem B584915 : Blo 583288 584915 := bstep (se 1 (by rfl) ⟨438686, by rfl⟩ : syracuseStep 584915 = 877373) B877373
theorem B879827 : Blo 583288 879827 := bstep (se 1 (by rfl) ⟨659870, by rfl⟩ : syracuseStep 879827 = 1319741) B1319741
theorem B584931 : Blo 583288 584931 := bstep (se 1 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 584931 = 877397) B877397
theorem B1502435 : Blo 583288 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B1404145 : Blo 583288 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B584947 : Blo 583288 584947 := bstep (se 1 (by rfl) ⟨438710, by rfl⟩ : syracuseStep 584947 = 877421) B877421
theorem B879857 : Blo 583288 879857 := bstep (se 2 (by rfl) ⟨329946, by rfl⟩ : syracuseStep 879857 = 659893) B659893
theorem B584963 : Blo 583288 584963 := bstep (se 1 (by rfl) ⟨438722, by rfl⟩ : syracuseStep 584963 = 877445) B877445
theorem B879875 : Blo 583288 879875 := bstep (se 1 (by rfl) ⟨659906, by rfl⟩ : syracuseStep 879875 = 1319813) B1319813
theorem B584979 : Blo 583288 584979 := bstep (se 1 (by rfl) ⟨438734, by rfl⟩ : syracuseStep 584979 = 877469) B877469
theorem B879905 : Blo 583288 879905 := bstep (se 2 (by rfl) ⟨329964, by rfl⟩ : syracuseStep 879905 = 659929) B659929
theorem B584995 : Blo 583288 584995 := bstep (se 1 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 584995 = 877493) B877493
theorem B585011 : Blo 583288 585011 := bstep (se 1 (by rfl) ⟨438758, by rfl⟩ : syracuseStep 585011 = 877517) B877517
theorem B879923 : Blo 583288 879923 := bstep (se 1 (by rfl) ⟨659942, by rfl⟩ : syracuseStep 879923 = 1319885) B1319885
theorem B585027 : Blo 583288 585027 := bstep (se 1 (by rfl) ⟨438770, by rfl⟩ : syracuseStep 585027 = 877541) B877541
theorem B6778181 : Blo 583288 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B879953 : Blo 583288 879953 := bstep (se 2 (by rfl) ⟨329982, by rfl⟩ : syracuseStep 879953 = 659965) B659965
theorem B585043 : Blo 583288 585043 := bstep (se 1 (by rfl) ⟨438782, by rfl⟩ : syracuseStep 585043 = 877565) B877565
theorem B1404259 : Blo 583288 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B585059 : Blo 583288 585059 := bstep (se 1 (by rfl) ⟨438794, by rfl⟩ : syracuseStep 585059 = 877589) B877589
theorem B1666403 : Blo 583288 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B879971 : Blo 583288 879971 := bstep (se 1 (by rfl) ⟨659978, by rfl⟩ : syracuseStep 879971 = 1319957) B1319957
theorem B585075 : Blo 583288 585075 := bstep (se 1 (by rfl) ⟨438806, by rfl⟩ : syracuseStep 585075 = 877613) B877613
theorem B880001 : Blo 583288 880001 := bstep (se 2 (by rfl) ⟨330000, by rfl⟩ : syracuseStep 880001 = 660001) B660001
theorem B585091 : Blo 583288 585091 := bstep (se 1 (by rfl) ⟨438818, by rfl⟩ : syracuseStep 585091 = 877637) B877637
theorem B585107 : Blo 583288 585107 := bstep (se 1 (by rfl) ⟨438830, by rfl⟩ : syracuseStep 585107 = 877661) B877661
theorem B880019 : Blo 583288 880019 := bstep (se 1 (by rfl) ⟨660014, by rfl⟩ : syracuseStep 880019 = 1320029) B1320029
theorem B585123 : Blo 583288 585123 := bstep (se 1 (by rfl) ⟨438842, by rfl⟩ : syracuseStep 585123 = 877685) B877685
theorem B1404337 : Blo 583288 1404337 := bstep (se 2 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 1404337 = 1053253) B1053253
theorem B880049 : Blo 583288 880049 := bstep (se 2 (by rfl) ⟨330018, by rfl⟩ : syracuseStep 880049 = 660037) B660037
theorem B585139 : Blo 583288 585139 := bstep (se 1 (by rfl) ⟨438854, by rfl⟩ : syracuseStep 585139 = 877709) B877709
theorem B585155 : Blo 583288 585155 := bstep (se 1 (by rfl) ⟨438866, by rfl⟩ : syracuseStep 585155 = 877733) B877733
theorem B880067 : Blo 583288 880067 := bstep (se 1 (by rfl) ⟨660050, by rfl⟩ : syracuseStep 880067 = 1320101) B1320101
theorem B585171 : Blo 583288 585171 := bstep (se 1 (by rfl) ⟨438878, by rfl⟩ : syracuseStep 585171 = 877757) B877757
theorem B880097 : Blo 583288 880097 := bstep (se 2 (by rfl) ⟨330036, by rfl⟩ : syracuseStep 880097 = 660073) B660073
theorem B585187 : Blo 583288 585187 := bstep (se 1 (by rfl) ⟨438890, by rfl⟩ : syracuseStep 585187 = 877781) B877781
theorem B585203 : Blo 583288 585203 := bstep (se 1 (by rfl) ⟨438902, by rfl⟩ : syracuseStep 585203 = 877805) B877805
theorem B880115 : Blo 583288 880115 := bstep (se 1 (by rfl) ⟨660086, by rfl⟩ : syracuseStep 880115 = 1320173) B1320173
theorem B585219 : Blo 583288 585219 := bstep (se 1 (by rfl) ⟨438914, by rfl⟩ : syracuseStep 585219 = 877829) B877829
theorem B880145 : Blo 583288 880145 := bstep (se 2 (by rfl) ⟨330054, by rfl⟩ : syracuseStep 880145 = 660109) B660109
theorem B585235 : Blo 583288 585235 := bstep (se 1 (by rfl) ⟨438926, by rfl⟩ : syracuseStep 585235 = 877853) B877853
theorem B585251 : Blo 583288 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B880163 : Blo 583288 880163 := bstep (se 1 (by rfl) ⟨660122, by rfl⟩ : syracuseStep 880163 = 1320245) B1320245
theorem B749107 : Blo 583288 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B585267 : Blo 583288 585267 := bstep (se 1 (by rfl) ⟨438950, by rfl⟩ : syracuseStep 585267 = 877901) B877901
theorem B880193 : Blo 583288 880193 := bstep (se 2 (by rfl) ⟨330072, by rfl⟩ : syracuseStep 880193 = 660145) B660145
theorem B585283 : Blo 583288 585283 := bstep (se 1 (by rfl) ⟨438962, by rfl⟩ : syracuseStep 585283 = 877925) B877925
theorem B585299 : Blo 583288 585299 := bstep (se 1 (by rfl) ⟨438974, by rfl⟩ : syracuseStep 585299 = 877949) B877949
theorem B880211 : Blo 583288 880211 := bstep (se 1 (by rfl) ⟨660158, by rfl⟩ : syracuseStep 880211 = 1320317) B1320317
theorem B585315 : Blo 583288 585315 := bstep (se 1 (by rfl) ⟨438986, by rfl⟩ : syracuseStep 585315 = 877973) B877973
theorem B3173987 : Blo 583288 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B880241 : Blo 583288 880241 := bstep (se 2 (by rfl) ⟨330090, by rfl⟩ : syracuseStep 880241 = 660181) B660181
theorem B585331 : Blo 583288 585331 := bstep (se 1 (by rfl) ⟨438998, by rfl⟩ : syracuseStep 585331 = 877997) B877997
theorem B585347 : Blo 583288 585347 := bstep (se 1 (by rfl) ⟨439010, by rfl⟩ : syracuseStep 585347 = 878021) B878021
theorem B880259 : Blo 583288 880259 := bstep (se 1 (by rfl) ⟨660194, by rfl⟩ : syracuseStep 880259 = 1320389) B1320389
theorem B585363 : Blo 583288 585363 := bstep (se 1 (by rfl) ⟨439022, by rfl⟩ : syracuseStep 585363 = 878045) B878045
theorem B880289 : Blo 583288 880289 := bstep (se 2 (by rfl) ⟨330108, by rfl⟩ : syracuseStep 880289 = 660217) B660217
theorem B585379 : Blo 583288 585379 := bstep (se 1 (by rfl) ⟨439034, by rfl⟩ : syracuseStep 585379 = 878069) B878069
theorem B585395 : Blo 583288 585395 := bstep (se 1 (by rfl) ⟨439046, by rfl⟩ : syracuseStep 585395 = 878093) B878093
theorem B880307 : Blo 583288 880307 := bstep (se 1 (by rfl) ⟨660230, by rfl⟩ : syracuseStep 880307 = 1320461) B1320461
theorem B585411 : Blo 583288 585411 := bstep (se 1 (by rfl) ⟨439058, by rfl⟩ : syracuseStep 585411 = 878117) B878117
theorem B1109713 : Blo 583288 1109713 := bstep (se 2 (by rfl) ⟨416142, by rfl⟩ : syracuseStep 1109713 = 832285) B832285
theorem B880337 : Blo 583288 880337 := bstep (se 2 (by rfl) ⟨330126, by rfl⟩ : syracuseStep 880337 = 660253) B660253
theorem B585427 : Blo 583288 585427 := bstep (se 1 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 585427 = 878141) B878141
theorem B3337955 : Blo 583288 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B585443 : Blo 583288 585443 := bstep (se 1 (by rfl) ⟨439082, by rfl⟩ : syracuseStep 585443 = 878165) B878165
theorem B880355 : Blo 583288 880355 := bstep (se 1 (by rfl) ⟨660266, by rfl⟩ : syracuseStep 880355 = 1320533) B1320533
theorem B585459 : Blo 583288 585459 := bstep (se 1 (by rfl) ⟨439094, by rfl⟩ : syracuseStep 585459 = 878189) B878189
theorem B880385 : Blo 583288 880385 := bstep (se 2 (by rfl) ⟨330144, by rfl⟩ : syracuseStep 880385 = 660289) B660289
theorem B585475 : Blo 583288 585475 := bstep (se 1 (by rfl) ⟨439106, by rfl⟩ : syracuseStep 585475 = 878213) B878213
theorem B585491 : Blo 583288 585491 := bstep (se 1 (by rfl) ⟨439118, by rfl⟩ : syracuseStep 585491 = 878237) B878237
theorem B880403 : Blo 583288 880403 := bstep (se 1 (by rfl) ⟨660302, by rfl⟩ : syracuseStep 880403 = 1320605) B1320605
theorem B585507 : Blo 583288 585507 := bstep (se 1 (by rfl) ⟨439130, by rfl⟩ : syracuseStep 585507 = 878261) B878261
theorem B880433 : Blo 583288 880433 := bstep (se 2 (by rfl) ⟨330162, by rfl⟩ : syracuseStep 880433 = 660325) B660325
theorem B585523 : Blo 583288 585523 := bstep (se 1 (by rfl) ⟨439142, by rfl⟩ : syracuseStep 585523 = 878285) B878285
theorem B585539 : Blo 583288 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B880451 : Blo 583288 880451 := bstep (se 1 (by rfl) ⟨660338, by rfl⟩ : syracuseStep 880451 = 1320677) B1320677
theorem B585555 : Blo 583288 585555 := bstep (se 1 (by rfl) ⟨439166, by rfl⟩ : syracuseStep 585555 = 878333) B878333
theorem B880481 : Blo 583288 880481 := bstep (se 2 (by rfl) ⟨330180, by rfl⟩ : syracuseStep 880481 = 660361) B660361
theorem B585571 : Blo 583288 585571 := bstep (se 1 (by rfl) ⟨439178, by rfl⟩ : syracuseStep 585571 = 878357) B878357
theorem B585587 : Blo 583288 585587 := bstep (se 1 (by rfl) ⟨439190, by rfl⟩ : syracuseStep 585587 = 878381) B878381
theorem B880499 : Blo 583288 880499 := bstep (se 1 (by rfl) ⟨660374, by rfl⟩ : syracuseStep 880499 = 1320749) B1320749
theorem B585603 : Blo 583288 585603 := bstep (se 1 (by rfl) ⟨439202, by rfl⟩ : syracuseStep 585603 = 878405) B878405
theorem B880529 : Blo 583288 880529 := bstep (se 2 (by rfl) ⟨330198, by rfl⟩ : syracuseStep 880529 = 660397) B660397
theorem B585619 : Blo 583288 585619 := bstep (se 1 (by rfl) ⟨439214, by rfl⟩ : syracuseStep 585619 = 878429) B878429
theorem B585635 : Blo 583288 585635 := bstep (se 1 (by rfl) ⟨439226, by rfl⟩ : syracuseStep 585635 = 878453) B878453
theorem B880547 : Blo 583288 880547 := bstep (se 1 (by rfl) ⟨660410, by rfl⟩ : syracuseStep 880547 = 1320821) B1320821
theorem B585651 : Blo 583288 585651 := bstep (se 1 (by rfl) ⟨439238, by rfl⟩ : syracuseStep 585651 = 878477) B878477
theorem B880577 : Blo 583288 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B585667 : Blo 583288 585667 := bstep (se 1 (by rfl) ⟨439250, by rfl⟩ : syracuseStep 585667 = 878501) B878501
theorem B585683 : Blo 583288 585683 := bstep (se 1 (by rfl) ⟨439262, by rfl⟩ : syracuseStep 585683 = 878525) B878525
theorem B880595 : Blo 583288 880595 := bstep (se 1 (by rfl) ⟨660446, by rfl⟩ : syracuseStep 880595 = 1320893) B1320893
theorem B585699 : Blo 583288 585699 := bstep (se 1 (by rfl) ⟨439274, by rfl⟩ : syracuseStep 585699 = 878549) B878549
theorem B880625 : Blo 583288 880625 := bstep (se 2 (by rfl) ⟨330234, by rfl⟩ : syracuseStep 880625 = 660469) B660469
theorem B585715 : Blo 583288 585715 := bstep (se 1 (by rfl) ⟨439286, by rfl⟩ : syracuseStep 585715 = 878573) B878573
theorem B585731 : Blo 583288 585731 := bstep (se 1 (by rfl) ⟨439298, by rfl⟩ : syracuseStep 585731 = 878597) B878597
theorem B880643 : Blo 583288 880643 := bstep (se 1 (by rfl) ⟨660482, by rfl⟩ : syracuseStep 880643 = 1320965) B1320965
theorem B585747 : Blo 583288 585747 := bstep (se 1 (by rfl) ⟨439310, by rfl⟩ : syracuseStep 585747 = 878621) B878621
theorem B880673 : Blo 583288 880673 := bstep (se 2 (by rfl) ⟨330252, by rfl⟩ : syracuseStep 880673 = 660505) B660505
theorem B585763 : Blo 583288 585763 := bstep (se 1 (by rfl) ⟨439322, by rfl⟩ : syracuseStep 585763 = 878645) B878645
theorem B585779 : Blo 583288 585779 := bstep (se 1 (by rfl) ⟨439334, by rfl⟩ : syracuseStep 585779 = 878669) B878669
theorem B880691 : Blo 583288 880691 := bstep (se 1 (by rfl) ⟨660518, by rfl⟩ : syracuseStep 880691 = 1321037) B1321037
theorem B585795 : Blo 583288 585795 := bstep (se 1 (by rfl) ⟨439346, by rfl⟩ : syracuseStep 585795 = 878693) B878693
theorem B880721 : Blo 583288 880721 := bstep (se 2 (by rfl) ⟨330270, by rfl⟩ : syracuseStep 880721 = 660541) B660541
theorem B585811 : Blo 583288 585811 := bstep (se 1 (by rfl) ⟨439358, by rfl⟩ : syracuseStep 585811 = 878717) B878717
theorem B1110115 : Blo 583288 1110115 := bstep (se 1 (by rfl) ⟨832586, by rfl⟩ : syracuseStep 1110115 = 1665173) B1665173
theorem B585827 : Blo 583288 585827 := bstep (se 1 (by rfl) ⟨439370, by rfl⟩ : syracuseStep 585827 = 878741) B878741
theorem B880739 : Blo 583288 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B585843 : Blo 583288 585843 := bstep (se 1 (by rfl) ⟨439382, by rfl⟩ : syracuseStep 585843 = 878765) B878765
theorem B880769 : Blo 583288 880769 := bstep (se 2 (by rfl) ⟨330288, by rfl⟩ : syracuseStep 880769 = 660577) B660577
theorem B585859 : Blo 583288 585859 := bstep (se 1 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 585859 = 878789) B878789
theorem B1667213 : Blo 583288 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B1110161 : Blo 583288 1110161 := bstep (se 2 (by rfl) ⟨416310, by rfl⟩ : syracuseStep 1110161 = 832621) B832621
theorem B585875 : Blo 583288 585875 := bstep (se 1 (by rfl) ⟨439406, by rfl⟩ : syracuseStep 585875 = 878813) B878813
theorem B880787 : Blo 583288 880787 := bstep (se 1 (by rfl) ⟨660590, by rfl⟩ : syracuseStep 880787 = 1321181) B1321181
theorem B585891 : Blo 583288 585891 := bstep (se 1 (by rfl) ⟨439418, by rfl⟩ : syracuseStep 585891 = 878837) B878837
theorem B880817 : Blo 583288 880817 := bstep (se 2 (by rfl) ⟨330306, by rfl⟩ : syracuseStep 880817 = 660613) B660613
theorem B585907 : Blo 583288 585907 := bstep (se 1 (by rfl) ⟨439430, by rfl⟩ : syracuseStep 585907 = 878861) B878861
theorem B585923 : Blo 583288 585923 := bstep (se 1 (by rfl) ⟨439442, by rfl⟩ : syracuseStep 585923 = 878885) B878885
theorem B880835 : Blo 583288 880835 := bstep (se 1 (by rfl) ⟨660626, by rfl⟩ : syracuseStep 880835 = 1321253) B1321253
theorem B585939 : Blo 583288 585939 := bstep (se 1 (by rfl) ⟨439454, by rfl⟩ : syracuseStep 585939 = 878909) B878909
theorem B880865 : Blo 583288 880865 := bstep (se 2 (by rfl) ⟨330324, by rfl⟩ : syracuseStep 880865 = 660649) B660649
theorem B585955 : Blo 583288 585955 := bstep (se 1 (by rfl) ⟨439466, by rfl⟩ : syracuseStep 585955 = 878933) B878933
theorem B585971 : Blo 583288 585971 := bstep (se 1 (by rfl) ⟨439478, by rfl⟩ : syracuseStep 585971 = 878957) B878957
theorem B880883 : Blo 583288 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B585987 : Blo 583288 585987 := bstep (se 1 (by rfl) ⟨439490, by rfl⟩ : syracuseStep 585987 = 878981) B878981
theorem B880913 : Blo 583288 880913 := bstep (se 2 (by rfl) ⟨330342, by rfl⟩ : syracuseStep 880913 = 660685) B660685
theorem B586003 : Blo 583288 586003 := bstep (se 1 (by rfl) ⟨439502, by rfl⟩ : syracuseStep 586003 = 879005) B879005
theorem B586019 : Blo 583288 586019 := bstep (se 1 (by rfl) ⟨439514, by rfl⟩ : syracuseStep 586019 = 879029) B879029
theorem B880931 : Blo 583288 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B586035 : Blo 583288 586035 := bstep (se 1 (by rfl) ⟨439526, by rfl⟩ : syracuseStep 586035 = 879053) B879053
theorem B586051 : Blo 583288 586051 := bstep (se 1 (by rfl) ⟨439538, by rfl⟩ : syracuseStep 586051 = 879077) B879077
theorem B1667405 : Blo 583288 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B586067 : Blo 583288 586067 := bstep (se 1 (by rfl) ⟨439550, by rfl⟩ : syracuseStep 586067 = 879101) B879101
theorem B586083 : Blo 583288 586083 := bstep (se 1 (by rfl) ⟨439562, by rfl⟩ : syracuseStep 586083 = 879125) B879125
theorem B586099 : Blo 583288 586099 := bstep (se 1 (by rfl) ⟨439574, by rfl⟩ : syracuseStep 586099 = 879149) B879149
theorem B586115 : Blo 583288 586115 := bstep (se 1 (by rfl) ⟨439586, by rfl⟩ : syracuseStep 586115 = 879173) B879173
theorem B586131 : Blo 583288 586131 := bstep (se 1 (by rfl) ⟨439598, by rfl⟩ : syracuseStep 586131 = 879197) B879197
theorem B586147 : Blo 583288 586147 := bstep (se 1 (by rfl) ⟨439610, by rfl⟩ : syracuseStep 586147 = 879221) B879221
theorem B1929635 : Blo 583288 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B1110449 : Blo 583288 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B586163 : Blo 583288 586163 := bstep (se 1 (by rfl) ⟨439622, by rfl⟩ : syracuseStep 586163 = 879245) B879245
theorem B586179 : Blo 583288 586179 := bstep (se 1 (by rfl) ⟨439634, by rfl⟩ : syracuseStep 586179 = 879269) B879269
theorem B586195 : Blo 583288 586195 := bstep (se 1 (by rfl) ⟨439646, by rfl⟩ : syracuseStep 586195 = 879293) B879293
theorem B586211 : Blo 583288 586211 := bstep (se 1 (by rfl) ⟨439658, by rfl⟩ : syracuseStep 586211 = 879317) B879317
theorem B7139825 : Blo 583288 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B586227 : Blo 583288 586227 := bstep (se 1 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 586227 = 879341) B879341
theorem B586243 : Blo 583288 586243 := bstep (se 1 (by rfl) ⟨439682, by rfl⟩ : syracuseStep 586243 = 879365) B879365
theorem B586259 : Blo 583288 586259 := bstep (se 1 (by rfl) ⟨439694, by rfl⟩ : syracuseStep 586259 = 879389) B879389
theorem B586275 : Blo 583288 586275 := bstep (se 1 (by rfl) ⟨439706, by rfl⟩ : syracuseStep 586275 = 879413) B879413
theorem B3011107 : Blo 583288 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B586291 : Blo 583288 586291 := bstep (se 1 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 586291 = 879437) B879437
theorem B586307 : Blo 583288 586307 := bstep (se 1 (by rfl) ⟨439730, by rfl⟩ : syracuseStep 586307 = 879461) B879461
theorem B586323 : Blo 583288 586323 := bstep (se 1 (by rfl) ⟨439742, by rfl⟩ : syracuseStep 586323 = 879485) B879485
theorem B586339 : Blo 583288 586339 := bstep (se 1 (by rfl) ⟨439754, by rfl⟩ : syracuseStep 586339 = 879509) B879509
theorem B586355 : Blo 583288 586355 := bstep (se 1 (by rfl) ⟨439766, by rfl⟩ : syracuseStep 586355 = 879533) B879533
theorem B586371 : Blo 583288 586371 := bstep (se 1 (by rfl) ⟨439778, by rfl⟩ : syracuseStep 586371 = 879557) B879557
theorem B586387 : Blo 583288 586387 := bstep (se 1 (by rfl) ⟨439790, by rfl⟩ : syracuseStep 586387 = 879581) B879581
theorem B586403 : Blo 583288 586403 := bstep (se 1 (by rfl) ⟨439802, by rfl⟩ : syracuseStep 586403 = 879605) B879605
theorem B2224817 : Blo 583288 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B586419 : Blo 583288 586419 := bstep (se 1 (by rfl) ⟨439814, by rfl⟩ : syracuseStep 586419 = 879629) B879629
theorem B586435 : Blo 583288 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B586451 : Blo 583288 586451 := bstep (se 1 (by rfl) ⟨439838, by rfl⟩ : syracuseStep 586451 = 879677) B879677
theorem B586467 : Blo 583288 586467 := bstep (se 1 (by rfl) ⟨439850, by rfl⟩ : syracuseStep 586467 = 879701) B879701
theorem B586483 : Blo 583288 586483 := bstep (se 1 (by rfl) ⟨439862, by rfl⟩ : syracuseStep 586483 = 879725) B879725
theorem B1504003 : Blo 583288 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B586499 : Blo 583288 586499 := bstep (se 1 (by rfl) ⟨439874, by rfl⟩ : syracuseStep 586499 = 879749) B879749
theorem B586515 : Blo 583288 586515 := bstep (se 1 (by rfl) ⟨439886, by rfl⟩ : syracuseStep 586515 = 879773) B879773
theorem B586531 : Blo 583288 586531 := bstep (se 1 (by rfl) ⟨439898, by rfl⟩ : syracuseStep 586531 = 879797) B879797
theorem B586547 : Blo 583288 586547 := bstep (se 1 (by rfl) ⟨439910, by rfl⟩ : syracuseStep 586547 = 879821) B879821
theorem B586563 : Blo 583288 586563 := bstep (se 1 (by rfl) ⟨439922, by rfl⟩ : syracuseStep 586563 = 879845) B879845
theorem B586579 : Blo 583288 586579 := bstep (se 1 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 586579 = 879869) B879869
theorem B586595 : Blo 583288 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B586611 : Blo 583288 586611 := bstep (se 1 (by rfl) ⟨439958, by rfl⟩ : syracuseStep 586611 = 879917) B879917
theorem B586627 : Blo 583288 586627 := bstep (se 1 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 586627 = 879941) B879941
theorem B586643 : Blo 583288 586643 := bstep (se 1 (by rfl) ⟨439982, by rfl⟩ : syracuseStep 586643 = 879965) B879965
theorem B586659 : Blo 583288 586659 := bstep (se 1 (by rfl) ⟨439994, by rfl⟩ : syracuseStep 586659 = 879989) B879989
theorem B586675 : Blo 583288 586675 := bstep (se 1 (by rfl) ⟨440006, by rfl⟩ : syracuseStep 586675 = 880013) B880013
theorem B586691 : Blo 583288 586691 := bstep (se 1 (by rfl) ⟨440018, by rfl⟩ : syracuseStep 586691 = 880037) B880037
theorem B586707 : Blo 583288 586707 := bstep (se 1 (by rfl) ⟨440030, by rfl⟩ : syracuseStep 586707 = 880061) B880061
theorem B586723 : Blo 583288 586723 := bstep (se 1 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 586723 = 880085) B880085
theorem B586739 : Blo 583288 586739 := bstep (se 1 (by rfl) ⟨440054, by rfl⟩ : syracuseStep 586739 = 880109) B880109
theorem B586755 : Blo 583288 586755 := bstep (se 1 (by rfl) ⟨440066, by rfl⟩ : syracuseStep 586755 = 880133) B880133
theorem B586771 : Blo 583288 586771 := bstep (se 1 (by rfl) ⟨440078, by rfl⟩ : syracuseStep 586771 = 880157) B880157
theorem B586787 : Blo 583288 586787 := bstep (se 1 (by rfl) ⟨440090, by rfl⟩ : syracuseStep 586787 = 880181) B880181
theorem B586803 : Blo 583288 586803 := bstep (se 1 (by rfl) ⟨440102, by rfl⟩ : syracuseStep 586803 = 880205) B880205
theorem B586819 : Blo 583288 586819 := bstep (se 1 (by rfl) ⟨440114, by rfl⟩ : syracuseStep 586819 = 880229) B880229
theorem B586835 : Blo 583288 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B586851 : Blo 583288 586851 := bstep (se 1 (by rfl) ⟨440138, by rfl⟩ : syracuseStep 586851 = 880277) B880277
theorem B586867 : Blo 583288 586867 := bstep (se 1 (by rfl) ⟨440150, by rfl⟩ : syracuseStep 586867 = 880301) B880301
theorem B1111171 : Blo 583288 1111171 := bstep (se 1 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 1111171 = 1666757) B1666757
theorem B586883 : Blo 583288 586883 := bstep (se 1 (by rfl) ⟨440162, by rfl⟩ : syracuseStep 586883 = 880325) B880325
theorem B7206029 : Blo 583288 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B586899 : Blo 583288 586899 := bstep (se 1 (by rfl) ⟨440174, by rfl⟩ : syracuseStep 586899 = 880349) B880349
theorem B586915 : Blo 583288 586915 := bstep (se 1 (by rfl) ⟨440186, by rfl⟩ : syracuseStep 586915 = 880373) B880373
theorem B586931 : Blo 583288 586931 := bstep (se 1 (by rfl) ⟨440198, by rfl⟩ : syracuseStep 586931 = 880397) B880397
theorem B586947 : Blo 583288 586947 := bstep (se 1 (by rfl) ⟨440210, by rfl⟩ : syracuseStep 586947 = 880421) B880421
theorem B586963 : Blo 583288 586963 := bstep (se 1 (by rfl) ⟨440222, by rfl⟩ : syracuseStep 586963 = 880445) B880445
theorem B5010659 : Blo 583288 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B586979 : Blo 583288 586979 := bstep (se 1 (by rfl) ⟨440234, by rfl⟩ : syracuseStep 586979 = 880469) B880469
theorem B586995 : Blo 583288 586995 := bstep (se 1 (by rfl) ⟨440246, by rfl⟩ : syracuseStep 586995 = 880493) B880493
theorem B587011 : Blo 583288 587011 := bstep (se 1 (by rfl) ⟨440258, by rfl⟩ : syracuseStep 587011 = 880517) B880517
theorem B587027 : Blo 583288 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B587043 : Blo 583288 587043 := bstep (se 1 (by rfl) ⟨440282, by rfl⟩ : syracuseStep 587043 = 880565) B880565
theorem B1668397 : Blo 583288 1668397 := bstep (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) B625649
theorem B587059 : Blo 583288 587059 := bstep (se 1 (by rfl) ⟨440294, by rfl⟩ : syracuseStep 587059 = 880589) B880589
theorem B587075 : Blo 583288 587075 := bstep (se 1 (by rfl) ⟨440306, by rfl⟩ : syracuseStep 587075 = 880613) B880613
theorem B587091 : Blo 583288 587091 := bstep (se 1 (by rfl) ⟨440318, by rfl⟩ : syracuseStep 587091 = 880637) B880637
theorem B587107 : Blo 583288 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B587123 : Blo 583288 587123 := bstep (se 1 (by rfl) ⟨440342, by rfl⟩ : syracuseStep 587123 = 880685) B880685
theorem B587139 : Blo 583288 587139 := bstep (se 1 (by rfl) ⟨440354, by rfl⟩ : syracuseStep 587139 = 880709) B880709
theorem B587155 : Blo 583288 587155 := bstep (se 1 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 587155 = 880733) B880733
theorem B587171 : Blo 583288 587171 := bstep (se 1 (by rfl) ⟨440378, by rfl⟩ : syracuseStep 587171 = 880757) B880757
theorem B587187 : Blo 583288 587187 := bstep (se 1 (by rfl) ⟨440390, by rfl⟩ : syracuseStep 587187 = 880781) B880781
theorem B587203 : Blo 583288 587203 := bstep (se 1 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 587203 = 880805) B880805
theorem B587219 : Blo 583288 587219 := bstep (se 1 (by rfl) ⟨440414, by rfl⟩ : syracuseStep 587219 = 880829) B880829
theorem B587235 : Blo 583288 587235 := bstep (se 1 (by rfl) ⟨440426, by rfl⟩ : syracuseStep 587235 = 880853) B880853
theorem B2848241 : Blo 583288 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B587251 : Blo 583288 587251 := bstep (se 1 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 587251 = 880877) B880877
theorem B587267 : Blo 583288 587267 := bstep (se 1 (by rfl) ⟨440450, by rfl⟩ : syracuseStep 587267 = 880901) B880901
theorem B587283 : Blo 583288 587283 := bstep (se 1 (by rfl) ⟨440462, by rfl⟩ : syracuseStep 587283 = 880925) B880925
theorem B1111619 : Blo 583288 1111619 := bstep (se 1 (by rfl) ⟨833714, by rfl⟩ : syracuseStep 1111619 = 1667429) B1667429
theorem B1111907 : Blo 583288 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B2226275 : Blo 583288 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B3045539 : Blo 583288 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B915923 : Blo 583288 915923 := bstep (se 1 (by rfl) ⟨686942, by rfl⟩ : syracuseStep 915923 = 1373885) B1373885
theorem B1505891 : Blo 583288 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1112849 : Blo 583288 1112849 := bstep (se 2 (by rfl) ⟨417318, by rfl⟩ : syracuseStep 1112849 = 834637) B834637
theorem B3341189 : Blo 583288 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B1670129 : Blo 583288 1670129 := bstep (se 2 (by rfl) ⟨626298, by rfl⟩ : syracuseStep 1670129 = 1252597) B1252597
theorem B1408067 : Blo 583288 1408067 := bstep (se 1 (by rfl) ⟨1056050, by rfl⟩ : syracuseStep 1408067 = 2112101) B2112101
theorem B2227277 : Blo 583288 2227277 := bstep (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) B835229
theorem B1670321 : Blo 583288 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B3341645 : Blo 583288 3341645 := bstep (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) B1253117
theorem B1080707 : Blo 583288 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B1408643 : Blo 583288 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B1113745 : Blo 583288 1113745 := bstep (se 2 (by rfl) ⟨417654, by rfl⟩ : syracuseStep 1113745 = 835309) B835309
theorem B4456133 : Blo 583288 4456133 := bstep (se 4 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 4456133 = 835525) B835525
theorem B1113905 : Blo 583288 1113905 := bstep (se 2 (by rfl) ⟨417714, by rfl⟩ : syracuseStep 1113905 = 835429) B835429
theorem B1408835 : Blo 583288 1408835 := bstep (se 1 (by rfl) ⟨1056626, by rfl⟩ : syracuseStep 1408835 = 2113253) B2113253
theorem B1671347 : Blo 583288 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B2228417 : Blo 583288 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B1114391 : Blo 583288 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B656203 : Blo 583288 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B656311 : Blo 583288 656311 := bstep (se 1 (by rfl) ⟨492233, by rfl⟩ : syracuseStep 656311 = 984467) B984467
theorem B623543 : Blo 583288 623543 := bstep (se 1 (by rfl) ⟨467657, by rfl⟩ : syracuseStep 623543 = 935315) B935315
theorem B1246283 : Blo 583288 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B656491 : Blo 583288 656491 := bstep (se 1 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 656491 = 984737) B984737
theorem B656599 : Blo 583288 656599 := bstep (se 1 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 656599 = 984899) B984899
theorem B656779 : Blo 583288 656779 := bstep (se 1 (by rfl) ⟨492584, by rfl⟩ : syracuseStep 656779 = 985169) B985169
theorem B2229677 : Blo 583288 2229677 := bstep (se 3 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 2229677 = 836129) B836129
theorem B2229707 : Blo 583288 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B656887 : Blo 583288 656887 := bstep (se 1 (by rfl) ⟨492665, by rfl⟩ : syracuseStep 656887 = 985331) B985331
theorem B1246745 : Blo 583288 1246745 := bstep (se 2 (by rfl) ⟨467529, by rfl⟩ : syracuseStep 1246745 = 935059) B935059
theorem B4458077 : Blo 583288 4458077 := bstep (se 3 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 4458077 = 1671779) B1671779
theorem B624235 : Blo 583288 624235 := bstep (se 1 (by rfl) ⟨468176, by rfl⟩ : syracuseStep 624235 = 936353) B936353
theorem B3606167 : Blo 583288 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B657067 : Blo 583288 657067 := bstep (se 1 (by rfl) ⟨492800, by rfl⟩ : syracuseStep 657067 = 985601) B985601
theorem B984791 : Blo 583288 984791 := bstep (se 1 (by rfl) ⟨738593, by rfl⟩ : syracuseStep 984791 = 1477187) B1477187
theorem B1312523 : Blo 583288 1312523 := bstep (se 1 (by rfl) ⟨984392, by rfl⟩ : syracuseStep 1312523 = 1968785) B1968785
theorem B657175 : Blo 583288 657175 := bstep (se 1 (by rfl) ⟨492881, by rfl⟩ : syracuseStep 657175 = 985763) B985763
theorem B1312577 : Blo 583288 1312577 := bstep (se 2 (by rfl) ⟨492216, by rfl⟩ : syracuseStep 1312577 = 984433) B984433
theorem B3999563 : Blo 583288 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B984919 : Blo 583288 984919 := bstep (se 1 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 984919 = 1477379) B1477379
theorem B657355 : Blo 583288 657355 := bstep (se 1 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 657355 = 986033) B986033
theorem B1476569 : Blo 583288 1476569 := bstep (se 2 (by rfl) ⟨553713, by rfl⟩ : syracuseStep 1476569 = 1107427) B1107427
theorem B788491 : Blo 583288 788491 := bstep (se 1 (by rfl) ⟨591368, by rfl⟩ : syracuseStep 788491 = 1182737) B1182737
theorem B1312793 : Blo 583288 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B1869875 : Blo 583288 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B657463 : Blo 583288 657463 := bstep (se 1 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 657463 = 986195) B986195
theorem B1312883 : Blo 583288 1312883 := bstep (se 1 (by rfl) ⟨984662, by rfl⟩ : syracuseStep 1312883 = 1969325) B1969325
theorem B1312919 : Blo 583288 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B2492633 : Blo 583288 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B657643 : Blo 583288 657643 := bstep (se 1 (by rfl) ⟨493232, by rfl⟩ : syracuseStep 657643 = 986465) B986465
theorem B1313099 : Blo 583288 1313099 := bstep (se 1 (by rfl) ⟨984824, by rfl⟩ : syracuseStep 1313099 = 1969649) B1969649
theorem B657751 : Blo 583288 657751 := bstep (se 1 (by rfl) ⟨493313, by rfl⟩ : syracuseStep 657751 = 986627) B986627
theorem B1313153 : Blo 583288 1313153 := bstep (se 2 (by rfl) ⟨492432, by rfl⟩ : syracuseStep 1313153 = 984865) B984865
theorem B985547 : Blo 583288 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B657931 : Blo 583288 657931 := bstep (se 1 (by rfl) ⟨493448, by rfl⟩ : syracuseStep 657931 = 986897) B986897
theorem B10029581 : Blo 583288 10029581 := bstep (se 3 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 10029581 = 3761093) B3761093
theorem B985675 : Blo 583288 985675 := bstep (se 1 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 985675 = 1478513) B1478513
theorem B1313369 : Blo 583288 1313369 := bstep (se 2 (by rfl) ⟨492513, by rfl⟩ : syracuseStep 1313369 = 985027) B985027
theorem B658039 : Blo 583288 658039 := bstep (se 1 (by rfl) ⟨493529, by rfl⟩ : syracuseStep 658039 = 987059) B987059
theorem B1313459 : Blo 583288 1313459 := bstep (se 1 (by rfl) ⟨985094, by rfl⟩ : syracuseStep 1313459 = 1970189) B1970189
theorem B1247923 : Blo 583288 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1313495 : Blo 583288 1313495 := bstep (se 1 (by rfl) ⟨985121, by rfl⟩ : syracuseStep 1313495 = 1970243) B1970243
theorem B1870553 : Blo 583288 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B985817 : Blo 583288 985817 := bstep (se 2 (by rfl) ⟨369681, by rfl⟩ : syracuseStep 985817 = 739363) B739363
theorem B1477399 : Blo 583288 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B658219 : Blo 583288 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B1968947 : Blo 583288 1968947 := bstep (se 1 (by rfl) ⟨1476710, by rfl⟩ : syracuseStep 1968947 = 2953421) B2953421
theorem B1051481 : Blo 583288 1051481 := bstep (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) B788611
theorem B985945 : Blo 583288 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B1313675 : Blo 583288 1313675 := bstep (se 1 (by rfl) ⟨985256, by rfl⟩ : syracuseStep 1313675 = 1970513) B1970513
theorem B658327 : Blo 583288 658327 := bstep (se 1 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 658327 = 987491) B987491
theorem B1313729 : Blo 583288 1313729 := bstep (se 2 (by rfl) ⟨492648, by rfl⟩ : syracuseStep 1313729 = 985297) B985297
theorem B1182721 : Blo 583288 1182721 := bstep (se 2 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 1182721 = 887041) B887041
theorem B625687 : Blo 583288 625687 := bstep (se 1 (by rfl) ⟨469265, by rfl⟩ : syracuseStep 625687 = 938531) B938531
theorem B789529 : Blo 583288 789529 := bstep (se 2 (by rfl) ⟨296073, by rfl⟩ : syracuseStep 789529 = 592147) B592147
theorem B1969217 : Blo 583288 1969217 := bstep (se 2 (by rfl) ⟨738456, by rfl⟩ : syracuseStep 1969217 = 1476913) B1476913
theorem B658507 : Blo 583288 658507 := bstep (se 1 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 658507 = 987761) B987761
theorem B1248385 : Blo 583288 1248385 := bstep (se 2 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 1248385 = 936289) B936289
theorem B1313945 : Blo 583288 1313945 := bstep (se 2 (by rfl) ⟨492729, by rfl⟩ : syracuseStep 1313945 = 985459) B985459
theorem B658615 : Blo 583288 658615 := bstep (se 1 (by rfl) ⟨493961, by rfl⟩ : syracuseStep 658615 = 987923) B987923
theorem B1477835 : Blo 583288 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B1314035 : Blo 583288 1314035 := bstep (se 1 (by rfl) ⟨985526, by rfl⟩ : syracuseStep 1314035 = 1971053) B1971053
theorem B1314071 : Blo 583288 1314071 := bstep (se 1 (by rfl) ⟨985553, by rfl⟩ : syracuseStep 1314071 = 1971107) B1971107
theorem B5639489 : Blo 583288 5639489 := bstep (se 2 (by rfl) ⟨2114808, by rfl⟩ : syracuseStep 5639489 = 4229617) B4229617
theorem B658795 : Blo 583288 658795 := bstep (se 1 (by rfl) ⟨494096, by rfl⟩ : syracuseStep 658795 = 988193) B988193
theorem B626059 : Blo 583288 626059 := bstep (se 1 (by rfl) ⟨469544, by rfl⟩ : syracuseStep 626059 = 939089) B939089
theorem B986519 : Blo 583288 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B2493899 : Blo 583288 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B1314251 : Blo 583288 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B658903 : Blo 583288 658903 := bstep (se 1 (by rfl) ⟨494177, by rfl⟩ : syracuseStep 658903 = 988355) B988355
theorem B1314305 : Blo 583288 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B986647 : Blo 583288 986647 := bstep (se 1 (by rfl) ⟨739985, by rfl⟩ : syracuseStep 986647 = 1479971) B1479971
theorem B1478209 : Blo 583288 1478209 := bstep (se 2 (by rfl) ⟨554328, by rfl⟩ : syracuseStep 1478209 = 1108657) B1108657
theorem B1969757 : Blo 583288 1969757 := bstep (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) B738659
theorem B659083 : Blo 583288 659083 := bstep (se 1 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 659083 = 988625) B988625
theorem B1314521 : Blo 583288 1314521 := bstep (se 2 (by rfl) ⟨492945, by rfl⟩ : syracuseStep 1314521 = 985891) B985891
theorem B1183475 : Blo 583288 1183475 := bstep (se 1 (by rfl) ⟨887606, by rfl⟩ : syracuseStep 1183475 = 1775213) B1775213
theorem B659191 : Blo 583288 659191 := bstep (se 1 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 659191 = 988787) B988787
theorem B1183499 : Blo 583288 1183499 := bstep (se 1 (by rfl) ⟨887624, by rfl⟩ : syracuseStep 1183499 = 1775249) B1775249
theorem B2494259 : Blo 583288 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B1314611 : Blo 583288 1314611 := bstep (se 1 (by rfl) ⟨985958, by rfl⟩ : syracuseStep 1314611 = 1971917) B1971917
theorem B1314647 : Blo 583288 1314647 := bstep (se 1 (by rfl) ⟨985985, by rfl⟩ : syracuseStep 1314647 = 1971971) B1971971
theorem B1249111 : Blo 583288 1249111 := bstep (se 1 (by rfl) ⟨936833, by rfl⟩ : syracuseStep 1249111 = 1873667) B1873667
theorem B659371 : Blo 583288 659371 := bstep (se 1 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 659371 = 989057) B989057
theorem B1314827 : Blo 583288 1314827 := bstep (se 1 (by rfl) ⟨986120, by rfl⟩ : syracuseStep 1314827 = 1972241) B1972241
theorem B659479 : Blo 583288 659479 := bstep (se 1 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 659479 = 989219) B989219
theorem B1314881 : Blo 583288 1314881 := bstep (se 2 (by rfl) ⟨493080, by rfl⟩ : syracuseStep 1314881 = 986161) B986161
theorem B987275 : Blo 583288 987275 := bstep (se 1 (by rfl) ⟨740456, by rfl⟩ : syracuseStep 987275 = 1480913) B1480913
theorem B1478807 : Blo 583288 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B1872065 : Blo 583288 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B659659 : Blo 583288 659659 := bstep (se 1 (by rfl) ⟨494744, by rfl⟩ : syracuseStep 659659 = 989489) B989489
theorem B987403 : Blo 583288 987403 := bstep (se 1 (by rfl) ⟨740552, by rfl⟩ : syracuseStep 987403 = 1481105) B1481105
theorem B1315097 : Blo 583288 1315097 := bstep (se 2 (by rfl) ⟨493161, by rfl⟩ : syracuseStep 1315097 = 986323) B986323
theorem B659767 : Blo 583288 659767 := bstep (se 1 (by rfl) ⟨494825, by rfl⟩ : syracuseStep 659767 = 989651) B989651
theorem B1872193 : Blo 583288 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B1315187 : Blo 583288 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B1315223 : Blo 583288 1315223 := bstep (se 1 (by rfl) ⟨986417, by rfl⟩ : syracuseStep 1315223 = 1972835) B1972835
theorem B987545 : Blo 583288 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B659947 : Blo 583288 659947 := bstep (se 1 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 659947 = 989921) B989921
theorem B2953745 : Blo 583288 2953745 := bstep (se 2 (by rfl) ⟨1107654, by rfl⟩ : syracuseStep 2953745 = 2215309) B2215309
theorem B8458769 : Blo 583288 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B987673 : Blo 583288 987673 := bstep (se 2 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 987673 = 740755) B740755
theorem B1872449 : Blo 583288 1872449 := bstep (se 2 (by rfl) ⟨702168, by rfl⟩ : syracuseStep 1872449 = 1404337) B1404337
theorem B1315403 : Blo 583288 1315403 := bstep (se 1 (by rfl) ⟨986552, by rfl⟩ : syracuseStep 1315403 = 1973105) B1973105
theorem B660055 : Blo 583288 660055 := bstep (se 1 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 660055 = 990083) B990083
theorem B1315457 : Blo 583288 1315457 := bstep (se 2 (by rfl) ⟨493296, by rfl⟩ : syracuseStep 1315457 = 986593) B986593
theorem B1249931 : Blo 583288 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B2953907 : Blo 583288 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B1970891 : Blo 583288 1970891 := bstep (se 1 (by rfl) ⟨1478168, by rfl⟩ : syracuseStep 1970891 = 2956337) B2956337
theorem B660235 : Blo 583288 660235 := bstep (se 1 (by rfl) ⟨495176, by rfl⟩ : syracuseStep 660235 = 990353) B990353
theorem B1315673 : Blo 583288 1315673 := bstep (se 2 (by rfl) ⟨493377, by rfl⟩ : syracuseStep 1315673 = 986755) B986755
theorem B660343 : Blo 583288 660343 := bstep (se 1 (by rfl) ⟨495257, by rfl⟩ : syracuseStep 660343 = 990515) B990515
theorem B1315763 : Blo 583288 1315763 := bstep (se 1 (by rfl) ⟨986822, by rfl⟩ : syracuseStep 1315763 = 1973645) B1973645
theorem B1479617 : Blo 583288 1479617 := bstep (se 2 (by rfl) ⟨554856, by rfl⟩ : syracuseStep 1479617 = 1109713) B1109713
theorem B1315799 : Blo 583288 1315799 := bstep (se 1 (by rfl) ⟨986849, by rfl⟩ : syracuseStep 1315799 = 1973699) B1973699
theorem B1971161 : Blo 583288 1971161 := bstep (se 2 (by rfl) ⟨739185, by rfl⟩ : syracuseStep 1971161 = 1478371) B1478371
theorem B1053707 : Blo 583288 1053707 := bstep (se 1 (by rfl) ⟨790280, by rfl⟩ : syracuseStep 1053707 = 1580561) B1580561
theorem B7476259 : Blo 583288 7476259 := bstep (se 1 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 7476259 = 11214389) B11214389
theorem B660523 : Blo 583288 660523 := bstep (se 1 (by rfl) ⟨495392, by rfl⟩ : syracuseStep 660523 = 990785) B990785
theorem B988247 : Blo 583288 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B1315979 : Blo 583288 1315979 := bstep (se 1 (by rfl) ⟨986984, by rfl⟩ : syracuseStep 1315979 = 1973969) B1973969
theorem B660631 : Blo 583288 660631 := bstep (se 1 (by rfl) ⟨495473, by rfl⟩ : syracuseStep 660631 = 990947) B990947
theorem B1316033 : Blo 583288 1316033 := bstep (se 2 (by rfl) ⟨493512, by rfl⟩ : syracuseStep 1316033 = 987025) B987025
theorem B988375 : Blo 583288 988375 := bstep (se 1 (by rfl) ⟨741281, by rfl⟩ : syracuseStep 988375 = 1482563) B1482563
theorem B1316249 : Blo 583288 1316249 := bstep (se 2 (by rfl) ⟨493593, by rfl⟩ : syracuseStep 1316249 = 987187) B987187
theorem B1480153 : Blo 583288 1480153 := bstep (se 2 (by rfl) ⟨555057, by rfl⟩ : syracuseStep 1480153 = 1110115) B1110115
theorem B1250777 : Blo 583288 1250777 := bstep (se 2 (by rfl) ⟨469041, by rfl⟩ : syracuseStep 1250777 = 938083) B938083
theorem B1316339 : Blo 583288 1316339 := bstep (se 1 (by rfl) ⟨987254, by rfl⟩ : syracuseStep 1316339 = 1974509) B1974509
theorem B1316375 : Blo 583288 1316375 := bstep (se 1 (by rfl) ⟨987281, by rfl⟩ : syracuseStep 1316375 = 1974563) B1974563
theorem B1971863 : Blo 583288 1971863 := bstep (se 1 (by rfl) ⟨1478897, by rfl⟩ : syracuseStep 1971863 = 2957795) B2957795
theorem B1316555 : Blo 583288 1316555 := bstep (se 1 (by rfl) ⟨987416, by rfl⟩ : syracuseStep 1316555 = 1974833) B1974833
theorem B1775321 : Blo 583288 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B1316609 : Blo 583288 1316609 := bstep (se 2 (by rfl) ⟨493728, by rfl⟩ : syracuseStep 1316609 = 987457) B987457
theorem B989003 : Blo 583288 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B11409329 : Blo 583288 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B989131 : Blo 583288 989131 := bstep (se 1 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 989131 = 1483697) B1483697
theorem B1316825 : Blo 583288 1316825 := bstep (se 2 (by rfl) ⟨493809, by rfl⟩ : syracuseStep 1316825 = 987619) B987619
theorem B1578973 : Blo 583288 1578973 := bstep (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) B592115
theorem B1316915 : Blo 583288 1316915 := bstep (se 1 (by rfl) ⟨987686, by rfl⟩ : syracuseStep 1316915 = 1975373) B1975373
theorem B4429889 : Blo 583288 4429889 := bstep (se 2 (by rfl) ⟨1661208, by rfl⟩ : syracuseStep 4429889 = 3322417) B3322417
theorem B1316951 : Blo 583288 1316951 := bstep (se 1 (by rfl) ⟨987713, by rfl⟩ : syracuseStep 1316951 = 1975427) B1975427
theorem B989273 : Blo 583288 989273 := bstep (se 2 (by rfl) ⟨370977, by rfl⟩ : syracuseStep 989273 = 741955) B741955
theorem B1251443 : Blo 583288 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B3741875 : Blo 583288 3741875 := bstep (se 1 (by rfl) ⟨2806406, by rfl⟩ : syracuseStep 3741875 = 5612813) B5612813
theorem B1972403 : Blo 583288 1972403 := bstep (se 1 (by rfl) ⟨1479302, by rfl⟩ : syracuseStep 1972403 = 2958605) B2958605
theorem B989401 : Blo 583288 989401 := bstep (se 2 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 989401 = 742051) B742051
theorem B1874141 : Blo 583288 1874141 := bstep (se 3 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 1874141 = 702803) B702803
theorem B1317131 : Blo 583288 1317131 := bstep (se 1 (by rfl) ⟨987848, by rfl⟩ : syracuseStep 1317131 = 1975697) B1975697
theorem B1317185 : Blo 583288 1317185 := bstep (se 2 (by rfl) ⟨493944, by rfl⟩ : syracuseStep 1317185 = 987889) B987889
theorem B2005337 : Blo 583288 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B1972673 : Blo 583288 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B1055243 : Blo 583288 1055243 := bstep (se 1 (by rfl) ⟨791432, by rfl⟩ : syracuseStep 1055243 = 1582865) B1582865
theorem B1317401 : Blo 583288 1317401 := bstep (se 2 (by rfl) ⟨494025, by rfl⟩ : syracuseStep 1317401 = 988051) B988051
theorem B2103853 : Blo 583288 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B1481267 : Blo 583288 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B2005555 : Blo 583288 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B2955851 : Blo 583288 2955851 := bstep (se 1 (by rfl) ⟨2216888, by rfl⟩ : syracuseStep 2955851 = 4433777) B4433777
theorem B1317491 : Blo 583288 1317491 := bstep (se 1 (by rfl) ⟨988118, by rfl⟩ : syracuseStep 1317491 = 1976237) B1976237
theorem B5053079 : Blo 583288 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B1317527 : Blo 583288 1317527 := bstep (se 1 (by rfl) ⟨988145, by rfl⟩ : syracuseStep 1317527 = 1976291) B1976291
theorem B989975 : Blo 583288 989975 := bstep (se 1 (by rfl) ⟨742481, by rfl⟩ : syracuseStep 989975 = 1484963) B1484963
theorem B1317707 : Blo 583288 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B1481561 : Blo 583288 1481561 := bstep (se 2 (by rfl) ⟨555585, by rfl⟩ : syracuseStep 1481561 = 1111171) B1111171
theorem B1317761 : Blo 583288 1317761 := bstep (se 2 (by rfl) ⟨494160, by rfl⟩ : syracuseStep 1317761 = 988321) B988321
theorem B990103 : Blo 583288 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B1973213 : Blo 583288 1973213 := bstep (se 3 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 1973213 = 739955) B739955
theorem B1874909 : Blo 583288 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B1252417 : Blo 583288 1252417 := bstep (se 2 (by rfl) ⟨469656, by rfl⟩ : syracuseStep 1252417 = 939313) B939313
theorem B1317977 : Blo 583288 1317977 := bstep (se 2 (by rfl) ⟨494241, by rfl⟩ : syracuseStep 1317977 = 988483) B988483
theorem B1318067 : Blo 583288 1318067 := bstep (se 1 (by rfl) ⟨988550, by rfl⟩ : syracuseStep 1318067 = 1977101) B1977101
theorem B1318103 : Blo 583288 1318103 := bstep (se 1 (by rfl) ⟨988577, by rfl⟩ : syracuseStep 1318103 = 1977155) B1977155
theorem B1580249 : Blo 583288 1580249 := bstep (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) B1185187
theorem B1580311 : Blo 583288 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B1252673 : Blo 583288 1252673 := bstep (se 2 (by rfl) ⟨469752, by rfl⟩ : syracuseStep 1252673 = 939505) B939505
theorem B1318283 : Blo 583288 1318283 := bstep (se 1 (by rfl) ⟨988712, by rfl⟩ : syracuseStep 1318283 = 1977425) B1977425
theorem B1252759 : Blo 583288 1252759 := bstep (se 1 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 1252759 = 1879139) B1879139
theorem B1318337 : Blo 583288 1318337 := bstep (se 2 (by rfl) ⟨494376, by rfl⟩ : syracuseStep 1318337 = 988753) B988753
theorem B1875421 : Blo 583288 1875421 := bstep (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) B703283
theorem B990731 : Blo 583288 990731 := bstep (se 1 (by rfl) ⟨743048, by rfl⟩ : syracuseStep 990731 = 1486097) B1486097
theorem B990859 : Blo 583288 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B1318553 : Blo 583288 1318553 := bstep (se 2 (by rfl) ⟨494457, by rfl⟩ : syracuseStep 1318553 = 988915) B988915
theorem B36052685 : Blo 583288 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B1318643 : Blo 583288 1318643 := bstep (se 1 (by rfl) ⟨988982, by rfl⟩ : syracuseStep 1318643 = 1977965) B1977965
theorem B1318679 : Blo 583288 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B991001 : Blo 583288 991001 := bstep (se 2 (by rfl) ⟨371625, by rfl⟩ : syracuseStep 991001 = 743251) B743251
theorem B15998897 : Blo 583288 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B1318859 : Blo 583288 1318859 := bstep (se 1 (by rfl) ⟨989144, by rfl⟩ : syracuseStep 1318859 = 1978289) B1978289
theorem B4431833 : Blo 583288 4431833 := bstep (se 2 (by rfl) ⟨1661937, by rfl⟩ : syracuseStep 4431833 = 3323875) B3323875
theorem B1318913 : Blo 583288 1318913 := bstep (se 2 (by rfl) ⟨494592, by rfl⟩ : syracuseStep 1318913 = 989185) B989185
theorem B9510929 : Blo 583288 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B1974347 : Blo 583288 1974347 := bstep (se 1 (by rfl) ⟨1480760, by rfl⟩ : syracuseStep 1974347 = 2961521) B2961521
theorem B1319129 : Blo 583288 1319129 := bstep (se 2 (by rfl) ⟨494673, by rfl⟩ : syracuseStep 1319129 = 989347) B989347
theorem B1286423 : Blo 583288 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B1319219 : Blo 583288 1319219 := bstep (se 1 (by rfl) ⟨989414, by rfl⟩ : syracuseStep 1319219 = 1978829) B1978829
theorem B2957633 : Blo 583288 2957633 := bstep (se 2 (by rfl) ⟨1109112, by rfl⟩ : syracuseStep 2957633 = 2218225) B2218225
theorem B4759883 : Blo 583288 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B1319255 : Blo 583288 1319255 := bstep (se 1 (by rfl) ⟨989441, by rfl⟩ : syracuseStep 1319255 = 1978883) B1978883
theorem B1974617 : Blo 583288 1974617 := bstep (se 2 (by rfl) ⟨740481, by rfl⟩ : syracuseStep 1974617 = 1480963) B1480963
theorem B1483211 : Blo 583288 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1319435 : Blo 583288 1319435 := bstep (se 1 (by rfl) ⟨989576, by rfl⟩ : syracuseStep 1319435 = 1979153) B1979153
theorem B1319489 : Blo 583288 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B4006493 : Blo 583288 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B2499331 : Blo 583288 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B1319705 : Blo 583288 1319705 := bstep (se 2 (by rfl) ⟨494889, by rfl⟩ : syracuseStep 1319705 = 989779) B989779
theorem B4760365 : Blo 583288 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B1319795 : Blo 583288 1319795 := bstep (se 1 (by rfl) ⟨989846, by rfl⟩ : syracuseStep 1319795 = 1979693) B1979693
theorem B1319831 : Blo 583288 1319831 := bstep (se 1 (by rfl) ⟨989873, by rfl⟩ : syracuseStep 1319831 = 1979747) B1979747
theorem B1975319 : Blo 583288 1975319 := bstep (se 1 (by rfl) ⟨1481489, by rfl⟩ : syracuseStep 1975319 = 2962979) B2962979
theorem B1778753 : Blo 583288 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B1320011 : Blo 583288 1320011 := bstep (se 1 (by rfl) ⟨990008, by rfl⟩ : syracuseStep 1320011 = 1980017) B1980017
theorem B2499673 : Blo 583288 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B1320065 : Blo 583288 1320065 := bstep (se 2 (by rfl) ⟨495024, by rfl⟩ : syracuseStep 1320065 = 990049) B990049
theorem B1123507 : Blo 583288 1123507 := bstep (se 1 (by rfl) ⟨842630, by rfl⟩ : syracuseStep 1123507 = 1685261) B1685261
theorem B1582301 : Blo 583288 1582301 := bstep (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) B593363
theorem B1189207 : Blo 583288 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B1320281 : Blo 583288 1320281 := bstep (se 2 (by rfl) ⟨495105, by rfl⟩ : syracuseStep 1320281 = 990211) B990211
theorem B1484183 : Blo 583288 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1320371 : Blo 583288 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B1320407 : Blo 583288 1320407 := bstep (se 1 (by rfl) ⟨990305, by rfl⟩ : syracuseStep 1320407 = 1980611) B1980611
theorem B2369027 : Blo 583288 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B1975859 : Blo 583288 1975859 := bstep (se 1 (by rfl) ⟨1481894, by rfl⟩ : syracuseStep 1975859 = 2963789) B2963789
theorem B1189451 : Blo 583288 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B1320587 : Blo 583288 1320587 := bstep (se 1 (by rfl) ⟨990440, by rfl⟩ : syracuseStep 1320587 = 1980881) B1980881
theorem B1320641 : Blo 583288 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B35923661 : Blo 583288 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B1976129 : Blo 583288 1976129 := bstep (se 2 (by rfl) ⟨741048, by rfl⟩ : syracuseStep 1976129 = 1482097) B1482097
theorem B1320857 : Blo 583288 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B1320947 : Blo 583288 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B2500631 : Blo 583288 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B1320983 : Blo 583288 1320983 := bstep (se 1 (by rfl) ⟨990737, by rfl⟩ : syracuseStep 1320983 = 1981475) B1981475
theorem B1484851 : Blo 583288 1484851 := bstep (se 1 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 1484851 = 2227277) B2227277
theorem B15050933 : Blo 583288 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B1484993 : Blo 583288 1484993 := bstep (se 2 (by rfl) ⟨556872, by rfl⟩ : syracuseStep 1484993 = 1113745) B1113745
theorem B1321163 : Blo 583288 1321163 := bstep (se 1 (by rfl) ⟨990872, by rfl⟩ : syracuseStep 1321163 = 1981745) B1981745
theorem B2959577 : Blo 583288 2959577 := bstep (se 2 (by rfl) ⟨1109841, by rfl⟩ : syracuseStep 2959577 = 2219683) B2219683
theorem B1321217 : Blo 583288 1321217 := bstep (se 2 (by rfl) ⟨495456, by rfl⟩ : syracuseStep 1321217 = 990913) B990913
theorem B15444229 : Blo 583288 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B1583383 : Blo 583288 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B1976669 : Blo 583288 1976669 := bstep (se 3 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 1976669 = 741251) B741251
theorem B9743435 : Blo 583288 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B4992101 : Blo 583288 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B4730033 : Blo 583288 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B4435235 : Blo 583288 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B3288385 : Blo 583288 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B1486259 : Blo 583288 1486259 := bstep (se 1 (by rfl) ⟨1114694, by rfl⟩ : syracuseStep 1486259 = 2229389) B2229389
theorem B1977803 : Blo 583288 1977803 := bstep (se 1 (by rfl) ⟨1483352, by rfl⟩ : syracuseStep 1977803 = 2966705) B2966705
theorem B830935 : Blo 583288 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B2666029 : Blo 583288 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2502323 : Blo 583288 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B1978073 : Blo 583288 1978073 := bstep (se 2 (by rfl) ⟨741777, by rfl⟩ : syracuseStep 1978073 = 1483555) B1483555
theorem B4992785 : Blo 583288 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B2961197 : Blo 583288 2961197 := bstep (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) B1110449
theorem B3747971 : Blo 583288 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B1781939 : Blo 583288 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B831755 : Blo 583288 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B1978775 : Blo 583288 1978775 := bstep (se 1 (by rfl) ⟨1484081, by rfl⟩ : syracuseStep 1978775 = 2968163) B2968163
theorem B1880471 : Blo 583288 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B3551809 : Blo 583288 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B7221835 : Blo 583288 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B1880779 : Blo 583288 1880779 := bstep (se 1 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 1880779 = 2821169) B2821169
theorem B1979315 : Blo 583288 1979315 := bstep (se 1 (by rfl) ⟨1484486, by rfl⟩ : syracuseStep 1979315 = 2968973) B2968973
theorem B2372611 : Blo 583288 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B2110657 : Blo 583288 2110657 := bstep (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) B1582993
theorem B1979585 : Blo 583288 1979585 := bstep (se 2 (by rfl) ⟨742344, by rfl⟩ : syracuseStep 1979585 = 1484689) B1484689
theorem B701707 : Blo 583288 701707 := bstep (se 1 (by rfl) ⟨526280, by rfl⟩ : syracuseStep 701707 = 1052561) B1052561
theorem B4208051 : Blo 583288 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B12826205 : Blo 583288 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B11417219 : Blo 583288 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1980125 : Blo 583288 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B10860293 : Blo 583288 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B3323693 : Blo 583288 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B1128587 : Blo 583288 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B2505005 : Blo 583288 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B36616493 : Blo 583288 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B1030553 : Blo 583288 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B1686091 : Blo 583288 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B703255 : Blo 583288 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B1981259 : Blo 583288 1981259 := bstep (se 1 (by rfl) ⟨1485944, by rfl⟩ : syracuseStep 1981259 = 2971889) B2971889
theorem B6339545 : Blo 583288 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1981529 : Blo 583288 1981529 := bstep (se 2 (by rfl) ⟨743073, by rfl⟩ : syracuseStep 1981529 = 1486147) B1486147
theorem B2112733 : Blo 583288 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B9977093 : Blo 583288 9977093 := bstep (se 4 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 9977093 = 1870705) B1870705
theorem B2669917 : Blo 583288 2669917 := bstep (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) B1001219
theorem B2965085 : Blo 583288 2965085 := bstep (se 3 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 2965085 = 1111907) B1111907
theorem B1622209 : Blo 583288 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B2245043 : Blo 583288 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B4440581 : Blo 583288 4440581 := bstep (se 4 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 4440581 = 832609) B832609
theorem B4014809 : Blo 583288 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B934681 : Blo 583288 934681 := bstep (se 2 (by rfl) ⟨350505, by rfl⟩ : syracuseStep 934681 = 701011) B701011
theorem B738391 : Blo 583288 738391 := bstep (se 1 (by rfl) ⟨553793, by rfl⟩ : syracuseStep 738391 = 1107587) B1107587
theorem B1852723 : Blo 583288 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B5064067 : Blo 583288 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B2508353 : Blo 583288 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B4212317 : Blo 583288 4212317 := bstep (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) B1579619
theorem B4015709 : Blo 583288 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B2967191 : Blo 583288 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B3163997 : Blo 583288 3163997 := bstep (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) B1186499
theorem B7489381 : Blo 583288 7489381 := bstep (se 4 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 7489381 = 1404259) B1404259
theorem B2377603 : Blo 583288 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B2672833 : Blo 583288 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B2115991 : Blo 583288 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B740107 : Blo 583288 740107 := bstep (se 1 (by rfl) ⟨555080, by rfl⟩ : syracuseStep 740107 = 1110161) B1110161
theorem B3164993 : Blo 583288 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B4443011 : Blo 583288 4443011 := bstep (se 1 (by rfl) ⟨3332258, by rfl⟩ : syracuseStep 4443011 = 6664517) B6664517
theorem B4804019 : Blo 583288 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B741079 : Blo 583288 741079 := bstep (se 1 (by rfl) ⟨555809, by rfl⟩ : syracuseStep 741079 = 1111619) B1111619
theorem B610615 : Blo 583288 610615 := bstep (se 1 (by rfl) ⟨457961, by rfl⟩ : syracuseStep 610615 = 915923) B915923
theorem B2216267 : Blo 583288 2216267 := bstep (se 1 (by rfl) ⟨1662200, by rfl⟩ : syracuseStep 2216267 = 3324401) B3324401
theorem B2216281 : Blo 583288 2216281 := bstep (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) B1662211
theorem B9163109 : Blo 583288 9163109 := bstep (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) B1718083
theorem B741899 : Blo 583288 741899 := bstep (se 1 (by rfl) ⟨556424, by rfl⟩ : syracuseStep 741899 = 1112849) B1112849
theorem B938711 : Blo 583288 938711 := bstep (se 1 (by rfl) ⟨704033, by rfl⟩ : syracuseStep 938711 = 1408067) B1408067
theorem B2380589 : Blo 583288 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B1200961 : Blo 583288 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B939095 : Blo 583288 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B3331165 : Blo 583288 3331165 := bstep (se 3 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 3331165 = 1249187) B1249187
theorem B2970755 : Blo 583288 2970755 := bstep (se 1 (by rfl) ⟨2228066, by rfl⟩ : syracuseStep 2970755 = 4456133) B4456133
theorem B742603 : Blo 583288 742603 := bstep (se 1 (by rfl) ⟨556952, by rfl⟩ : syracuseStep 742603 = 1113905) B1113905
theorem B939223 : Blo 583288 939223 := bstep (se 1 (by rfl) ⟨704417, by rfl⟩ : syracuseStep 939223 = 1408835) B1408835
theorem B2217239 : Blo 583288 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B742871 : Blo 583288 742871 := bstep (se 1 (by rfl) ⟨557153, by rfl⟩ : syracuseStep 742871 = 1114307) B1114307
theorem B1267201 : Blo 583288 1267201 := bstep (se 2 (by rfl) ⟨475200, by rfl⟩ : syracuseStep 1267201 = 950401) B950401
theorem B1267265 : Blo 583288 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B3757661 : Blo 583288 3757661 := bstep (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) B1409123
theorem B940043 : Blo 583288 940043 := bstep (se 1 (by rfl) ⟨705032, by rfl⟩ : syracuseStep 940043 = 1410065) B1410065
theorem B5003309 : Blo 583288 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B940171 : Blo 583288 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B1661107 : Blo 583288 1661107 := bstep (se 1 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 1661107 = 2491661) B2491661
theorem B4741325 : Blo 583288 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B4446413 : Blo 583288 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B2676995 : Blo 583288 2676995 := bstep (se 1 (by rfl) ⟨2007746, by rfl⟩ : syracuseStep 2676995 = 4015493) B4015493
theorem B842071 : Blo 583288 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B874955 : Blo 583288 874955 := bstep (se 1 (by rfl) ⟨656216, by rfl⟩ : syracuseStep 874955 = 1312433) B1312433
theorem B874967 : Blo 583288 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B2218499 : Blo 583288 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B875033 : Blo 583288 875033 := bstep (se 2 (by rfl) ⟨328137, by rfl⟩ : syracuseStep 875033 = 656275) B656275
theorem B875147 : Blo 583288 875147 := bstep (se 1 (by rfl) ⟨656360, by rfl⟩ : syracuseStep 875147 = 1312721) B1312721
theorem B875159 : Blo 583288 875159 := bstep (se 1 (by rfl) ⟨656369, by rfl⟩ : syracuseStep 875159 = 1312739) B1312739
theorem B4446899 : Blo 583288 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B875225 : Blo 583288 875225 := bstep (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) B656419
theorem B1334081 : Blo 583288 1334081 := bstep (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) B1000561
theorem B875339 : Blo 583288 875339 := bstep (se 1 (by rfl) ⟨656504, by rfl⟩ : syracuseStep 875339 = 1313009) B1313009
theorem B875351 : Blo 583288 875351 := bstep (se 1 (by rfl) ⟨656513, by rfl⟩ : syracuseStep 875351 = 1313027) B1313027
theorem B875417 : Blo 583288 875417 := bstep (se 2 (by rfl) ⟨328281, by rfl⟩ : syracuseStep 875417 = 656563) B656563
theorem B2710451 : Blo 583288 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B875531 : Blo 583288 875531 := bstep (se 1 (by rfl) ⟨656648, by rfl⟩ : syracuseStep 875531 = 1313297) B1313297
theorem B875543 : Blo 583288 875543 := bstep (se 1 (by rfl) ⟨656657, by rfl⟩ : syracuseStep 875543 = 1313315) B1313315
theorem B875609 : Blo 583288 875609 := bstep (se 2 (by rfl) ⟨328353, by rfl⟩ : syracuseStep 875609 = 656707) B656707
theorem B875723 : Blo 583288 875723 := bstep (se 1 (by rfl) ⟨656792, by rfl⟩ : syracuseStep 875723 = 1313585) B1313585
theorem B875735 : Blo 583288 875735 := bstep (se 1 (by rfl) ⟨656801, by rfl⟩ : syracuseStep 875735 = 1313603) B1313603
theorem B875801 : Blo 583288 875801 := bstep (se 2 (by rfl) ⟨328425, by rfl⟩ : syracuseStep 875801 = 656851) B656851
theorem B875915 : Blo 583288 875915 := bstep (se 1 (by rfl) ⟨656936, by rfl⟩ : syracuseStep 875915 = 1313873) B1313873
theorem B875927 : Blo 583288 875927 := bstep (se 1 (by rfl) ⟨656945, by rfl⟩ : syracuseStep 875927 = 1313891) B1313891
theorem B875993 : Blo 583288 875993 := bstep (se 2 (by rfl) ⟨328497, by rfl⟩ : syracuseStep 875993 = 656995) B656995
theorem B876107 : Blo 583288 876107 := bstep (se 1 (by rfl) ⟨657080, by rfl⟩ : syracuseStep 876107 = 1314161) B1314161
theorem B876119 : Blo 583288 876119 := bstep (se 1 (by rfl) ⟨657089, by rfl⟩ : syracuseStep 876119 = 1314179) B1314179
theorem B4742749 : Blo 583288 4742749 := bstep (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) B1778531
theorem B876185 : Blo 583288 876185 := bstep (se 2 (by rfl) ⟨328569, by rfl⟩ : syracuseStep 876185 = 657139) B657139
theorem B876299 : Blo 583288 876299 := bstep (se 1 (by rfl) ⟨657224, by rfl⟩ : syracuseStep 876299 = 1314449) B1314449
theorem B876311 : Blo 583288 876311 := bstep (se 1 (by rfl) ⟨657233, by rfl⟩ : syracuseStep 876311 = 1314467) B1314467
theorem B19259201 : Blo 583288 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B876377 : Blo 583288 876377 := bstep (se 2 (by rfl) ⟨328641, by rfl⟩ : syracuseStep 876377 = 657283) B657283
theorem B876491 : Blo 583288 876491 := bstep (se 1 (by rfl) ⟨657368, by rfl⟩ : syracuseStep 876491 = 1314737) B1314737
theorem B876503 : Blo 583288 876503 := bstep (se 1 (by rfl) ⟨657377, by rfl⟩ : syracuseStep 876503 = 1314755) B1314755
theorem B876569 : Blo 583288 876569 := bstep (se 2 (by rfl) ⟨328713, by rfl⟩ : syracuseStep 876569 = 657427) B657427
theorem B1335361 : Blo 583288 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B4448357 : Blo 583288 4448357 := bstep (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) B834067
theorem B876683 : Blo 583288 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B876695 : Blo 583288 876695 := bstep (se 1 (by rfl) ⟨657521, by rfl⟩ : syracuseStep 876695 = 1315043) B1315043
theorem B876761 : Blo 583288 876761 := bstep (se 2 (by rfl) ⟨328785, by rfl⟩ : syracuseStep 876761 = 657571) B657571
theorem B876875 : Blo 583288 876875 := bstep (se 1 (by rfl) ⟨657656, by rfl⟩ : syracuseStep 876875 = 1315313) B1315313
theorem B876887 : Blo 583288 876887 := bstep (se 1 (by rfl) ⟨657665, by rfl⟩ : syracuseStep 876887 = 1315331) B1315331
theorem B844121 : Blo 583288 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B876953 : Blo 583288 876953 := bstep (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) B657715
theorem B877067 : Blo 583288 877067 := bstep (se 1 (by rfl) ⟨657800, by rfl⟩ : syracuseStep 877067 = 1315601) B1315601
theorem B10117649 : Blo 583288 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B877079 : Blo 583288 877079 := bstep (se 1 (by rfl) ⟨657809, by rfl⟩ : syracuseStep 877079 = 1315619) B1315619
theorem B4448843 : Blo 583288 4448843 := bstep (se 1 (by rfl) ⟨3336632, by rfl⟩ : syracuseStep 4448843 = 6673265) B6673265
theorem B877145 : Blo 583288 877145 := bstep (se 2 (by rfl) ⟨328929, by rfl⟩ : syracuseStep 877145 = 657859) B657859
theorem B1270451 : Blo 583288 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B877259 : Blo 583288 877259 := bstep (se 1 (by rfl) ⟨657944, by rfl⟩ : syracuseStep 877259 = 1315889) B1315889
theorem B877271 : Blo 583288 877271 := bstep (se 1 (by rfl) ⟨657953, by rfl⟩ : syracuseStep 877271 = 1315907) B1315907
theorem B877337 : Blo 583288 877337 := bstep (se 2 (by rfl) ⟨329001, by rfl⟩ : syracuseStep 877337 = 658003) B658003
theorem B877451 : Blo 583288 877451 := bstep (se 1 (by rfl) ⟨658088, by rfl⟩ : syracuseStep 877451 = 1316177) B1316177
theorem B877463 : Blo 583288 877463 := bstep (se 1 (by rfl) ⟨658097, by rfl⟩ : syracuseStep 877463 = 1316195) B1316195
theorem B5006285 : Blo 583288 5006285 := bstep (se 3 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 5006285 = 1877357) B1877357
theorem B877529 : Blo 583288 877529 := bstep (se 2 (by rfl) ⟨329073, by rfl⟩ : syracuseStep 877529 = 658147) B658147
theorem B1664023 : Blo 583288 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B877643 : Blo 583288 877643 := bstep (se 1 (by rfl) ⟨658232, by rfl⟩ : syracuseStep 877643 = 1316465) B1316465
theorem B877655 : Blo 583288 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B877721 : Blo 583288 877721 := bstep (se 2 (by rfl) ⟨329145, by rfl⟩ : syracuseStep 877721 = 658291) B658291
theorem B877835 : Blo 583288 877835 := bstep (se 1 (by rfl) ⟨658376, by rfl⟩ : syracuseStep 877835 = 1316753) B1316753
theorem B877847 : Blo 583288 877847 := bstep (se 1 (by rfl) ⟨658385, by rfl⟩ : syracuseStep 877847 = 1316771) B1316771
theorem B7595309 : Blo 583288 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B877913 : Blo 583288 877913 := bstep (se 2 (by rfl) ⟨329217, by rfl⟩ : syracuseStep 877913 = 658435) B658435
theorem B2811287 : Blo 583288 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B878027 : Blo 583288 878027 := bstep (se 1 (by rfl) ⟨658520, by rfl⟩ : syracuseStep 878027 = 1317041) B1317041
theorem B878039 : Blo 583288 878039 := bstep (se 1 (by rfl) ⟨658529, by rfl⟩ : syracuseStep 878039 = 1317059) B1317059
theorem B1336819 : Blo 583288 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B878105 : Blo 583288 878105 := bstep (se 2 (by rfl) ⟨329289, by rfl⟩ : syracuseStep 878105 = 658579) B658579
theorem B2221613 : Blo 583288 2221613 := bstep (se 3 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 2221613 = 833105) B833105
theorem B583307 : Blo 583288 583307 := bstep (se 1 (by rfl) ⟨437480, by rfl⟩ : syracuseStep 583307 = 874961) B874961
theorem B878219 : Blo 583288 878219 := bstep (se 1 (by rfl) ⟨658664, by rfl⟩ : syracuseStep 878219 = 1317329) B1317329
theorem B583319 : Blo 583288 583319 := bstep (se 1 (by rfl) ⟨437489, by rfl⟩ : syracuseStep 583319 = 874979) B874979
theorem B878231 : Blo 583288 878231 := bstep (se 1 (by rfl) ⟨658673, by rfl⟩ : syracuseStep 878231 = 1317347) B1317347
theorem B583339 : Blo 583288 583339 := bstep (se 1 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 583339 = 875009) B875009
theorem B583351 : Blo 583288 583351 := bstep (se 1 (by rfl) ⟨437513, by rfl⟩ : syracuseStep 583351 = 875027) B875027
theorem B583371 : Blo 583288 583371 := bstep (se 1 (by rfl) ⟨437528, by rfl⟩ : syracuseStep 583371 = 875057) B875057
theorem B583383 : Blo 583288 583383 := bstep (se 1 (by rfl) ⟨437537, by rfl⟩ : syracuseStep 583383 = 875075) B875075
theorem B878297 : Blo 583288 878297 := bstep (se 2 (by rfl) ⟨329361, by rfl⟩ : syracuseStep 878297 = 658723) B658723
theorem B583403 : Blo 583288 583403 := bstep (se 1 (by rfl) ⟨437552, by rfl⟩ : syracuseStep 583403 = 875105) B875105
theorem B583415 : Blo 583288 583415 := bstep (se 1 (by rfl) ⟨437561, by rfl⟩ : syracuseStep 583415 = 875123) B875123
theorem B583435 : Blo 583288 583435 := bstep (se 1 (by rfl) ⟨437576, by rfl⟩ : syracuseStep 583435 = 875153) B875153
theorem B583447 : Blo 583288 583447 := bstep (se 1 (by rfl) ⟨437585, by rfl⟩ : syracuseStep 583447 = 875171) B875171
theorem B583467 : Blo 583288 583467 := bstep (se 1 (by rfl) ⟨437600, by rfl⟩ : syracuseStep 583467 = 875201) B875201
theorem B583479 : Blo 583288 583479 := bstep (se 1 (by rfl) ⟨437609, by rfl⟩ : syracuseStep 583479 = 875219) B875219
theorem B2713409 : Blo 583288 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B583499 : Blo 583288 583499 := bstep (se 1 (by rfl) ⟨437624, by rfl⟩ : syracuseStep 583499 = 875249) B875249
theorem B878411 : Blo 583288 878411 := bstep (se 1 (by rfl) ⟨658808, by rfl⟩ : syracuseStep 878411 = 1317617) B1317617
theorem B583511 : Blo 583288 583511 := bstep (se 1 (by rfl) ⟨437633, by rfl⟩ : syracuseStep 583511 = 875267) B875267
theorem B878423 : Blo 583288 878423 := bstep (se 1 (by rfl) ⟨658817, by rfl⟩ : syracuseStep 878423 = 1317635) B1317635
theorem B14215013 : Blo 583288 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B583531 : Blo 583288 583531 := bstep (se 1 (by rfl) ⟨437648, by rfl⟩ : syracuseStep 583531 = 875297) B875297
theorem B583543 : Blo 583288 583543 := bstep (se 1 (by rfl) ⟨437657, by rfl⟩ : syracuseStep 583543 = 875315) B875315
theorem B583563 : Blo 583288 583563 := bstep (se 1 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 583563 = 875345) B875345
theorem B583575 : Blo 583288 583575 := bstep (se 1 (by rfl) ⟨437681, by rfl⟩ : syracuseStep 583575 = 875363) B875363
theorem B878489 : Blo 583288 878489 := bstep (se 2 (by rfl) ⟨329433, by rfl⟩ : syracuseStep 878489 = 658867) B658867
theorem B583595 : Blo 583288 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B583607 : Blo 583288 583607 := bstep (se 1 (by rfl) ⟨437705, by rfl⟩ : syracuseStep 583607 = 875411) B875411
theorem B583627 : Blo 583288 583627 := bstep (se 1 (by rfl) ⟨437720, by rfl⟩ : syracuseStep 583627 = 875441) B875441
theorem B583639 : Blo 583288 583639 := bstep (se 1 (by rfl) ⟨437729, by rfl⟩ : syracuseStep 583639 = 875459) B875459
theorem B583659 : Blo 583288 583659 := bstep (se 1 (by rfl) ⟨437744, by rfl⟩ : syracuseStep 583659 = 875489) B875489
theorem B583671 : Blo 583288 583671 := bstep (se 1 (by rfl) ⟨437753, by rfl⟩ : syracuseStep 583671 = 875507) B875507
theorem B583691 : Blo 583288 583691 := bstep (se 1 (by rfl) ⟨437768, by rfl⟩ : syracuseStep 583691 = 875537) B875537
theorem B878603 : Blo 583288 878603 := bstep (se 1 (by rfl) ⟨658952, by rfl⟩ : syracuseStep 878603 = 1317905) B1317905
theorem B583703 : Blo 583288 583703 := bstep (se 1 (by rfl) ⟨437777, by rfl⟩ : syracuseStep 583703 = 875555) B875555
theorem B878615 : Blo 583288 878615 := bstep (se 1 (by rfl) ⟨658961, by rfl⟩ : syracuseStep 878615 = 1317923) B1317923
theorem B583723 : Blo 583288 583723 := bstep (se 1 (by rfl) ⟨437792, by rfl⟩ : syracuseStep 583723 = 875585) B875585
theorem B5335085 : Blo 583288 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B1108019 : Blo 583288 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B583735 : Blo 583288 583735 := bstep (se 1 (by rfl) ⟨437801, by rfl⟩ : syracuseStep 583735 = 875603) B875603
theorem B583755 : Blo 583288 583755 := bstep (se 1 (by rfl) ⟨437816, by rfl⟩ : syracuseStep 583755 = 875633) B875633
theorem B583767 : Blo 583288 583767 := bstep (se 1 (by rfl) ⟨437825, by rfl⟩ : syracuseStep 583767 = 875651) B875651
theorem B878681 : Blo 583288 878681 := bstep (se 2 (by rfl) ⟨329505, by rfl⟩ : syracuseStep 878681 = 659011) B659011
theorem B583787 : Blo 583288 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B583799 : Blo 583288 583799 := bstep (se 1 (by rfl) ⟨437849, by rfl⟩ : syracuseStep 583799 = 875699) B875699
theorem B583819 : Blo 583288 583819 := bstep (se 1 (by rfl) ⟨437864, by rfl⟩ : syracuseStep 583819 = 875729) B875729
theorem B583831 : Blo 583288 583831 := bstep (se 1 (by rfl) ⟨437873, by rfl⟩ : syracuseStep 583831 = 875747) B875747
theorem B583851 : Blo 583288 583851 := bstep (se 1 (by rfl) ⟨437888, by rfl⟩ : syracuseStep 583851 = 875777) B875777
theorem B583863 : Blo 583288 583863 := bstep (se 1 (by rfl) ⟨437897, by rfl⟩ : syracuseStep 583863 = 875795) B875795
theorem B1108171 : Blo 583288 1108171 := bstep (se 1 (by rfl) ⟨831128, by rfl⟩ : syracuseStep 1108171 = 1662257) B1662257
theorem B583883 : Blo 583288 583883 := bstep (se 1 (by rfl) ⟨437912, by rfl⟩ : syracuseStep 583883 = 875825) B875825
theorem B878795 : Blo 583288 878795 := bstep (se 1 (by rfl) ⟨659096, by rfl⟩ : syracuseStep 878795 = 1318193) B1318193
theorem B583895 : Blo 583288 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B878807 : Blo 583288 878807 := bstep (se 1 (by rfl) ⟨659105, by rfl⟩ : syracuseStep 878807 = 1318211) B1318211
theorem B583915 : Blo 583288 583915 := bstep (se 1 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 583915 = 875873) B875873
theorem B583927 : Blo 583288 583927 := bstep (se 1 (by rfl) ⟨437945, by rfl⟩ : syracuseStep 583927 = 875891) B875891
theorem B5335301 : Blo 583288 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B583947 : Blo 583288 583947 := bstep (se 1 (by rfl) ⟨437960, by rfl⟩ : syracuseStep 583947 = 875921) B875921
theorem B583959 : Blo 583288 583959 := bstep (se 1 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 583959 = 875939) B875939
theorem B878873 : Blo 583288 878873 := bstep (se 2 (by rfl) ⟨329577, by rfl⟩ : syracuseStep 878873 = 659155) B659155
theorem B583979 : Blo 583288 583979 := bstep (se 1 (by rfl) ⟨437984, by rfl⟩ : syracuseStep 583979 = 875969) B875969
theorem B2222387 : Blo 583288 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B583991 : Blo 583288 583991 := bstep (se 1 (by rfl) ⟨437993, by rfl⟩ : syracuseStep 583991 = 875987) B875987
theorem B584011 : Blo 583288 584011 := bstep (se 1 (by rfl) ⟨438008, by rfl⟩ : syracuseStep 584011 = 876017) B876017
theorem B1665355 : Blo 583288 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B584023 : Blo 583288 584023 := bstep (se 1 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 584023 = 876035) B876035
theorem B584043 : Blo 583288 584043 := bstep (se 1 (by rfl) ⟨438032, by rfl⟩ : syracuseStep 584043 = 876065) B876065
theorem B584055 : Blo 583288 584055 := bstep (se 1 (by rfl) ⟨438041, by rfl⟩ : syracuseStep 584055 = 876083) B876083
theorem B4745603 : Blo 583288 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B584075 : Blo 583288 584075 := bstep (se 1 (by rfl) ⟨438056, by rfl⟩ : syracuseStep 584075 = 876113) B876113
theorem B878987 : Blo 583288 878987 := bstep (se 1 (by rfl) ⟨659240, by rfl⟩ : syracuseStep 878987 = 1318481) B1318481
theorem B584087 : Blo 583288 584087 := bstep (se 1 (by rfl) ⟨438065, by rfl⟩ : syracuseStep 584087 = 876131) B876131
theorem B878999 : Blo 583288 878999 := bstep (se 1 (by rfl) ⟨659249, by rfl⟩ : syracuseStep 878999 = 1318499) B1318499
theorem B584107 : Blo 583288 584107 := bstep (se 1 (by rfl) ⟨438080, by rfl⟩ : syracuseStep 584107 = 876161) B876161
theorem B584119 : Blo 583288 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B584139 : Blo 583288 584139 := bstep (se 1 (by rfl) ⟨438104, by rfl⟩ : syracuseStep 584139 = 876209) B876209
theorem B584151 : Blo 583288 584151 := bstep (se 1 (by rfl) ⟨438113, by rfl⟩ : syracuseStep 584151 = 876227) B876227
theorem B879065 : Blo 583288 879065 := bstep (se 2 (by rfl) ⟨329649, by rfl⟩ : syracuseStep 879065 = 659299) B659299
theorem B584171 : Blo 583288 584171 := bstep (se 1 (by rfl) ⟨438128, by rfl⟩ : syracuseStep 584171 = 876257) B876257
theorem B584183 : Blo 583288 584183 := bstep (se 1 (by rfl) ⟨438137, by rfl⟩ : syracuseStep 584183 = 876275) B876275
theorem B584203 : Blo 583288 584203 := bstep (se 1 (by rfl) ⟨438152, by rfl⟩ : syracuseStep 584203 = 876305) B876305
theorem B584215 : Blo 583288 584215 := bstep (se 1 (by rfl) ⟨438161, by rfl⟩ : syracuseStep 584215 = 876323) B876323
theorem B1108505 : Blo 583288 1108505 := bstep (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) B831379
theorem B584235 : Blo 583288 584235 := bstep (se 1 (by rfl) ⟨438176, by rfl⟩ : syracuseStep 584235 = 876353) B876353
theorem B584247 : Blo 583288 584247 := bstep (se 1 (by rfl) ⟨438185, by rfl⟩ : syracuseStep 584247 = 876371) B876371
theorem B584267 : Blo 583288 584267 := bstep (se 1 (by rfl) ⟨438200, by rfl⟩ : syracuseStep 584267 = 876401) B876401
theorem B879179 : Blo 583288 879179 := bstep (se 1 (by rfl) ⟨659384, by rfl⟩ : syracuseStep 879179 = 1318769) B1318769
theorem B584279 : Blo 583288 584279 := bstep (se 1 (by rfl) ⟨438209, by rfl⟩ : syracuseStep 584279 = 876419) B876419
theorem B879191 : Blo 583288 879191 := bstep (se 1 (by rfl) ⟨659393, by rfl⟩ : syracuseStep 879191 = 1318787) B1318787
theorem B1665629 : Blo 583288 1665629 := bstep (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) B624611
theorem B584299 : Blo 583288 584299 := bstep (se 1 (by rfl) ⟨438224, by rfl⟩ : syracuseStep 584299 = 876449) B876449
theorem B584311 : Blo 583288 584311 := bstep (se 1 (by rfl) ⟨438233, by rfl⟩ : syracuseStep 584311 = 876467) B876467
theorem B584331 : Blo 583288 584331 := bstep (se 1 (by rfl) ⟨438248, by rfl⟩ : syracuseStep 584331 = 876497) B876497
theorem B584343 : Blo 583288 584343 := bstep (se 1 (by rfl) ⟨438257, by rfl⟩ : syracuseStep 584343 = 876515) B876515
theorem B879257 : Blo 583288 879257 := bstep (se 2 (by rfl) ⟨329721, by rfl⟩ : syracuseStep 879257 = 659443) B659443
theorem B584363 : Blo 583288 584363 := bstep (se 1 (by rfl) ⟨438272, by rfl⟩ : syracuseStep 584363 = 876545) B876545
theorem B584375 : Blo 583288 584375 := bstep (se 1 (by rfl) ⟨438281, by rfl⟩ : syracuseStep 584375 = 876563) B876563
theorem B584395 : Blo 583288 584395 := bstep (se 1 (by rfl) ⟨438296, by rfl⟩ : syracuseStep 584395 = 876593) B876593
theorem B1338059 : Blo 583288 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B584407 : Blo 583288 584407 := bstep (se 1 (by rfl) ⟨438305, by rfl⟩ : syracuseStep 584407 = 876611) B876611
theorem B584427 : Blo 583288 584427 := bstep (se 1 (by rfl) ⟨438320, by rfl⟩ : syracuseStep 584427 = 876641) B876641
theorem B584439 : Blo 583288 584439 := bstep (se 1 (by rfl) ⟨438329, by rfl⟩ : syracuseStep 584439 = 876659) B876659
theorem B584459 : Blo 583288 584459 := bstep (se 1 (by rfl) ⟨438344, by rfl⟩ : syracuseStep 584459 = 876689) B876689
theorem B879371 : Blo 583288 879371 := bstep (se 1 (by rfl) ⟨659528, by rfl⟩ : syracuseStep 879371 = 1319057) B1319057
theorem B584471 : Blo 583288 584471 := bstep (se 1 (by rfl) ⟨438353, by rfl⟩ : syracuseStep 584471 = 876707) B876707
theorem B879383 : Blo 583288 879383 := bstep (se 1 (by rfl) ⟨659537, by rfl⟩ : syracuseStep 879383 = 1319075) B1319075
theorem B584491 : Blo 583288 584491 := bstep (se 1 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 584491 = 876737) B876737
theorem B584503 : Blo 583288 584503 := bstep (se 1 (by rfl) ⟨438377, by rfl⟩ : syracuseStep 584503 = 876755) B876755
theorem B584523 : Blo 583288 584523 := bstep (se 1 (by rfl) ⟨438392, by rfl⟩ : syracuseStep 584523 = 876785) B876785
theorem B584535 : Blo 583288 584535 := bstep (se 1 (by rfl) ⟨438401, by rfl⟩ : syracuseStep 584535 = 876803) B876803
theorem B879449 : Blo 583288 879449 := bstep (se 2 (by rfl) ⟨329793, by rfl⟩ : syracuseStep 879449 = 659587) B659587
theorem B584555 : Blo 583288 584555 := bstep (se 1 (by rfl) ⟨438416, by rfl⟩ : syracuseStep 584555 = 876833) B876833
theorem B584567 : Blo 583288 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B584587 : Blo 583288 584587 := bstep (se 1 (by rfl) ⟨438440, by rfl⟩ : syracuseStep 584587 = 876881) B876881
theorem B584599 : Blo 583288 584599 := bstep (se 1 (by rfl) ⟨438449, by rfl⟩ : syracuseStep 584599 = 876899) B876899
theorem B584619 : Blo 583288 584619 := bstep (se 1 (by rfl) ⟨438464, by rfl⟩ : syracuseStep 584619 = 876929) B876929
theorem B1665971 : Blo 583288 1665971 := bstep (se 1 (by rfl) ⟨1249478, by rfl⟩ : syracuseStep 1665971 = 2498957) B2498957
theorem B584631 : Blo 583288 584631 := bstep (se 1 (by rfl) ⟨438473, by rfl⟩ : syracuseStep 584631 = 876947) B876947
theorem B584651 : Blo 583288 584651 := bstep (se 1 (by rfl) ⟨438488, by rfl⟩ : syracuseStep 584651 = 876977) B876977
theorem B879563 : Blo 583288 879563 := bstep (se 1 (by rfl) ⟨659672, by rfl⟩ : syracuseStep 879563 = 1319345) B1319345
theorem B584663 : Blo 583288 584663 := bstep (se 1 (by rfl) ⟨438497, by rfl⟩ : syracuseStep 584663 = 876995) B876995
theorem B879575 : Blo 583288 879575 := bstep (se 1 (by rfl) ⟨659681, by rfl⟩ : syracuseStep 879575 = 1319363) B1319363
theorem B584683 : Blo 583288 584683 := bstep (se 1 (by rfl) ⟨438512, by rfl⟩ : syracuseStep 584683 = 877025) B877025
theorem B584695 : Blo 583288 584695 := bstep (se 1 (by rfl) ⟨438521, by rfl⟩ : syracuseStep 584695 = 877043) B877043
theorem B584715 : Blo 583288 584715 := bstep (se 1 (by rfl) ⟨438536, by rfl⟩ : syracuseStep 584715 = 877073) B877073
theorem B584727 : Blo 583288 584727 := bstep (se 1 (by rfl) ⟨438545, by rfl⟩ : syracuseStep 584727 = 877091) B877091
theorem B879641 : Blo 583288 879641 := bstep (se 2 (by rfl) ⟨329865, by rfl⟩ : syracuseStep 879641 = 659731) B659731
theorem B584747 : Blo 583288 584747 := bstep (se 1 (by rfl) ⟨438560, by rfl⟩ : syracuseStep 584747 = 877121) B877121
theorem B584759 : Blo 583288 584759 := bstep (se 1 (by rfl) ⟨438569, by rfl⟩ : syracuseStep 584759 = 877139) B877139
theorem B584779 : Blo 583288 584779 := bstep (se 1 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 584779 = 877169) B877169
theorem B584791 : Blo 583288 584791 := bstep (se 1 (by rfl) ⟨438593, by rfl⟩ : syracuseStep 584791 = 877187) B877187
theorem B584811 : Blo 583288 584811 := bstep (se 1 (by rfl) ⟨438608, by rfl⟩ : syracuseStep 584811 = 877217) B877217
theorem B584823 : Blo 583288 584823 := bstep (se 1 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 584823 = 877235) B877235
theorem B879755 : Blo 583288 879755 := bstep (se 1 (by rfl) ⟨659816, by rfl⟩ : syracuseStep 879755 = 1319633) B1319633
theorem B584843 : Blo 583288 584843 := bstep (se 1 (by rfl) ⟨438632, by rfl⟩ : syracuseStep 584843 = 877265) B877265
theorem B1109143 : Blo 583288 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B584855 : Blo 583288 584855 := bstep (se 1 (by rfl) ⟨438641, by rfl⟩ : syracuseStep 584855 = 877283) B877283
theorem B879767 : Blo 583288 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B584875 : Blo 583288 584875 := bstep (se 1 (by rfl) ⟨438656, by rfl⟩ : syracuseStep 584875 = 877313) B877313
theorem B584887 : Blo 583288 584887 := bstep (se 1 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 584887 = 877331) B877331
theorem B584907 : Blo 583288 584907 := bstep (se 1 (by rfl) ⟨438680, by rfl⟩ : syracuseStep 584907 = 877361) B877361
theorem B584919 : Blo 583288 584919 := bstep (se 1 (by rfl) ⟨438689, by rfl⟩ : syracuseStep 584919 = 877379) B877379
theorem B879833 : Blo 583288 879833 := bstep (se 2 (by rfl) ⟨329937, by rfl⟩ : syracuseStep 879833 = 659875) B659875
theorem B584939 : Blo 583288 584939 := bstep (se 1 (by rfl) ⟨438704, by rfl⟩ : syracuseStep 584939 = 877409) B877409
theorem B584951 : Blo 583288 584951 := bstep (se 1 (by rfl) ⟨438713, by rfl⟩ : syracuseStep 584951 = 877427) B877427
theorem B584971 : Blo 583288 584971 := bstep (se 1 (by rfl) ⟨438728, by rfl⟩ : syracuseStep 584971 = 877457) B877457
theorem B584983 : Blo 583288 584983 := bstep (se 1 (by rfl) ⟨438737, by rfl⟩ : syracuseStep 584983 = 877475) B877475
theorem B585003 : Blo 583288 585003 := bstep (se 1 (by rfl) ⟨438752, by rfl⟩ : syracuseStep 585003 = 877505) B877505
theorem B585015 : Blo 583288 585015 := bstep (se 1 (by rfl) ⟨438761, by rfl⟩ : syracuseStep 585015 = 877523) B877523
theorem B585035 : Blo 583288 585035 := bstep (se 1 (by rfl) ⟨438776, by rfl⟩ : syracuseStep 585035 = 877553) B877553
theorem B879947 : Blo 583288 879947 := bstep (se 1 (by rfl) ⟨659960, by rfl⟩ : syracuseStep 879947 = 1319921) B1319921
theorem B585047 : Blo 583288 585047 := bstep (se 1 (by rfl) ⟨438785, by rfl⟩ : syracuseStep 585047 = 877571) B877571
theorem B879959 : Blo 583288 879959 := bstep (se 1 (by rfl) ⟨659969, by rfl⟩ : syracuseStep 879959 = 1319939) B1319939
theorem B585067 : Blo 583288 585067 := bstep (se 1 (by rfl) ⟨438800, by rfl⟩ : syracuseStep 585067 = 877601) B877601
theorem B585079 : Blo 583288 585079 := bstep (se 1 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 585079 = 877619) B877619
theorem B585099 : Blo 583288 585099 := bstep (se 1 (by rfl) ⟨438824, by rfl⟩ : syracuseStep 585099 = 877649) B877649
theorem B585111 : Blo 583288 585111 := bstep (se 1 (by rfl) ⟨438833, by rfl⟩ : syracuseStep 585111 = 877667) B877667
theorem B880025 : Blo 583288 880025 := bstep (se 2 (by rfl) ⟨330009, by rfl⟩ : syracuseStep 880025 = 660019) B660019
theorem B585131 : Blo 583288 585131 := bstep (se 1 (by rfl) ⟨438848, by rfl⟩ : syracuseStep 585131 = 877697) B877697
theorem B2813363 : Blo 583288 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B585143 : Blo 583288 585143 := bstep (se 1 (by rfl) ⟨438857, by rfl⟩ : syracuseStep 585143 = 877715) B877715
theorem B585163 : Blo 583288 585163 := bstep (se 1 (by rfl) ⟨438872, by rfl⟩ : syracuseStep 585163 = 877745) B877745
theorem B585175 : Blo 583288 585175 := bstep (se 1 (by rfl) ⟨438881, by rfl⟩ : syracuseStep 585175 = 877763) B877763
theorem B585195 : Blo 583288 585195 := bstep (se 1 (by rfl) ⟨438896, by rfl⟩ : syracuseStep 585195 = 877793) B877793
theorem B585207 : Blo 583288 585207 := bstep (se 1 (by rfl) ⟨438905, by rfl⟩ : syracuseStep 585207 = 877811) B877811
theorem B585227 : Blo 583288 585227 := bstep (se 1 (by rfl) ⟨438920, by rfl⟩ : syracuseStep 585227 = 877841) B877841
theorem B880139 : Blo 583288 880139 := bstep (se 1 (by rfl) ⟨660104, by rfl⟩ : syracuseStep 880139 = 1320209) B1320209
theorem B585239 : Blo 583288 585239 := bstep (se 1 (by rfl) ⟨438929, by rfl⟩ : syracuseStep 585239 = 877859) B877859
theorem B880151 : Blo 583288 880151 := bstep (se 1 (by rfl) ⟨660113, by rfl⟩ : syracuseStep 880151 = 1320227) B1320227
theorem B585259 : Blo 583288 585259 := bstep (se 1 (by rfl) ⟨438944, by rfl⟩ : syracuseStep 585259 = 877889) B877889
theorem B585271 : Blo 583288 585271 := bstep (se 1 (by rfl) ⟨438953, by rfl⟩ : syracuseStep 585271 = 877907) B877907
theorem B4222529 : Blo 583288 4222529 := bstep (se 2 (by rfl) ⟨1583448, by rfl⟩ : syracuseStep 4222529 = 3166897) B3166897
theorem B585291 : Blo 583288 585291 := bstep (se 1 (by rfl) ⟨438968, by rfl⟩ : syracuseStep 585291 = 877937) B877937
theorem B585303 : Blo 583288 585303 := bstep (se 1 (by rfl) ⟨438977, by rfl⟩ : syracuseStep 585303 = 877955) B877955
theorem B880217 : Blo 583288 880217 := bstep (se 2 (by rfl) ⟨330081, by rfl⟩ : syracuseStep 880217 = 660163) B660163
theorem B585323 : Blo 583288 585323 := bstep (se 1 (by rfl) ⟨438992, by rfl⟩ : syracuseStep 585323 = 877985) B877985
theorem B585335 : Blo 583288 585335 := bstep (se 1 (by rfl) ⟨439001, by rfl⟩ : syracuseStep 585335 = 878003) B878003
theorem B585355 : Blo 583288 585355 := bstep (se 1 (by rfl) ⟨439016, by rfl⟩ : syracuseStep 585355 = 878033) B878033
theorem B585367 : Blo 583288 585367 := bstep (se 1 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 585367 = 878051) B878051
theorem B585387 : Blo 583288 585387 := bstep (se 1 (by rfl) ⟨439040, by rfl⟩ : syracuseStep 585387 = 878081) B878081
theorem B585399 : Blo 583288 585399 := bstep (se 1 (by rfl) ⟨439049, by rfl⟩ : syracuseStep 585399 = 878099) B878099
theorem B585419 : Blo 583288 585419 := bstep (se 1 (by rfl) ⟨439064, by rfl⟩ : syracuseStep 585419 = 878129) B878129
theorem B880331 : Blo 583288 880331 := bstep (se 1 (by rfl) ⟨660248, by rfl⟩ : syracuseStep 880331 = 1320497) B1320497
theorem B585431 : Blo 583288 585431 := bstep (se 1 (by rfl) ⟨439073, by rfl⟩ : syracuseStep 585431 = 878147) B878147
theorem B880343 : Blo 583288 880343 := bstep (se 1 (by rfl) ⟨660257, by rfl⟩ : syracuseStep 880343 = 1320515) B1320515
theorem B585451 : Blo 583288 585451 := bstep (se 1 (by rfl) ⟨439088, by rfl⟩ : syracuseStep 585451 = 878177) B878177
theorem B585463 : Blo 583288 585463 := bstep (se 1 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 585463 = 878195) B878195
theorem B2223875 : Blo 583288 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B585483 : Blo 583288 585483 := bstep (se 1 (by rfl) ⟨439112, by rfl⟩ : syracuseStep 585483 = 878225) B878225
theorem B585495 : Blo 583288 585495 := bstep (se 1 (by rfl) ⟨439121, by rfl⟩ : syracuseStep 585495 = 878243) B878243
theorem B880409 : Blo 583288 880409 := bstep (se 2 (by rfl) ⟨330153, by rfl⟩ : syracuseStep 880409 = 660307) B660307
theorem B585515 : Blo 583288 585515 := bstep (se 1 (by rfl) ⟨439136, by rfl⟩ : syracuseStep 585515 = 878273) B878273
theorem B585527 : Blo 583288 585527 := bstep (se 1 (by rfl) ⟨439145, by rfl⟩ : syracuseStep 585527 = 878291) B878291
theorem B585547 : Blo 583288 585547 := bstep (se 1 (by rfl) ⟨439160, by rfl⟩ : syracuseStep 585547 = 878321) B878321
theorem B585559 : Blo 583288 585559 := bstep (se 1 (by rfl) ⟨439169, by rfl⟩ : syracuseStep 585559 = 878339) B878339
theorem B4222813 : Blo 583288 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B1929053 : Blo 583288 1929053 := bstep (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) B723395
theorem B585579 : Blo 583288 585579 := bstep (se 1 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 585579 = 878369) B878369
theorem B585591 : Blo 583288 585591 := bstep (se 1 (by rfl) ⟨439193, by rfl⟩ : syracuseStep 585591 = 878387) B878387
theorem B585611 : Blo 583288 585611 := bstep (se 1 (by rfl) ⟨439208, by rfl⟩ : syracuseStep 585611 = 878417) B878417
theorem B880523 : Blo 583288 880523 := bstep (se 1 (by rfl) ⟨660392, by rfl⟩ : syracuseStep 880523 = 1320785) B1320785
theorem B585623 : Blo 583288 585623 := bstep (se 1 (by rfl) ⟨439217, by rfl⟩ : syracuseStep 585623 = 878435) B878435
theorem B880535 : Blo 583288 880535 := bstep (se 1 (by rfl) ⟨660401, by rfl⟩ : syracuseStep 880535 = 1320803) B1320803
theorem B585643 : Blo 583288 585643 := bstep (se 1 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 585643 = 878465) B878465
theorem B585655 : Blo 583288 585655 := bstep (se 1 (by rfl) ⟨439241, by rfl⟩ : syracuseStep 585655 = 878483) B878483
theorem B1109963 : Blo 583288 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B585675 : Blo 583288 585675 := bstep (se 1 (by rfl) ⟨439256, by rfl⟩ : syracuseStep 585675 = 878513) B878513
theorem B585687 : Blo 583288 585687 := bstep (se 1 (by rfl) ⟨439265, by rfl⟩ : syracuseStep 585687 = 878531) B878531
theorem B880601 : Blo 583288 880601 := bstep (se 2 (by rfl) ⟨330225, by rfl⟩ : syracuseStep 880601 = 660451) B660451
theorem B585707 : Blo 583288 585707 := bstep (se 1 (by rfl) ⟨439280, by rfl⟩ : syracuseStep 585707 = 878561) B878561
theorem B585719 : Blo 583288 585719 := bstep (se 1 (by rfl) ⟨439289, by rfl⟩ : syracuseStep 585719 = 878579) B878579
theorem B1110017 : Blo 583288 1110017 := bstep (se 2 (by rfl) ⟨416256, by rfl⟩ : syracuseStep 1110017 = 832513) B832513
theorem B585739 : Blo 583288 585739 := bstep (se 1 (by rfl) ⟨439304, by rfl⟩ : syracuseStep 585739 = 878609) B878609
theorem B585751 : Blo 583288 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B585771 : Blo 583288 585771 := bstep (se 1 (by rfl) ⟨439328, by rfl⟩ : syracuseStep 585771 = 878657) B878657
theorem B585783 : Blo 583288 585783 := bstep (se 1 (by rfl) ⟨439337, by rfl⟩ : syracuseStep 585783 = 878675) B878675
theorem B1142849 : Blo 583288 1142849 := bstep (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) B857137
theorem B585803 : Blo 583288 585803 := bstep (se 1 (by rfl) ⟨439352, by rfl⟩ : syracuseStep 585803 = 878705) B878705
theorem B880715 : Blo 583288 880715 := bstep (se 1 (by rfl) ⟨660536, by rfl⟩ : syracuseStep 880715 = 1321073) B1321073
theorem B585815 : Blo 583288 585815 := bstep (se 1 (by rfl) ⟨439361, by rfl⟩ : syracuseStep 585815 = 878723) B878723
theorem B880727 : Blo 583288 880727 := bstep (se 1 (by rfl) ⟨660545, by rfl⟩ : syracuseStep 880727 = 1321091) B1321091
theorem B585835 : Blo 583288 585835 := bstep (se 1 (by rfl) ⟨439376, by rfl⟩ : syracuseStep 585835 = 878753) B878753
theorem B585847 : Blo 583288 585847 := bstep (se 1 (by rfl) ⟨439385, by rfl⟩ : syracuseStep 585847 = 878771) B878771
theorem B585867 : Blo 583288 585867 := bstep (se 1 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 585867 = 878801) B878801
theorem B585879 : Blo 583288 585879 := bstep (se 1 (by rfl) ⟨439409, by rfl⟩ : syracuseStep 585879 = 878819) B878819
theorem B880793 : Blo 583288 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B585899 : Blo 583288 585899 := bstep (se 1 (by rfl) ⟨439424, by rfl⟩ : syracuseStep 585899 = 878849) B878849
theorem B585911 : Blo 583288 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B2224331 : Blo 583288 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B585931 : Blo 583288 585931 := bstep (se 1 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 585931 = 878897) B878897
theorem B585943 : Blo 583288 585943 := bstep (se 1 (by rfl) ⟨439457, by rfl⟩ : syracuseStep 585943 = 878915) B878915
theorem B585963 : Blo 583288 585963 := bstep (se 1 (by rfl) ⟨439472, by rfl⟩ : syracuseStep 585963 = 878945) B878945
theorem B585975 : Blo 583288 585975 := bstep (se 1 (by rfl) ⟨439481, by rfl⟩ : syracuseStep 585975 = 878963) B878963
theorem B585995 : Blo 583288 585995 := bstep (se 1 (by rfl) ⟨439496, by rfl⟩ : syracuseStep 585995 = 878993) B878993
theorem B880907 : Blo 583288 880907 := bstep (se 1 (by rfl) ⟨660680, by rfl⟩ : syracuseStep 880907 = 1321361) B1321361
theorem B586007 : Blo 583288 586007 := bstep (se 1 (by rfl) ⟨439505, by rfl⟩ : syracuseStep 586007 = 879011) B879011
theorem B880919 : Blo 583288 880919 := bstep (se 1 (by rfl) ⟨660689, by rfl⟩ : syracuseStep 880919 = 1321379) B1321379
theorem B586027 : Blo 583288 586027 := bstep (se 1 (by rfl) ⟨439520, by rfl⟩ : syracuseStep 586027 = 879041) B879041
theorem B2289971 : Blo 583288 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B586039 : Blo 583288 586039 := bstep (se 1 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 586039 = 879059) B879059
theorem B5337419 : Blo 583288 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B586059 : Blo 583288 586059 := bstep (se 1 (by rfl) ⟨439544, by rfl⟩ : syracuseStep 586059 = 879089) B879089
theorem B586071 : Blo 583288 586071 := bstep (se 1 (by rfl) ⟨439553, by rfl⟩ : syracuseStep 586071 = 879107) B879107
theorem B586091 : Blo 583288 586091 := bstep (se 1 (by rfl) ⟨439568, by rfl⟩ : syracuseStep 586091 = 879137) B879137
theorem B586103 : Blo 583288 586103 := bstep (se 1 (by rfl) ⟨439577, by rfl⟩ : syracuseStep 586103 = 879155) B879155
theorem B586123 : Blo 583288 586123 := bstep (se 1 (by rfl) ⟨439592, by rfl⟩ : syracuseStep 586123 = 879185) B879185
theorem B2224529 : Blo 583288 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B586135 : Blo 583288 586135 := bstep (se 1 (by rfl) ⟨439601, by rfl⟩ : syracuseStep 586135 = 879203) B879203
theorem B586155 : Blo 583288 586155 := bstep (se 1 (by rfl) ⟨439616, by rfl⟩ : syracuseStep 586155 = 879233) B879233
theorem B586167 : Blo 583288 586167 := bstep (se 1 (by rfl) ⟨439625, by rfl⟩ : syracuseStep 586167 = 879251) B879251
theorem B586187 : Blo 583288 586187 := bstep (se 1 (by rfl) ⟨439640, by rfl⟩ : syracuseStep 586187 = 879281) B879281
theorem B586199 : Blo 583288 586199 := bstep (se 1 (by rfl) ⟨439649, by rfl⟩ : syracuseStep 586199 = 879299) B879299
theorem B586219 : Blo 583288 586219 := bstep (se 1 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 586219 = 879329) B879329
theorem B586231 : Blo 583288 586231 := bstep (se 1 (by rfl) ⟨439673, by rfl⟩ : syracuseStep 586231 = 879347) B879347
theorem B586251 : Blo 583288 586251 := bstep (se 1 (by rfl) ⟨439688, by rfl⟩ : syracuseStep 586251 = 879377) B879377
theorem B586263 : Blo 583288 586263 := bstep (se 1 (by rfl) ⟨439697, by rfl⟩ : syracuseStep 586263 = 879395) B879395
theorem B586283 : Blo 583288 586283 := bstep (se 1 (by rfl) ⟨439712, by rfl⟩ : syracuseStep 586283 = 879425) B879425
theorem B586295 : Blo 583288 586295 := bstep (se 1 (by rfl) ⟨439721, by rfl⟩ : syracuseStep 586295 = 879443) B879443
theorem B586315 : Blo 583288 586315 := bstep (se 1 (by rfl) ⟨439736, by rfl⟩ : syracuseStep 586315 = 879473) B879473
theorem B586327 : Blo 583288 586327 := bstep (se 1 (by rfl) ⟨439745, by rfl⟩ : syracuseStep 586327 = 879491) B879491
theorem B586347 : Blo 583288 586347 := bstep (se 1 (by rfl) ⟨439760, by rfl⟩ : syracuseStep 586347 = 879521) B879521
theorem B586359 : Blo 583288 586359 := bstep (se 1 (by rfl) ⟨439769, by rfl⟩ : syracuseStep 586359 = 879539) B879539
theorem B586379 : Blo 583288 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B586391 : Blo 583288 586391 := bstep (se 1 (by rfl) ⟨439793, by rfl⟩ : syracuseStep 586391 = 879587) B879587
theorem B586411 : Blo 583288 586411 := bstep (se 1 (by rfl) ⟨439808, by rfl⟩ : syracuseStep 586411 = 879617) B879617
theorem B586423 : Blo 583288 586423 := bstep (se 1 (by rfl) ⟨439817, by rfl⟩ : syracuseStep 586423 = 879635) B879635
theorem B586443 : Blo 583288 586443 := bstep (se 1 (by rfl) ⟨439832, by rfl⟩ : syracuseStep 586443 = 879665) B879665
theorem B586455 : Blo 583288 586455 := bstep (se 1 (by rfl) ⟨439841, by rfl⟩ : syracuseStep 586455 = 879683) B879683
theorem B586475 : Blo 583288 586475 := bstep (se 1 (by rfl) ⟨439856, by rfl⟩ : syracuseStep 586475 = 879713) B879713
theorem B586487 : Blo 583288 586487 := bstep (se 1 (by rfl) ⟨439865, by rfl⟩ : syracuseStep 586487 = 879731) B879731
theorem B586507 : Blo 583288 586507 := bstep (se 1 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 586507 = 879761) B879761
theorem B586519 : Blo 583288 586519 := bstep (se 1 (by rfl) ⟨439889, by rfl⟩ : syracuseStep 586519 = 879779) B879779
theorem B586539 : Blo 583288 586539 := bstep (se 1 (by rfl) ⟨439904, by rfl⟩ : syracuseStep 586539 = 879809) B879809
theorem B586551 : Blo 583288 586551 := bstep (se 1 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 586551 = 879827) B879827
theorem B586571 : Blo 583288 586571 := bstep (se 1 (by rfl) ⟨439928, by rfl⟩ : syracuseStep 586571 = 879857) B879857
theorem B586583 : Blo 583288 586583 := bstep (se 1 (by rfl) ⟨439937, by rfl⟩ : syracuseStep 586583 = 879875) B879875
theorem B586603 : Blo 583288 586603 := bstep (se 1 (by rfl) ⟨439952, by rfl⟩ : syracuseStep 586603 = 879905) B879905
theorem B586615 : Blo 583288 586615 := bstep (se 1 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 586615 = 879923) B879923
theorem B4518787 : Blo 583288 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B586635 : Blo 583288 586635 := bstep (se 1 (by rfl) ⟨439976, by rfl⟩ : syracuseStep 586635 = 879953) B879953
theorem B1110935 : Blo 583288 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B586647 : Blo 583288 586647 := bstep (se 1 (by rfl) ⟨439985, by rfl⟩ : syracuseStep 586647 = 879971) B879971
theorem B586667 : Blo 583288 586667 := bstep (se 1 (by rfl) ⟨440000, by rfl⟩ : syracuseStep 586667 = 880001) B880001
theorem B586679 : Blo 583288 586679 := bstep (se 1 (by rfl) ⟨440009, by rfl⟩ : syracuseStep 586679 = 880019) B880019
theorem B1668043 : Blo 583288 1668043 := bstep (se 1 (by rfl) ⟨1251032, by rfl⟩ : syracuseStep 1668043 = 2502065) B2502065
theorem B586699 : Blo 583288 586699 := bstep (se 1 (by rfl) ⟨440024, by rfl⟩ : syracuseStep 586699 = 880049) B880049
theorem B586711 : Blo 583288 586711 := bstep (se 1 (by rfl) ⟨440033, by rfl⟩ : syracuseStep 586711 = 880067) B880067
theorem B586731 : Blo 583288 586731 := bstep (se 1 (by rfl) ⟨440048, by rfl⟩ : syracuseStep 586731 = 880097) B880097
theorem B586743 : Blo 583288 586743 := bstep (se 1 (by rfl) ⟨440057, by rfl⟩ : syracuseStep 586743 = 880115) B880115
theorem B586763 : Blo 583288 586763 := bstep (se 1 (by rfl) ⟨440072, by rfl⟩ : syracuseStep 586763 = 880145) B880145
theorem B586775 : Blo 583288 586775 := bstep (se 1 (by rfl) ⟨440081, by rfl⟩ : syracuseStep 586775 = 880163) B880163
theorem B586795 : Blo 583288 586795 := bstep (se 1 (by rfl) ⟨440096, by rfl⟩ : syracuseStep 586795 = 880193) B880193
theorem B586807 : Blo 583288 586807 := bstep (se 1 (by rfl) ⟨440105, by rfl⟩ : syracuseStep 586807 = 880211) B880211
theorem B586827 : Blo 583288 586827 := bstep (se 1 (by rfl) ⟨440120, by rfl⟩ : syracuseStep 586827 = 880241) B880241
theorem B586839 : Blo 583288 586839 := bstep (se 1 (by rfl) ⟨440129, by rfl⟩ : syracuseStep 586839 = 880259) B880259
theorem B586859 : Blo 583288 586859 := bstep (se 1 (by rfl) ⟨440144, by rfl⟩ : syracuseStep 586859 = 880289) B880289
theorem B586871 : Blo 583288 586871 := bstep (se 1 (by rfl) ⟨440153, by rfl⟩ : syracuseStep 586871 = 880307) B880307
theorem B586891 : Blo 583288 586891 := bstep (se 1 (by rfl) ⟨440168, by rfl⟩ : syracuseStep 586891 = 880337) B880337
theorem B2225303 : Blo 583288 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B586903 : Blo 583288 586903 := bstep (se 1 (by rfl) ⟨440177, by rfl⟩ : syracuseStep 586903 = 880355) B880355
theorem B586923 : Blo 583288 586923 := bstep (se 1 (by rfl) ⟨440192, by rfl⟩ : syracuseStep 586923 = 880385) B880385
theorem B586935 : Blo 583288 586935 := bstep (se 1 (by rfl) ⟨440201, by rfl⟩ : syracuseStep 586935 = 880403) B880403
theorem B586955 : Blo 583288 586955 := bstep (se 1 (by rfl) ⟨440216, by rfl⟩ : syracuseStep 586955 = 880433) B880433
theorem B586967 : Blo 583288 586967 := bstep (se 1 (by rfl) ⟨440225, by rfl⟩ : syracuseStep 586967 = 880451) B880451
theorem B586987 : Blo 583288 586987 := bstep (se 1 (by rfl) ⟨440240, by rfl⟩ : syracuseStep 586987 = 880481) B880481
theorem B586999 : Blo 583288 586999 := bstep (se 1 (by rfl) ⟨440249, by rfl⟩ : syracuseStep 586999 = 880499) B880499
theorem B587019 : Blo 583288 587019 := bstep (se 1 (by rfl) ⟨440264, by rfl⟩ : syracuseStep 587019 = 880529) B880529
theorem B587031 : Blo 583288 587031 := bstep (se 1 (by rfl) ⟨440273, by rfl⟩ : syracuseStep 587031 = 880547) B880547
theorem B587051 : Blo 583288 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B587063 : Blo 583288 587063 := bstep (se 1 (by rfl) ⟨440297, by rfl⟩ : syracuseStep 587063 = 880595) B880595
theorem B587083 : Blo 583288 587083 := bstep (se 1 (by rfl) ⟨440312, by rfl⟩ : syracuseStep 587083 = 880625) B880625
theorem B587095 : Blo 583288 587095 := bstep (se 1 (by rfl) ⟨440321, by rfl⟩ : syracuseStep 587095 = 880643) B880643
theorem B2225501 : Blo 583288 2225501 := bstep (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) B834563
theorem B587115 : Blo 583288 587115 := bstep (se 1 (by rfl) ⟨440336, by rfl⟩ : syracuseStep 587115 = 880673) B880673
theorem B587127 : Blo 583288 587127 := bstep (se 1 (by rfl) ⟨440345, by rfl⟩ : syracuseStep 587127 = 880691) B880691
theorem B587147 : Blo 583288 587147 := bstep (se 1 (by rfl) ⟨440360, by rfl⟩ : syracuseStep 587147 = 880721) B880721
theorem B587159 : Blo 583288 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B587179 : Blo 583288 587179 := bstep (se 1 (by rfl) ⟨440384, by rfl⟩ : syracuseStep 587179 = 880769) B880769
theorem B1111475 : Blo 583288 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B587191 : Blo 583288 587191 := bstep (se 1 (by rfl) ⟨440393, by rfl⟩ : syracuseStep 587191 = 880787) B880787
theorem B1668545 : Blo 583288 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B587211 : Blo 583288 587211 := bstep (se 1 (by rfl) ⟨440408, by rfl⟩ : syracuseStep 587211 = 880817) B880817
theorem B587223 : Blo 583288 587223 := bstep (se 1 (by rfl) ⟨440417, by rfl⟩ : syracuseStep 587223 = 880835) B880835
theorem B587243 : Blo 583288 587243 := bstep (se 1 (by rfl) ⟨440432, by rfl⟩ : syracuseStep 587243 = 880865) B880865
theorem B587255 : Blo 583288 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B587275 : Blo 583288 587275 := bstep (se 1 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 587275 = 880913) B880913
theorem B587287 : Blo 583288 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B3995237 : Blo 583288 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B1668887 : Blo 583288 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B4454189 : Blo 583288 4454189 := bstep (se 3 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 4454189 = 1670321) B1670321
theorem B1111961 : Blo 583288 1111961 := bstep (se 2 (by rfl) ⟨416985, by rfl⟩ : syracuseStep 1111961 = 833971) B833971
theorem B3340439 : Blo 583288 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B2881885 : Blo 583288 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B2030359 : Blo 583288 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B4815877 : Blo 583288 4815877 := bstep (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) B902977
theorem B2227459 : Blo 583288 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B3374401 : Blo 583288 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B1113419 : Blo 583288 1113419 := bstep (se 1 (by rfl) ⟨835064, by rfl⟩ : syracuseStep 1113419 = 1670129) B1670129
theorem B3571075 : Blo 583288 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B1113601 : Blo 583288 1113601 := bstep (se 2 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 1113601 = 835201) B835201
theorem B8453645 : Blo 583288 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B2227763 : Blo 583288 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B1671005 : Blo 583288 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B40468403 : Blo 583288 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B1114049 : Blo 583288 1114049 := bstep (se 2 (by rfl) ⟨417768, by rfl⟩ : syracuseStep 1114049 = 835537) B835537
theorem B1114231 : Blo 583288 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B2162945 : Blo 583288 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B9994589 : Blo 583288 9994589 := bstep (se 3 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 9994589 = 3747971) B3747971
theorem B54887381 : Blo 583288 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B1246241 : Blo 583288 1246241 := bstep (se 2 (by rfl) ⟨467340, by rfl⟩ : syracuseStep 1246241 = 934681) B934681
theorem B1672235 : Blo 583288 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B656527 : Blo 583288 656527 := bstep (se 1 (by rfl) ⟨492395, by rfl⟩ : syracuseStep 656527 = 984791) B984791
theorem B984379 : Blo 583288 984379 := bstep (se 1 (by rfl) ⟨738284, by rfl⟩ : syracuseStep 984379 = 1476569) B1476569
theorem B1246583 : Blo 583288 1246583 := bstep (se 1 (by rfl) ⟨934937, by rfl⟩ : syracuseStep 1246583 = 1869875) B1869875
theorem B984521 : Blo 583288 984521 := bstep (se 2 (by rfl) ⟨369195, by rfl⟩ : syracuseStep 984521 = 738391) B738391
theorem B657031 : Blo 583288 657031 := bstep (se 1 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 657031 = 985547) B985547
theorem B6686387 : Blo 583288 6686387 := bstep (se 1 (by rfl) ⟨5014790, by rfl⟩ : syracuseStep 6686387 = 10029581) B10029581
theorem B1247035 : Blo 583288 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B657211 : Blo 583288 657211 := bstep (se 1 (by rfl) ⟨492908, by rfl⟩ : syracuseStep 657211 = 985817) B985817
theorem B6752089 : Blo 583288 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B1312631 : Blo 583288 1312631 := bstep (se 1 (by rfl) ⟨984473, by rfl⟩ : syracuseStep 1312631 = 1968947) B1968947
theorem B1312811 : Blo 583288 1312811 := bstep (se 1 (by rfl) ⟨984608, by rfl⟩ : syracuseStep 1312811 = 1969217) B1969217
theorem B985223 : Blo 583288 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B657679 : Blo 583288 657679 := bstep (se 1 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 657679 = 986519) B986519
theorem B1313171 : Blo 583288 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B1313225 : Blo 583288 1313225 := bstep (se 2 (by rfl) ⟨492459, by rfl⟩ : syracuseStep 1313225 = 984919) B984919
theorem B788983 : Blo 583288 788983 := bstep (se 1 (by rfl) ⟨591737, by rfl⟩ : syracuseStep 788983 = 1183475) B1183475
theorem B788999 : Blo 583288 788999 := bstep (se 1 (by rfl) ⟨591749, by rfl⟩ : syracuseStep 788999 = 1183499) B1183499
theorem B1051321 : Blo 583288 1051321 := bstep (se 2 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 1051321 = 788491) B788491
theorem B658183 : Blo 583288 658183 := bstep (se 1 (by rfl) ⟨493637, by rfl⟩ : syracuseStep 658183 = 987275) B987275
theorem B985871 : Blo 583288 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B1248043 : Blo 583288 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B1477511 : Blo 583288 1477511 := bstep (se 1 (by rfl) ⟨1108133, by rfl⟩ : syracuseStep 1477511 = 2216267) B2216267
theorem B1477561 : Blo 583288 1477561 := bstep (se 2 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 1477561 = 1108171) B1108171
theorem B658363 : Blo 583288 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B1969163 : Blo 583288 1969163 := bstep (se 1 (by rfl) ⟨1476872, by rfl⟩ : syracuseStep 1969163 = 2953745) B2953745
theorem B1248299 : Blo 583288 1248299 := bstep (se 1 (by rfl) ⟨936224, by rfl⟩ : syracuseStep 1248299 = 1872449) B1872449
theorem B1969271 : Blo 583288 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B1313927 : Blo 583288 1313927 := bstep (se 1 (by rfl) ⟨985445, by rfl⟩ : syracuseStep 1313927 = 1970891) B1970891
theorem B625807 : Blo 583288 625807 := bstep (se 1 (by rfl) ⟨469355, by rfl⟩ : syracuseStep 625807 = 938711) B938711
theorem B2821321 : Blo 583288 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B986411 : Blo 583288 986411 := bstep (se 1 (by rfl) ⟨739808, by rfl⟩ : syracuseStep 986411 = 1479617) B1479617
theorem B1314107 : Blo 583288 1314107 := bstep (se 1 (by rfl) ⟨985580, by rfl⟩ : syracuseStep 1314107 = 1971161) B1971161
theorem B658831 : Blo 583288 658831 := bstep (se 1 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 658831 = 988247) B988247
theorem B626063 : Blo 583288 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B1314233 : Blo 583288 1314233 := bstep (se 2 (by rfl) ⟨492837, by rfl⟩ : syracuseStep 1314233 = 985675) B985675
theorem B20254157 : Blo 583288 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B1478159 : Blo 583288 1478159 := bstep (se 1 (by rfl) ⟨1108619, by rfl⟩ : syracuseStep 1478159 = 2217239) B2217239
theorem B986809 : Blo 583288 986809 := bstep (se 2 (by rfl) ⟨370053, by rfl⟩ : syracuseStep 986809 = 740107) B740107
theorem B1969865 : Blo 583288 1969865 := bstep (se 2 (by rfl) ⟨738699, by rfl⟩ : syracuseStep 1969865 = 1477399) B1477399
theorem B1314575 : Blo 583288 1314575 := bstep (se 1 (by rfl) ⟨985931, by rfl⟩ : syracuseStep 1314575 = 1971863) B1971863
theorem B1314593 : Blo 583288 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B1183547 : Blo 583288 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B659335 : Blo 583288 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B7606219 : Blo 583288 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B1576961 : Blo 583288 1576961 := bstep (se 2 (by rfl) ⟨591360, by rfl⟩ : syracuseStep 1576961 = 1182721) B1182721
theorem B1052705 : Blo 583288 1052705 := bstep (se 2 (by rfl) ⟨394764, by rfl⟩ : syracuseStep 1052705 = 789529) B789529
theorem B2953259 : Blo 583288 2953259 := bstep (se 1 (by rfl) ⟨2214944, by rfl⟩ : syracuseStep 2953259 = 4429889) B4429889
theorem B659515 : Blo 583288 659515 := bstep (se 1 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 659515 = 989273) B989273
theorem B2494583 : Blo 583288 2494583 := bstep (se 1 (by rfl) ⟨1870937, by rfl⟩ : syracuseStep 2494583 = 3741875) B3741875
theorem B1314935 : Blo 583288 1314935 := bstep (se 1 (by rfl) ⟨986201, by rfl⟩ : syracuseStep 1314935 = 1972403) B1972403
theorem B1249427 : Blo 583288 1249427 := bstep (se 1 (by rfl) ⟨937070, by rfl⟩ : syracuseStep 1249427 = 1874141) B1874141
theorem B1478857 : Blo 583288 1478857 := bstep (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) B1109143
theorem B1315115 : Blo 583288 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B1478999 : Blo 583288 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B987511 : Blo 583288 987511 := bstep (se 1 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 987511 = 1481267) B1481267
theorem B1970567 : Blo 583288 1970567 := bstep (se 1 (by rfl) ⟨1477925, by rfl⟩ : syracuseStep 1970567 = 2955851) B2955851
theorem B659983 : Blo 583288 659983 := bstep (se 1 (by rfl) ⟨494987, by rfl⟩ : syracuseStep 659983 = 989975) B989975
theorem B987707 : Blo 583288 987707 := bstep (se 1 (by rfl) ⟨740780, by rfl⟩ : syracuseStep 987707 = 1481561) B1481561
theorem B1806967 : Blo 583288 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B1315475 : Blo 583288 1315475 := bstep (se 1 (by rfl) ⟨986606, by rfl⟩ : syracuseStep 1315475 = 1973213) B1973213
theorem B1249939 : Blo 583288 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1315529 : Blo 583288 1315529 := bstep (se 2 (by rfl) ⟨493323, by rfl⟩ : syracuseStep 1315529 = 986647) B986647
theorem B1970945 : Blo 583288 1970945 := bstep (se 2 (by rfl) ⟨739104, by rfl⟩ : syracuseStep 1970945 = 1478209) B1478209
theorem B1053499 : Blo 583288 1053499 := bstep (se 1 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 1053499 = 1580249) B1580249
theorem B988105 : Blo 583288 988105 := bstep (se 2 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 988105 = 741079) B741079
theorem B660487 : Blo 583288 660487 := bstep (se 1 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 660487 = 990731) B990731
theorem B660667 : Blo 583288 660667 := bstep (se 1 (by rfl) ⟨495500, by rfl⟩ : syracuseStep 660667 = 991001) B991001
theorem B2954555 : Blo 583288 2954555 := bstep (se 1 (by rfl) ⟨2215916, by rfl⟩ : syracuseStep 2954555 = 4431833) B4431833
theorem B1316231 : Blo 583288 1316231 := bstep (se 1 (by rfl) ⟨987173, by rfl⟩ : syracuseStep 1316231 = 1974347) B1974347
theorem B2954717 : Blo 583288 2954717 := bstep (se 3 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 2954717 = 1108019) B1108019
theorem B1971755 : Blo 583288 1971755 := bstep (se 1 (by rfl) ⟨1478816, by rfl⟩ : syracuseStep 1971755 = 2957633) B2957633
theorem B1316411 : Blo 583288 1316411 := bstep (se 1 (by rfl) ⟨987308, by rfl⟩ : syracuseStep 1316411 = 1974617) B1974617
theorem B988807 : Blo 583288 988807 := bstep (se 1 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 988807 = 1483211) B1483211
theorem B1316537 : Blo 583288 1316537 := bstep (se 2 (by rfl) ⟨493701, by rfl⟩ : syracuseStep 1316537 = 987403) B987403
theorem B2496257 : Blo 583288 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B2955041 : Blo 583288 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B1316879 : Blo 583288 1316879 := bstep (se 1 (by rfl) ⟨987659, by rfl⟩ : syracuseStep 1316879 = 1975319) B1975319
theorem B1316897 : Blo 583288 1316897 := bstep (se 2 (by rfl) ⟨493836, by rfl⟩ : syracuseStep 1316897 = 987673) B987673
theorem B1185835 : Blo 583288 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B1054867 : Blo 583288 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B5347565 : Blo 583288 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B1874191 : Blo 583288 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B989455 : Blo 583288 989455 := bstep (se 1 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 989455 = 1484183) B1484183
theorem B1579351 : Blo 583288 1579351 := bstep (se 1 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 1579351 = 2369027) B2369027
theorem B1481075 : Blo 583288 1481075 := bstep (se 1 (by rfl) ⟨1110806, by rfl⟩ : syracuseStep 1481075 = 2221613) B2221613
theorem B1317239 : Blo 583288 1317239 := bstep (se 1 (by rfl) ⟨987929, by rfl⟩ : syracuseStep 1317239 = 1975859) B1975859
theorem B1317419 : Blo 583288 1317419 := bstep (se 1 (by rfl) ⟨988064, by rfl⟩ : syracuseStep 1317419 = 1976129) B1976129
theorem B1808939 : Blo 583288 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B9476675 : Blo 583288 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B9968345 : Blo 583288 9968345 := bstep (se 2 (by rfl) ⟨3738129, by rfl⟩ : syracuseStep 9968345 = 7476259) B7476259
theorem B2956013 : Blo 583288 2956013 := bstep (se 3 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 2956013 = 1108505) B1108505
theorem B10033955 : Blo 583288 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B989995 : Blo 583288 989995 := bstep (se 1 (by rfl) ⟨742496, by rfl⟩ : syracuseStep 989995 = 1484993) B1484993
theorem B1973051 : Blo 583288 1973051 := bstep (se 1 (by rfl) ⟨1479788, by rfl⟩ : syracuseStep 1973051 = 2959577) B2959577
theorem B1481591 : Blo 583288 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1317779 : Blo 583288 1317779 := bstep (se 1 (by rfl) ⟨988334, by rfl⟩ : syracuseStep 1317779 = 1976669) B1976669
theorem B990137 : Blo 583288 990137 := bstep (se 2 (by rfl) ⟨371301, by rfl⟩ : syracuseStep 990137 = 742603) B742603
theorem B1317833 : Blo 583288 1317833 := bstep (se 2 (by rfl) ⟨494187, by rfl⟩ : syracuseStep 1317833 = 988375) B988375
theorem B1252297 : Blo 583288 1252297 := bstep (se 2 (by rfl) ⟨469611, by rfl⟩ : syracuseStep 1252297 = 939223) B939223
theorem B17538053 : Blo 583288 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B1973537 : Blo 583288 1973537 := bstep (se 2 (by rfl) ⟨740076, by rfl⟩ : syracuseStep 1973537 = 1480153) B1480153
theorem B6495623 : Blo 583288 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B2956823 : Blo 583288 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B1875575 : Blo 583288 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B990839 : Blo 583288 990839 := bstep (se 1 (by rfl) ⟨743129, by rfl⟩ : syracuseStep 990839 = 1486259) B1486259
theorem B1318535 : Blo 583288 1318535 := bstep (se 1 (by rfl) ⟨988901, by rfl⟩ : syracuseStep 1318535 = 1977803) B1977803
theorem B1318715 : Blo 583288 1318715 := bstep (se 1 (by rfl) ⟨989036, by rfl⟩ : syracuseStep 1318715 = 1978073) B1978073
theorem B1482583 : Blo 583288 1482583 := bstep (se 1 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 1482583 = 2223875) B2223875
theorem B1974131 : Blo 583288 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B1318841 : Blo 583288 1318841 := bstep (se 2 (by rfl) ⟨494565, by rfl⟩ : syracuseStep 1318841 = 989131) B989131
theorem B2105297 : Blo 583288 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B761899 : Blo 583288 761899 := bstep (se 1 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 761899 = 1142849) B1142849
theorem B1187959 : Blo 583288 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B1482887 : Blo 583288 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B1253561 : Blo 583288 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B1483019 : Blo 583288 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B1319183 : Blo 583288 1319183 := bstep (se 1 (by rfl) ⟨989387, by rfl⟩ : syracuseStep 1319183 = 1978775) B1978775
theorem B1253647 : Blo 583288 1253647 := bstep (se 1 (by rfl) ⟨940235, by rfl⟩ : syracuseStep 1253647 = 1880471) B1880471
theorem B1319201 : Blo 583288 1319201 := bstep (se 2 (by rfl) ⟨494700, by rfl⟩ : syracuseStep 1319201 = 989401) B989401
theorem B1122761 : Blo 583288 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B3842513 : Blo 583288 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B1319543 : Blo 583288 1319543 := bstep (se 1 (by rfl) ⟨989657, by rfl⟩ : syracuseStep 1319543 = 1979315) B1979315
theorem B1483535 : Blo 583288 1483535 := bstep (se 1 (by rfl) ⟨1112651, by rfl⟩ : syracuseStep 1483535 = 2225303) B2225303
theorem B1319723 : Blo 583288 1319723 := bstep (se 1 (by rfl) ⟨989792, by rfl⟩ : syracuseStep 1319723 = 1979585) B1979585
theorem B1483667 : Blo 583288 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B2663491 : Blo 583288 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B7611479 : Blo 583288 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1320083 : Blo 583288 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B1320137 : Blo 583288 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B2107081 : Blo 583288 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B4499201 : Blo 583288 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B4761433 : Blo 583288 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B1320839 : Blo 583288 1320839 := bstep (se 1 (by rfl) ⟨990629, by rfl⟩ : syracuseStep 1320839 = 1981259) B1981259
theorem B2500561 : Blo 583288 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1484801 : Blo 583288 1484801 := bstep (se 2 (by rfl) ⟨556800, by rfl⟩ : syracuseStep 1484801 = 1113601) B1113601
theorem B1321019 : Blo 583288 1321019 := bstep (se 1 (by rfl) ⟨990764, by rfl⟩ : syracuseStep 1321019 = 1981529) B1981529
theorem B1321145 : Blo 583288 1321145 := bstep (se 2 (by rfl) ⟨495429, by rfl⟩ : syracuseStep 1321145 = 990859) B990859
theorem B1485175 : Blo 583288 1485175 := bstep (se 1 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 1485175 = 2227763) B2227763
theorem B1976723 : Blo 583288 1976723 := bstep (se 1 (by rfl) ⟨1482542, by rfl⟩ : syracuseStep 1976723 = 2965085) B2965085
theorem B2959901 : Blo 583288 2959901 := bstep (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) B1109963
theorem B26978935 : Blo 583288 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B1780481 : Blo 583288 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B1485611 : Blo 583288 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B2960387 : Blo 583288 2960387 := bstep (se 1 (by rfl) ⟨2220290, by rfl⟩ : syracuseStep 2960387 = 4440581) B4440581
theorem B830855 : Blo 583288 830855 := bstep (se 1 (by rfl) ⟨623141, by rfl⟩ : syracuseStep 830855 = 1246283) B1246283
theorem B14233117 : Blo 583288 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B1486451 : Blo 583288 1486451 := bstep (se 1 (by rfl) ⟨1114838, by rfl⟩ : syracuseStep 1486451 = 2229677) B2229677
theorem B1486471 : Blo 583288 1486471 := bstep (se 1 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 1486471 = 2229707) B2229707
theorem B831163 : Blo 583288 831163 := bstep (se 1 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 831163 = 1246745) B1246745
theorem B1978127 : Blo 583288 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B2666375 : Blo 583288 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B2109331 : Blo 583288 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B1978397 : Blo 583288 1978397 := bstep (se 3 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 1978397 = 741899) B741899
theorem B26980397 : Blo 583288 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B22556717 : Blo 583288 22556717 := bstep (se 3 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 22556717 = 8458769) B8458769
theorem B3256613 : Blo 583288 3256613 := bstep (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) B610615
theorem B2470297 : Blo 583288 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B3387869 : Blo 583288 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B2109995 : Blo 583288 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B700987 : Blo 583288 700987 := bstep (se 1 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 700987 = 1051481) B1051481
theorem B2962007 : Blo 583288 2962007 := bstep (se 1 (by rfl) ⟨2221505, by rfl⟩ : syracuseStep 2962007 = 4443011) B4443011
theorem B1782425 : Blo 583288 1782425 := bstep (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) B1336819
theorem B832313 : Blo 583288 832313 := bstep (se 2 (by rfl) ⟨312117, by rfl⟩ : syracuseStep 832313 = 624235) B624235
theorem B2962493 : Blo 583288 2962493 := bstep (se 3 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 2962493 = 1110935) B1110935
theorem B1979801 : Blo 583288 1979801 := bstep (se 2 (by rfl) ⟨742425, by rfl⟩ : syracuseStep 1979801 = 1484851) B1484851
theorem B6108739 : Blo 583288 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B20592305 : Blo 583288 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B2111177 : Blo 583288 2111177 := bstep (se 2 (by rfl) ⟨791691, by rfl⟩ : syracuseStep 2111177 = 1583383) B1583383
theorem B1587059 : Blo 583288 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B1980503 : Blo 583288 1980503 := bstep (se 1 (by rfl) ⟨1485377, by rfl⟩ : syracuseStep 1980503 = 2970755) B2970755
theorem B833851 : Blo 583288 833851 := bstep (se 1 (by rfl) ⟨625388, by rfl⟩ : syracuseStep 833851 = 1250777) B1250777
theorem B2505107 : Blo 583288 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B1980989 : Blo 583288 1980989 := bstep (se 3 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 1980989 = 742871) B742871
theorem B834295 : Blo 583288 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B3160883 : Blo 583288 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B2964275 : Blo 583288 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1784663 : Blo 583288 1784663 := bstep (se 1 (by rfl) ⟨1338497, by rfl⟩ : syracuseStep 1784663 = 2676995) B2676995
theorem B703495 : Blo 583288 703495 := bstep (se 1 (by rfl) ⟨527621, by rfl⟩ : syracuseStep 703495 = 1055243) B1055243
theorem B9616445 : Blo 583288 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B2964599 : Blo 583288 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B3554705 : Blo 583288 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B835115 : Blo 583288 835115 := bstep (se 1 (by rfl) ⟨626336, by rfl⟩ : syracuseStep 835115 = 1252673) B1252673
theorem B24035123 : Blo 583288 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B10665931 : Blo 583288 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B6340619 : Blo 583288 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B2506781 : Blo 583288 2506781 := bstep (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) B940043
theorem B2965571 : Blo 583288 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B2965895 : Blo 583288 2965895 := bstep (se 1 (by rfl) ⟨2224421, by rfl⟩ : syracuseStep 2965895 = 4448843) B4448843
theorem B2670995 : Blo 583288 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B4735745 : Blo 583288 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B2507705 : Blo 583288 2507705 := bstep (se 2 (by rfl) ⟨940389, by rfl⟩ : syracuseStep 2507705 = 1880779) B1880779
theorem B3163481 : Blo 583288 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B3556723 : Blo 583288 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B4441553 : Blo 583288 4441553 := bstep (se 2 (by rfl) ⟨1665582, by rfl⟩ : syracuseStep 4441553 = 3331165) B3331165
theorem B3556867 : Blo 583288 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B3163735 : Blo 583288 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B935609 : Blo 583288 935609 := bstep (se 2 (by rfl) ⟨350853, by rfl⟩ : syracuseStep 935609 = 701707) B701707
theorem B6342437 : Blo 583288 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B1689601 : Blo 583288 1689601 := bstep (se 2 (by rfl) ⟨633600, by rfl⟩ : syracuseStep 1689601 = 1267201) B1267201
theorem B3328067 : Blo 583288 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B3557549 : Blo 583288 3557549 := bstep (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) B1334081
theorem B3328523 : Blo 583288 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B740011 : Blo 583288 740011 := bstep (se 1 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 740011 = 1110017) B1110017
theorem B1526647 : Blo 583288 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B2214809 : Blo 583288 2214809 := bstep (se 2 (by rfl) ⟨830553, by rfl⟩ : syracuseStep 2214809 = 1661107) B1661107
theorem B2805137 : Blo 583288 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B2674073 : Blo 583288 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B2248121 : Blo 583288 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B2805367 : Blo 583288 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B740983 : Blo 583288 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B937673 : Blo 583288 937673 := bstep (se 2 (by rfl) ⟨351627, by rfl⟩ : syracuseStep 937673 = 703255) B703255
theorem B2707145 : Blo 583288 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B2215795 : Blo 583288 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B2969459 : Blo 583288 2969459 := bstep (se 1 (by rfl) ⟨2227094, by rfl⟩ : syracuseStep 2969459 = 4454189) B4454189
theorem B741307 : Blo 583288 741307 := bstep (se 1 (by rfl) ⟨555980, by rfl⟩ : syracuseStep 741307 = 1111961) B1111961
theorem B2969945 : Blo 583288 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B3559889 : Blo 583288 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B742279 : Blo 583288 742279 := bstep (se 1 (by rfl) ⟨556709, by rfl⟩ : syracuseStep 742279 = 1113419) B1113419
theorem B742699 : Blo 583288 742699 := bstep (se 1 (by rfl) ⟨557024, by rfl⟩ : syracuseStep 742699 = 1114049) B1114049
theorem B742927 : Blo 583288 742927 := bstep (se 1 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 742927 = 1114391) B1114391
theorem B2676539 : Blo 583288 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B2218013 : Blo 583288 2218013 := bstep (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) B831755
theorem B2250989 : Blo 583288 2250989 := bstep (se 3 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 2250989 = 844121) B844121
theorem B3332441 : Blo 583288 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B6347153 : Blo 583288 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B2808211 : Blo 583288 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B2677139 : Blo 583288 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B2972051 : Blo 583288 2972051 := bstep (se 1 (by rfl) ⟨2229038, by rfl⟩ : syracuseStep 2972051 = 4458077) B4458077
theorem B874937 : Blo 583288 874937 := bstep (se 2 (by rfl) ⟨328101, by rfl⟩ : syracuseStep 874937 = 656203) B656203
theorem B5986781 : Blo 583288 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B875015 : Blo 583288 875015 := bstep (se 1 (by rfl) ⟨656261, by rfl⟩ : syracuseStep 875015 = 1312523) B1312523
theorem B875051 : Blo 583288 875051 := bstep (se 1 (by rfl) ⟨656288, by rfl⟩ : syracuseStep 875051 = 1312577) B1312577
theorem B875081 : Blo 583288 875081 := bstep (se 2 (by rfl) ⟨328155, by rfl⟩ : syracuseStep 875081 = 656311) B656311
theorem B875195 : Blo 583288 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B2218697 : Blo 583288 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B875255 : Blo 583288 875255 := bstep (se 1 (by rfl) ⟨656441, by rfl⟩ : syracuseStep 875255 = 1312883) B1312883
theorem B875279 : Blo 583288 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B3332897 : Blo 583288 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B875321 : Blo 583288 875321 := bstep (se 2 (by rfl) ⟨328245, by rfl⟩ : syracuseStep 875321 = 656491) B656491
theorem B875399 : Blo 583288 875399 := bstep (se 1 (by rfl) ⟨656549, by rfl⟩ : syracuseStep 875399 = 1313099) B1313099
theorem B1498009 : Blo 583288 1498009 := bstep (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) B1123507
theorem B875435 : Blo 583288 875435 := bstep (se 1 (by rfl) ⟨656576, by rfl⟩ : syracuseStep 875435 = 1313153) B1313153
theorem B875465 : Blo 583288 875465 := bstep (se 2 (by rfl) ⟨328299, by rfl⟩ : syracuseStep 875465 = 656599) B656599
theorem B3333149 : Blo 583288 3333149 := bstep (se 3 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 3333149 = 1249931) B1249931
theorem B875579 : Blo 583288 875579 := bstep (se 1 (by rfl) ⟨656684, by rfl⟩ : syracuseStep 875579 = 1313369) B1313369
theorem B875639 : Blo 583288 875639 := bstep (se 1 (by rfl) ⟨656729, by rfl⟩ : syracuseStep 875639 = 1313459) B1313459
theorem B875663 : Blo 583288 875663 := bstep (se 1 (by rfl) ⟨656747, by rfl⟩ : syracuseStep 875663 = 1313495) B1313495
theorem B875705 : Blo 583288 875705 := bstep (se 2 (by rfl) ⟨328389, by rfl⟩ : syracuseStep 875705 = 656779) B656779
theorem B875783 : Blo 583288 875783 := bstep (se 1 (by rfl) ⟨656837, by rfl⟩ : syracuseStep 875783 = 1313675) B1313675
theorem B875819 : Blo 583288 875819 := bstep (se 1 (by rfl) ⟨656864, by rfl⟩ : syracuseStep 875819 = 1313729) B1313729
theorem B875849 : Blo 583288 875849 := bstep (se 2 (by rfl) ⟨328443, by rfl⟩ : syracuseStep 875849 = 656887) B656887
theorem B875963 : Blo 583288 875963 := bstep (se 1 (by rfl) ⟨656972, by rfl⟩ : syracuseStep 875963 = 1313945) B1313945
theorem B876023 : Blo 583288 876023 := bstep (se 1 (by rfl) ⟨657017, by rfl⟩ : syracuseStep 876023 = 1314035) B1314035
theorem B876047 : Blo 583288 876047 := bstep (se 1 (by rfl) ⟨657035, by rfl⟩ : syracuseStep 876047 = 1314071) B1314071
theorem B3759659 : Blo 583288 3759659 := bstep (se 1 (by rfl) ⟨2819744, by rfl⟩ : syracuseStep 3759659 = 5639489) B5639489
theorem B876089 : Blo 583288 876089 := bstep (se 2 (by rfl) ⟨328533, by rfl⟩ : syracuseStep 876089 = 657067) B657067
theorem B3202679 : Blo 583288 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1662599 : Blo 583288 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B876167 : Blo 583288 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B876203 : Blo 583288 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B876233 : Blo 583288 876233 := bstep (se 2 (by rfl) ⟨328587, by rfl⟩ : syracuseStep 876233 = 657175) B657175
theorem B9985841 : Blo 583288 9985841 := bstep (se 2 (by rfl) ⟨3744690, by rfl⟩ : syracuseStep 9985841 = 7489381) B7489381
theorem B876347 : Blo 583288 876347 := bstep (se 1 (by rfl) ⟨657260, by rfl⟩ : syracuseStep 876347 = 1314521) B1314521
theorem B1662781 : Blo 583288 1662781 := bstep (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) B623543
theorem B3170137 : Blo 583288 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1662839 : Blo 583288 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B876407 : Blo 583288 876407 := bstep (se 1 (by rfl) ⟨657305, by rfl⟩ : syracuseStep 876407 = 1314611) B1314611
theorem B876431 : Blo 583288 876431 := bstep (se 1 (by rfl) ⟨657323, by rfl⟩ : syracuseStep 876431 = 1314647) B1314647
theorem B876473 : Blo 583288 876473 := bstep (se 2 (by rfl) ⟨328677, by rfl⟩ : syracuseStep 876473 = 657355) B657355
theorem B876551 : Blo 583288 876551 := bstep (se 1 (by rfl) ⟨657413, by rfl⟩ : syracuseStep 876551 = 1314827) B1314827
theorem B2809885 : Blo 583288 2809885 := bstep (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) B1053707
theorem B876587 : Blo 583288 876587 := bstep (se 1 (by rfl) ⟨657440, by rfl⟩ : syracuseStep 876587 = 1314881) B1314881
theorem B876617 : Blo 583288 876617 := bstep (se 2 (by rfl) ⟨328731, by rfl⟩ : syracuseStep 876617 = 657463) B657463
theorem B876731 : Blo 583288 876731 := bstep (se 1 (by rfl) ⟨657548, by rfl⟩ : syracuseStep 876731 = 1315097) B1315097
theorem B876791 : Blo 583288 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B3563777 : Blo 583288 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B876815 : Blo 583288 876815 := bstep (se 1 (by rfl) ⟨657611, by rfl⟩ : syracuseStep 876815 = 1315223) B1315223
theorem B876857 : Blo 583288 876857 := bstep (se 2 (by rfl) ⟨328821, by rfl⟩ : syracuseStep 876857 = 657643) B657643
theorem B876935 : Blo 583288 876935 := bstep (se 1 (by rfl) ⟨657701, by rfl⟩ : syracuseStep 876935 = 1315403) B1315403
theorem B876971 : Blo 583288 876971 := bstep (se 1 (by rfl) ⟨657728, by rfl⟩ : syracuseStep 876971 = 1315457) B1315457
theorem B2220473 : Blo 583288 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B877001 : Blo 583288 877001 := bstep (se 2 (by rfl) ⟨328875, by rfl⟩ : syracuseStep 877001 = 657751) B657751
theorem B877115 : Blo 583288 877115 := bstep (se 1 (by rfl) ⟨657836, by rfl⟩ : syracuseStep 877115 = 1315673) B1315673
theorem B877175 : Blo 583288 877175 := bstep (se 1 (by rfl) ⟨657881, by rfl⟩ : syracuseStep 877175 = 1315763) B1315763
theorem B877199 : Blo 583288 877199 := bstep (se 1 (by rfl) ⟨657899, by rfl⟩ : syracuseStep 877199 = 1315799) B1315799
theorem B877241 : Blo 583288 877241 := bstep (se 2 (by rfl) ⟨328965, by rfl⟩ : syracuseStep 877241 = 657931) B657931
theorem B877319 : Blo 583288 877319 := bstep (se 1 (by rfl) ⟨657989, by rfl⟩ : syracuseStep 877319 = 1315979) B1315979
theorem B877355 : Blo 583288 877355 := bstep (se 1 (by rfl) ⟨658016, by rfl⟩ : syracuseStep 877355 = 1316033) B1316033
theorem B877385 : Blo 583288 877385 := bstep (se 2 (by rfl) ⟨329019, by rfl⟩ : syracuseStep 877385 = 658039) B658039
theorem B1663897 : Blo 583288 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B877499 : Blo 583288 877499 := bstep (se 1 (by rfl) ⟨658124, by rfl⟩ : syracuseStep 877499 = 1316249) B1316249
theorem B877559 : Blo 583288 877559 := bstep (se 1 (by rfl) ⟨658169, by rfl⟩ : syracuseStep 877559 = 1316339) B1316339
theorem B877583 : Blo 583288 877583 := bstep (se 1 (by rfl) ⟨658187, by rfl⟩ : syracuseStep 877583 = 1316375) B1316375
theorem B844843 : Blo 583288 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B877625 : Blo 583288 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B877703 : Blo 583288 877703 := bstep (se 1 (by rfl) ⟨658277, by rfl⟩ : syracuseStep 877703 = 1316555) B1316555
theorem B877739 : Blo 583288 877739 := bstep (se 1 (by rfl) ⟨658304, by rfl⟩ : syracuseStep 877739 = 1316609) B1316609
theorem B877769 : Blo 583288 877769 := bstep (se 2 (by rfl) ⟨329163, by rfl⟩ : syracuseStep 877769 = 658327) B658327
theorem B877883 : Blo 583288 877883 := bstep (se 1 (by rfl) ⟨658412, by rfl⟩ : syracuseStep 877883 = 1316825) B1316825
theorem B3335539 : Blo 583288 3335539 := bstep (se 1 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 3335539 = 5003309) B5003309
theorem B877943 : Blo 583288 877943 := bstep (se 1 (by rfl) ⟨658457, by rfl⟩ : syracuseStep 877943 = 1316915) B1316915
theorem B877967 : Blo 583288 877967 := bstep (se 1 (by rfl) ⟨658475, by rfl⟩ : syracuseStep 877967 = 1316951) B1316951
theorem B878009 : Blo 583288 878009 := bstep (se 2 (by rfl) ⟨329253, by rfl⟩ : syracuseStep 878009 = 658507) B658507
theorem B1664513 : Blo 583288 1664513 := bstep (se 2 (by rfl) ⟨624192, by rfl⟩ : syracuseStep 1664513 = 1248385) B1248385
theorem B878087 : Blo 583288 878087 := bstep (se 1 (by rfl) ⟨658565, by rfl⟩ : syracuseStep 878087 = 1317131) B1317131
theorem B3171869 : Blo 583288 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B878123 : Blo 583288 878123 := bstep (se 1 (by rfl) ⟨658592, by rfl⟩ : syracuseStep 878123 = 1317185) B1317185
theorem B878153 : Blo 583288 878153 := bstep (se 2 (by rfl) ⟨329307, by rfl⟩ : syracuseStep 878153 = 658615) B658615
theorem B583303 : Blo 583288 583303 := bstep (se 1 (by rfl) ⟨437477, by rfl⟩ : syracuseStep 583303 = 874955) B874955
theorem B583311 : Blo 583288 583311 := bstep (se 1 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 583311 = 874967) B874967
theorem B583355 : Blo 583288 583355 := bstep (se 1 (by rfl) ⟨437516, by rfl⟩ : syracuseStep 583355 = 875033) B875033
theorem B878267 : Blo 583288 878267 := bstep (se 1 (by rfl) ⟨658700, by rfl⟩ : syracuseStep 878267 = 1317401) B1317401
theorem B878327 : Blo 583288 878327 := bstep (se 1 (by rfl) ⟨658745, by rfl⟩ : syracuseStep 878327 = 1317491) B1317491
theorem B583431 : Blo 583288 583431 := bstep (se 1 (by rfl) ⟨437573, by rfl⟩ : syracuseStep 583431 = 875147) B875147
theorem B583439 : Blo 583288 583439 := bstep (se 1 (by rfl) ⟨437579, by rfl⟩ : syracuseStep 583439 = 875159) B875159
theorem B3368719 : Blo 583288 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B878351 : Blo 583288 878351 := bstep (se 1 (by rfl) ⟨658763, by rfl⟩ : syracuseStep 878351 = 1317527) B1317527
theorem B878393 : Blo 583288 878393 := bstep (se 2 (by rfl) ⟨329397, by rfl⟩ : syracuseStep 878393 = 658795) B658795
theorem B583483 : Blo 583288 583483 := bstep (se 1 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 583483 = 875225) B875225
theorem B583559 : Blo 583288 583559 := bstep (se 1 (by rfl) ⟨437669, by rfl⟩ : syracuseStep 583559 = 875339) B875339
theorem B878471 : Blo 583288 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B583567 : Blo 583288 583567 := bstep (se 1 (by rfl) ⟨437675, by rfl⟩ : syracuseStep 583567 = 875351) B875351
theorem B878507 : Blo 583288 878507 := bstep (se 1 (by rfl) ⟨658880, by rfl⟩ : syracuseStep 878507 = 1317761) B1317761
theorem B583611 : Blo 583288 583611 := bstep (se 1 (by rfl) ⟨437708, by rfl⟩ : syracuseStep 583611 = 875417) B875417
theorem B1107913 : Blo 583288 1107913 := bstep (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) B830935
theorem B878537 : Blo 583288 878537 := bstep (se 2 (by rfl) ⟨329451, by rfl⟩ : syracuseStep 878537 = 658903) B658903
theorem B583687 : Blo 583288 583687 := bstep (se 1 (by rfl) ⟨437765, by rfl⟩ : syracuseStep 583687 = 875531) B875531
theorem B583695 : Blo 583288 583695 := bstep (se 1 (by rfl) ⟨437771, by rfl⟩ : syracuseStep 583695 = 875543) B875543
theorem B583739 : Blo 583288 583739 := bstep (se 1 (by rfl) ⟨437804, by rfl⟩ : syracuseStep 583739 = 875609) B875609
theorem B878651 : Blo 583288 878651 := bstep (se 1 (by rfl) ⟨658988, by rfl⟩ : syracuseStep 878651 = 1317977) B1317977
theorem B878711 : Blo 583288 878711 := bstep (se 1 (by rfl) ⟨659033, by rfl⟩ : syracuseStep 878711 = 1318067) B1318067
theorem B583815 : Blo 583288 583815 := bstep (se 1 (by rfl) ⟨437861, by rfl⟩ : syracuseStep 583815 = 875723) B875723
theorem B583823 : Blo 583288 583823 := bstep (se 1 (by rfl) ⟨437867, by rfl⟩ : syracuseStep 583823 = 875735) B875735
theorem B878735 : Blo 583288 878735 := bstep (se 1 (by rfl) ⟨659051, by rfl⟩ : syracuseStep 878735 = 1318103) B1318103
theorem B878777 : Blo 583288 878777 := bstep (se 2 (by rfl) ⟨329541, by rfl⟩ : syracuseStep 878777 = 659083) B659083
theorem B583867 : Blo 583288 583867 := bstep (se 1 (by rfl) ⟨437900, by rfl⟩ : syracuseStep 583867 = 875801) B875801
theorem B583943 : Blo 583288 583943 := bstep (se 1 (by rfl) ⟨437957, by rfl⟩ : syracuseStep 583943 = 875915) B875915
theorem B878855 : Blo 583288 878855 := bstep (se 1 (by rfl) ⟨659141, by rfl⟩ : syracuseStep 878855 = 1318283) B1318283
theorem B583951 : Blo 583288 583951 := bstep (se 1 (by rfl) ⟨437963, by rfl⟩ : syracuseStep 583951 = 875927) B875927
theorem B878891 : Blo 583288 878891 := bstep (se 1 (by rfl) ⟨659168, by rfl⟩ : syracuseStep 878891 = 1318337) B1318337
theorem B583995 : Blo 583288 583995 := bstep (se 1 (by rfl) ⟨437996, by rfl⟩ : syracuseStep 583995 = 875993) B875993
theorem B878921 : Blo 583288 878921 := bstep (se 2 (by rfl) ⟨329595, by rfl⟩ : syracuseStep 878921 = 659191) B659191
theorem B584071 : Blo 583288 584071 := bstep (se 1 (by rfl) ⟨438053, by rfl⟩ : syracuseStep 584071 = 876107) B876107
theorem B584079 : Blo 583288 584079 := bstep (se 1 (by rfl) ⟨438059, by rfl⟩ : syracuseStep 584079 = 876119) B876119
theorem B584123 : Blo 583288 584123 := bstep (se 1 (by rfl) ⟨438092, by rfl⟩ : syracuseStep 584123 = 876185) B876185
theorem B879035 : Blo 583288 879035 := bstep (se 1 (by rfl) ⟨659276, by rfl⟩ : syracuseStep 879035 = 1318553) B1318553
theorem B1665481 : Blo 583288 1665481 := bstep (se 2 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 1665481 = 1249111) B1249111
theorem B5630417 : Blo 583288 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B879095 : Blo 583288 879095 := bstep (se 1 (by rfl) ⟨659321, by rfl⟩ : syracuseStep 879095 = 1318643) B1318643
theorem B584199 : Blo 583288 584199 := bstep (se 1 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 584199 = 876299) B876299
theorem B584207 : Blo 583288 584207 := bstep (se 1 (by rfl) ⟨438155, by rfl⟩ : syracuseStep 584207 = 876311) B876311
theorem B879119 : Blo 583288 879119 := bstep (se 1 (by rfl) ⟨659339, by rfl⟩ : syracuseStep 879119 = 1318679) B1318679
theorem B12839467 : Blo 583288 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B879161 : Blo 583288 879161 := bstep (se 2 (by rfl) ⟨329685, by rfl⟩ : syracuseStep 879161 = 659371) B659371
theorem B584251 : Blo 583288 584251 := bstep (se 1 (by rfl) ⟨438188, by rfl⟩ : syracuseStep 584251 = 876377) B876377
theorem B584327 : Blo 583288 584327 := bstep (se 1 (by rfl) ⟨438245, by rfl⟩ : syracuseStep 584327 = 876491) B876491
theorem B879239 : Blo 583288 879239 := bstep (se 1 (by rfl) ⟨659429, by rfl⟩ : syracuseStep 879239 = 1318859) B1318859
theorem B584335 : Blo 583288 584335 := bstep (se 1 (by rfl) ⟨438251, by rfl⟩ : syracuseStep 584335 = 876503) B876503
theorem B879275 : Blo 583288 879275 := bstep (se 1 (by rfl) ⟨659456, by rfl⟩ : syracuseStep 879275 = 1318913) B1318913
theorem B584379 : Blo 583288 584379 := bstep (se 1 (by rfl) ⟨438284, by rfl⟩ : syracuseStep 584379 = 876569) B876569
theorem B879305 : Blo 583288 879305 := bstep (se 2 (by rfl) ⟨329739, by rfl⟩ : syracuseStep 879305 = 659479) B659479
theorem B584455 : Blo 583288 584455 := bstep (se 1 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 584455 = 876683) B876683
theorem B584463 : Blo 583288 584463 := bstep (se 1 (by rfl) ⟨438347, by rfl⟩ : syracuseStep 584463 = 876695) B876695
theorem B3336997 : Blo 583288 3336997 := bstep (se 4 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 3336997 = 625687) B625687
theorem B584507 : Blo 583288 584507 := bstep (se 1 (by rfl) ⟨438380, by rfl⟩ : syracuseStep 584507 = 876761) B876761
theorem B879419 : Blo 583288 879419 := bstep (se 1 (by rfl) ⟨659564, by rfl⟩ : syracuseStep 879419 = 1319129) B1319129
theorem B879479 : Blo 583288 879479 := bstep (se 1 (by rfl) ⟨659609, by rfl⟩ : syracuseStep 879479 = 1319219) B1319219
theorem B584583 : Blo 583288 584583 := bstep (se 1 (by rfl) ⟨438437, by rfl⟩ : syracuseStep 584583 = 876875) B876875
theorem B3173255 : Blo 583288 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B584591 : Blo 583288 584591 := bstep (se 1 (by rfl) ⟨438443, by rfl⟩ : syracuseStep 584591 = 876887) B876887
theorem B879503 : Blo 583288 879503 := bstep (se 1 (by rfl) ⟨659627, by rfl⟩ : syracuseStep 879503 = 1319255) B1319255
theorem B879545 : Blo 583288 879545 := bstep (se 2 (by rfl) ⟨329829, by rfl⟩ : syracuseStep 879545 = 659659) B659659
theorem B584635 : Blo 583288 584635 := bstep (se 1 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 584635 = 876953) B876953
theorem B584711 : Blo 583288 584711 := bstep (se 1 (by rfl) ⟨438533, by rfl⟩ : syracuseStep 584711 = 877067) B877067
theorem B879623 : Blo 583288 879623 := bstep (se 1 (by rfl) ⟨659717, by rfl⟩ : syracuseStep 879623 = 1319435) B1319435
theorem B584719 : Blo 583288 584719 := bstep (se 1 (by rfl) ⟨438539, by rfl⟩ : syracuseStep 584719 = 877079) B877079
theorem B3009565 : Blo 583288 3009565 := bstep (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) B1128587
theorem B879659 : Blo 583288 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B584763 : Blo 583288 584763 := bstep (se 1 (by rfl) ⟨438572, by rfl⟩ : syracuseStep 584763 = 877145) B877145
theorem B879689 : Blo 583288 879689 := bstep (se 2 (by rfl) ⟨329883, by rfl⟩ : syracuseStep 879689 = 659767) B659767
theorem B584839 : Blo 583288 584839 := bstep (se 1 (by rfl) ⟨438629, by rfl⟩ : syracuseStep 584839 = 877259) B877259
theorem B584847 : Blo 583288 584847 := bstep (se 1 (by rfl) ⟨438635, by rfl⟩ : syracuseStep 584847 = 877271) B877271
theorem B584891 : Blo 583288 584891 := bstep (se 1 (by rfl) ⟨438668, by rfl⟩ : syracuseStep 584891 = 877337) B877337
theorem B879803 : Blo 583288 879803 := bstep (se 1 (by rfl) ⟨659852, by rfl⟩ : syracuseStep 879803 = 1319705) B1319705
theorem B6647021 : Blo 583288 6647021 := bstep (se 3 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 6647021 = 2492633) B2492633
theorem B879863 : Blo 583288 879863 := bstep (se 1 (by rfl) ⟨659897, by rfl⟩ : syracuseStep 879863 = 1319795) B1319795
theorem B584967 : Blo 583288 584967 := bstep (se 1 (by rfl) ⟨438725, by rfl⟩ : syracuseStep 584967 = 877451) B877451
theorem B584975 : Blo 583288 584975 := bstep (se 1 (by rfl) ⟨438731, by rfl⟩ : syracuseStep 584975 = 877463) B877463
theorem B879887 : Blo 583288 879887 := bstep (se 1 (by rfl) ⟨659915, by rfl⟩ : syracuseStep 879887 = 1319831) B1319831
theorem B3337523 : Blo 583288 3337523 := bstep (se 1 (by rfl) ⟨2503142, by rfl⟩ : syracuseStep 3337523 = 5006285) B5006285
theorem B879929 : Blo 583288 879929 := bstep (se 2 (by rfl) ⟨329973, by rfl⟩ : syracuseStep 879929 = 659947) B659947
theorem B585019 : Blo 583288 585019 := bstep (se 1 (by rfl) ⟨438764, by rfl⟩ : syracuseStep 585019 = 877529) B877529
theorem B585095 : Blo 583288 585095 := bstep (se 1 (by rfl) ⟨438821, by rfl⟩ : syracuseStep 585095 = 877643) B877643
theorem B880007 : Blo 583288 880007 := bstep (se 1 (by rfl) ⟨660005, by rfl⟩ : syracuseStep 880007 = 1320011) B1320011
theorem B585103 : Blo 583288 585103 := bstep (se 1 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 585103 = 877655) B877655
theorem B880043 : Blo 583288 880043 := bstep (se 1 (by rfl) ⟨660032, by rfl⟩ : syracuseStep 880043 = 1320065) B1320065
theorem B9629113 : Blo 583288 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B585147 : Blo 583288 585147 := bstep (se 1 (by rfl) ⟨438860, by rfl⟩ : syracuseStep 585147 = 877721) B877721
theorem B880073 : Blo 583288 880073 := bstep (se 2 (by rfl) ⟨330027, by rfl⟩ : syracuseStep 880073 = 660055) B660055
theorem B97643981 : Blo 583288 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B585223 : Blo 583288 585223 := bstep (se 1 (by rfl) ⟨438917, by rfl⟩ : syracuseStep 585223 = 877835) B877835
theorem B585231 : Blo 583288 585231 := bstep (se 1 (by rfl) ⟨438923, by rfl⟩ : syracuseStep 585231 = 877847) B877847
theorem B585275 : Blo 583288 585275 := bstep (se 1 (by rfl) ⟨438956, by rfl⟩ : syracuseStep 585275 = 877913) B877913
theorem B880187 : Blo 583288 880187 := bstep (se 1 (by rfl) ⟨660140, by rfl⟩ : syracuseStep 880187 = 1320281) B1320281
theorem B880247 : Blo 583288 880247 := bstep (se 1 (by rfl) ⟨660185, by rfl⟩ : syracuseStep 880247 = 1320371) B1320371
theorem B585351 : Blo 583288 585351 := bstep (se 1 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 585351 = 878027) B878027
theorem B585359 : Blo 583288 585359 := bstep (se 1 (by rfl) ⟨439019, by rfl⟩ : syracuseStep 585359 = 878039) B878039
theorem B880271 : Blo 583288 880271 := bstep (se 1 (by rfl) ⟨660203, by rfl⟩ : syracuseStep 880271 = 1320407) B1320407
theorem B880313 : Blo 583288 880313 := bstep (se 2 (by rfl) ⟨330117, by rfl⟩ : syracuseStep 880313 = 660235) B660235
theorem B585403 : Blo 583288 585403 := bstep (se 1 (by rfl) ⟨439052, by rfl⟩ : syracuseStep 585403 = 878105) B878105
theorem B1601281 : Blo 583288 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B585479 : Blo 583288 585479 := bstep (se 1 (by rfl) ⟨439109, by rfl⟩ : syracuseStep 585479 = 878219) B878219
theorem B880391 : Blo 583288 880391 := bstep (se 1 (by rfl) ⟨660293, by rfl⟩ : syracuseStep 880391 = 1320587) B1320587
theorem B585487 : Blo 583288 585487 := bstep (se 1 (by rfl) ⟨439115, by rfl⟩ : syracuseStep 585487 = 878231) B878231
theorem B880427 : Blo 583288 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B23949107 : Blo 583288 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B585531 : Blo 583288 585531 := bstep (se 1 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 585531 = 878297) B878297
theorem B880457 : Blo 583288 880457 := bstep (se 2 (by rfl) ⟨330171, by rfl⟩ : syracuseStep 880457 = 660343) B660343
theorem B6025049 : Blo 583288 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B585607 : Blo 583288 585607 := bstep (se 1 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 585607 = 878411) B878411
theorem B585615 : Blo 583288 585615 := bstep (se 1 (by rfl) ⟨439211, by rfl⟩ : syracuseStep 585615 = 878423) B878423
theorem B2224057 : Blo 583288 2224057 := bstep (se 2 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 2224057 = 1668043) B1668043
theorem B585659 : Blo 583288 585659 := bstep (se 1 (by rfl) ⟨439244, by rfl⟩ : syracuseStep 585659 = 878489) B878489
theorem B880571 : Blo 583288 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B880631 : Blo 583288 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B585735 : Blo 583288 585735 := bstep (se 1 (by rfl) ⟨439301, by rfl⟩ : syracuseStep 585735 = 878603) B878603
theorem B1667087 : Blo 583288 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B585743 : Blo 583288 585743 := bstep (se 1 (by rfl) ⟨439307, by rfl⟩ : syracuseStep 585743 = 878615) B878615
theorem B880655 : Blo 583288 880655 := bstep (se 1 (by rfl) ⟨660491, by rfl⟩ : syracuseStep 880655 = 1320983) B1320983
theorem B880697 : Blo 583288 880697 := bstep (se 2 (by rfl) ⟨330261, by rfl⟩ : syracuseStep 880697 = 660523) B660523
theorem B585787 : Blo 583288 585787 := bstep (se 1 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 585787 = 878681) B878681
theorem B585863 : Blo 583288 585863 := bstep (se 1 (by rfl) ⟨439397, by rfl⟩ : syracuseStep 585863 = 878795) B878795
theorem B880775 : Blo 583288 880775 := bstep (se 1 (by rfl) ⟨660581, by rfl⟩ : syracuseStep 880775 = 1321163) B1321163
theorem B585871 : Blo 583288 585871 := bstep (se 1 (by rfl) ⟨439403, by rfl⟩ : syracuseStep 585871 = 878807) B878807
theorem B880811 : Blo 583288 880811 := bstep (se 1 (by rfl) ⟨660608, by rfl⟩ : syracuseStep 880811 = 1321217) B1321217
theorem B585915 : Blo 583288 585915 := bstep (se 1 (by rfl) ⟨439436, by rfl⟩ : syracuseStep 585915 = 878873) B878873
theorem B880841 : Blo 583288 880841 := bstep (se 2 (by rfl) ⟨330315, by rfl⟩ : syracuseStep 880841 = 660631) B660631
theorem B2814209 : Blo 583288 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B585991 : Blo 583288 585991 := bstep (se 1 (by rfl) ⟨439493, by rfl⟩ : syracuseStep 585991 = 878987) B878987
theorem B585999 : Blo 583288 585999 := bstep (se 1 (by rfl) ⟨439499, by rfl⟩ : syracuseStep 585999 = 878999) B878999
theorem B586043 : Blo 583288 586043 := bstep (se 1 (by rfl) ⟨439532, by rfl⟩ : syracuseStep 586043 = 879065) B879065
theorem B586119 : Blo 583288 586119 := bstep (se 1 (by rfl) ⟨439589, by rfl⟩ : syracuseStep 586119 = 879179) B879179
theorem B586127 : Blo 583288 586127 := bstep (se 1 (by rfl) ⟨439595, by rfl⟩ : syracuseStep 586127 = 879191) B879191
theorem B1110419 : Blo 583288 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B586171 : Blo 583288 586171 := bstep (se 1 (by rfl) ⟨439628, by rfl⟩ : syracuseStep 586171 = 879257) B879257
theorem B586247 : Blo 583288 586247 := bstep (se 1 (by rfl) ⟨439685, by rfl⟩ : syracuseStep 586247 = 879371) B879371
theorem B586255 : Blo 583288 586255 := bstep (se 1 (by rfl) ⟨439691, by rfl⟩ : syracuseStep 586255 = 879383) B879383
theorem B3568157 : Blo 583288 3568157 := bstep (se 3 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 3568157 = 1338059) B1338059
theorem B586299 : Blo 583288 586299 := bstep (se 1 (by rfl) ⟨439724, by rfl⟩ : syracuseStep 586299 = 879449) B879449
theorem B1110647 : Blo 583288 1110647 := bstep (se 1 (by rfl) ⟨832985, by rfl⟩ : syracuseStep 1110647 = 1665971) B1665971
theorem B586375 : Blo 583288 586375 := bstep (se 1 (by rfl) ⟨439781, by rfl⟩ : syracuseStep 586375 = 879563) B879563
theorem B586383 : Blo 583288 586383 := bstep (se 1 (by rfl) ⟨439787, by rfl⟩ : syracuseStep 586383 = 879575) B879575
theorem B586427 : Blo 583288 586427 := bstep (se 1 (by rfl) ⟨439820, by rfl⟩ : syracuseStep 586427 = 879641) B879641
theorem B3338981 : Blo 583288 3338981 := bstep (se 4 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 3338981 = 626059) B626059
theorem B586503 : Blo 583288 586503 := bstep (se 1 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 586503 = 879755) B879755
theorem B586511 : Blo 583288 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B586555 : Blo 583288 586555 := bstep (se 1 (by rfl) ⟨439916, by rfl⟩ : syracuseStep 586555 = 879833) B879833
theorem B586631 : Blo 583288 586631 := bstep (se 1 (by rfl) ⟨439973, by rfl⟩ : syracuseStep 586631 = 879947) B879947
theorem B586639 : Blo 583288 586639 := bstep (se 1 (by rfl) ⟨439979, by rfl⟩ : syracuseStep 586639 = 879959) B879959
theorem B586683 : Blo 583288 586683 := bstep (se 1 (by rfl) ⟨440012, by rfl⟩ : syracuseStep 586683 = 880025) B880025
theorem B586759 : Blo 583288 586759 := bstep (se 1 (by rfl) ⟨440069, by rfl⟩ : syracuseStep 586759 = 880139) B880139
theorem B586767 : Blo 583288 586767 := bstep (se 1 (by rfl) ⟨440075, by rfl⟩ : syracuseStep 586767 = 880151) B880151
theorem B2815019 : Blo 583288 2815019 := bstep (se 1 (by rfl) ⟨2111264, by rfl⟩ : syracuseStep 2815019 = 4222529) B4222529
theorem B586811 : Blo 583288 586811 := bstep (se 1 (by rfl) ⟨440108, by rfl⟩ : syracuseStep 586811 = 880217) B880217
theorem B1668215 : Blo 583288 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B586887 : Blo 583288 586887 := bstep (se 1 (by rfl) ⟨440165, by rfl⟩ : syracuseStep 586887 = 880331) B880331
theorem B586895 : Blo 583288 586895 := bstep (se 1 (by rfl) ⟨440171, by rfl⟩ : syracuseStep 586895 = 880343) B880343
theorem B586939 : Blo 583288 586939 := bstep (se 1 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 586939 = 880409) B880409
theorem B587015 : Blo 583288 587015 := bstep (se 1 (by rfl) ⟨440261, by rfl⟩ : syracuseStep 587015 = 880523) B880523
theorem B587023 : Blo 583288 587023 := bstep (se 1 (by rfl) ⟨440267, by rfl⟩ : syracuseStep 587023 = 880535) B880535
theorem B587067 : Blo 583288 587067 := bstep (se 1 (by rfl) ⟨440300, by rfl⟩ : syracuseStep 587067 = 880601) B880601
theorem B587143 : Blo 583288 587143 := bstep (se 1 (by rfl) ⟨440357, by rfl⟩ : syracuseStep 587143 = 880715) B880715
theorem B587151 : Blo 583288 587151 := bstep (se 1 (by rfl) ⟨440363, by rfl⟩ : syracuseStep 587151 = 880727) B880727
theorem B587195 : Blo 583288 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B587271 : Blo 583288 587271 := bstep (se 1 (by rfl) ⟨440453, by rfl⟩ : syracuseStep 587271 = 880907) B880907
theorem B587279 : Blo 583288 587279 := bstep (se 1 (by rfl) ⟨440459, by rfl⟩ : syracuseStep 587279 = 880919) B880919
theorem B12613421 : Blo 583288 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B1112363 : Blo 583288 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B8550803 : Blo 583288 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B7240195 : Blo 583288 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B1112591 : Blo 583288 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B6421169 : Blo 583288 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B1669889 : Blo 583288 1669889 := bstep (se 2 (by rfl) ⟨626208, by rfl⟩ : syracuseStep 1669889 = 1252417) B1252417
theorem B2226959 : Blo 583288 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B1670003 : Blo 583288 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B687035 : Blo 583288 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B2816977 : Blo 583288 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1670345 : Blo 583288 1670345 := bstep (se 2 (by rfl) ⟨626379, by rfl⟩ : syracuseStep 1670345 = 1252759) B1252759
theorem B4226363 : Blo 583288 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B6323665 : Blo 583288 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B6651395 : Blo 583288 6651395 := bstep (se 1 (by rfl) ⟨4988546, by rfl⟩ : syracuseStep 6651395 = 9977093) B9977093
theorem B5144141 : Blo 583288 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B5635763 : Blo 583288 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B1114003 : Blo 583288 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B4227079 : Blo 583288 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B1671187 : Blo 583288 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B1015865 : Blo 583288 1015865 := bstep (se 2 (by rfl) ⟨380949, by rfl⟩ : syracuseStep 1015865 = 761899) B761899
theorem B1441963 : Blo 583288 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B1671529 : Blo 583288 1671529 := bstep (se 2 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 1671529 = 1253647) B1253647
theorem B3342829 : Blo 583288 3342829 := bstep (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) B1253561
theorem B1671803 : Blo 583288 1671803 := bstep (se 1 (by rfl) ⟨1253852, by rfl⟩ : syracuseStep 1671803 = 2507705) B2507705
theorem B9503405 : Blo 583288 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B1114823 : Blo 583288 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B656347 : Blo 583288 656347 := bstep (se 1 (by rfl) ⟨492260, by rfl⟩ : syracuseStep 656347 = 984521) B984521
theorem B4457591 : Blo 583288 4457591 := bstep (se 1 (by rfl) ⟨3343193, by rfl⟩ : syracuseStep 4457591 = 6686387) B6686387
theorem B4228291 : Blo 583288 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B656815 : Blo 583288 656815 := bstep (se 1 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 656815 = 985223) B985223
theorem B1312505 : Blo 583288 1312505 := bstep (se 2 (by rfl) ⟨492189, by rfl⟩ : syracuseStep 1312505 = 984379) B984379
theorem B657247 : Blo 583288 657247 := bstep (se 1 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 657247 = 985871) B985871
theorem B985007 : Blo 583288 985007 := bstep (se 1 (by rfl) ⟨738755, by rfl⟩ : syracuseStep 985007 = 1477511) B1477511
theorem B1476539 : Blo 583288 1476539 := bstep (se 1 (by rfl) ⟨1107404, by rfl⟩ : syracuseStep 1476539 = 2214809) B2214809
theorem B1312775 : Blo 583288 1312775 := bstep (se 1 (by rfl) ⟨984581, by rfl⟩ : syracuseStep 1312775 = 1969163) B1969163
theorem B1312847 : Blo 583288 1312847 := bstep (se 1 (by rfl) ⟨984635, by rfl⟩ : syracuseStep 1312847 = 1969271) B1969271
theorem B657607 : Blo 583288 657607 := bstep (se 1 (by rfl) ⟨493205, by rfl⟩ : syracuseStep 657607 = 986411) B986411
theorem B1870091 : Blo 583288 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B13502771 : Blo 583288 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B985439 : Blo 583288 985439 := bstep (se 1 (by rfl) ⟨739079, by rfl⟩ : syracuseStep 985439 = 1478159) B1478159
theorem B4491625 : Blo 583288 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B1313243 : Blo 583288 1313243 := bstep (se 1 (by rfl) ⟨984932, by rfl⟩ : syracuseStep 1313243 = 1969865) B1969865
theorem B625115 : Blo 583288 625115 := bstep (se 1 (by rfl) ⟨468836, by rfl⟩ : syracuseStep 625115 = 937673) B937673
theorem B1804763 : Blo 583288 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B789031 : Blo 583288 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B1477217 : Blo 583288 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B1051307 : Blo 583288 1051307 := bstep (se 1 (by rfl) ⟨788480, by rfl⟩ : syracuseStep 1051307 = 1576961) B1576961
theorem B1968839 : Blo 583288 1968839 := bstep (se 1 (by rfl) ⟨1476629, by rfl⟩ : syracuseStep 1968839 = 2953259) B2953259
theorem B985999 : Blo 583288 985999 := bstep (se 1 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 985999 = 1478999) B1478999
theorem B1313711 : Blo 583288 1313711 := bstep (se 1 (by rfl) ⟨985283, by rfl⟩ : syracuseStep 1313711 = 1970567) B1970567
theorem B658471 : Blo 583288 658471 := bstep (se 1 (by rfl) ⟨493853, by rfl⟩ : syracuseStep 658471 = 987707) B987707
theorem B1313963 : Blo 583288 1313963 := bstep (se 1 (by rfl) ⟨985472, by rfl⟩ : syracuseStep 1313963 = 1970945) B1970945
theorem B9637157 : Blo 583288 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B1969703 : Blo 583288 1969703 := bstep (se 1 (by rfl) ⟨1477277, by rfl⟩ : syracuseStep 1969703 = 2954555) B2954555
theorem B986681 : Blo 583288 986681 := bstep (se 2 (by rfl) ⟨370005, by rfl⟩ : syracuseStep 986681 = 740011) B740011
theorem B1969811 : Blo 583288 1969811 := bstep (se 1 (by rfl) ⟨1477358, by rfl⟩ : syracuseStep 1969811 = 2954717) B2954717
theorem B1314503 : Blo 583288 1314503 := bstep (se 1 (by rfl) ⟨985877, by rfl⟩ : syracuseStep 1314503 = 1971755) B1971755
theorem B2035529 : Blo 583288 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B1970027 : Blo 583288 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B1970081 : Blo 583288 1970081 := bstep (se 2 (by rfl) ⟨738780, by rfl⟩ : syracuseStep 1970081 = 1477561) B1477561
theorem B1478675 : Blo 583288 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B987383 : Blo 583288 987383 := bstep (se 1 (by rfl) ⟨740537, by rfl⟩ : syracuseStep 987383 = 1481075) B1481075
theorem B4231435 : Blo 583288 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B1479131 : Blo 583288 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B2494957 : Blo 583288 2494957 := bstep (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) B935609
theorem B1970675 : Blo 583288 1970675 := bstep (se 1 (by rfl) ⟨1478006, by rfl⟩ : syracuseStep 1970675 = 2956013) B2956013
theorem B6689303 : Blo 583288 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B1315367 : Blo 583288 1315367 := bstep (se 1 (by rfl) ⟨986525, by rfl⟩ : syracuseStep 1315367 = 1973051) B1973051
theorem B987727 : Blo 583288 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B660091 : Blo 583288 660091 := bstep (se 1 (by rfl) ⟨495068, by rfl⟩ : syracuseStep 660091 = 990137) B990137
theorem B18977489 : Blo 583288 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B3740489 : Blo 583288 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B987977 : Blo 583288 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B1315691 : Blo 583288 1315691 := bstep (se 1 (by rfl) ⟨986768, by rfl⟩ : syracuseStep 1315691 = 1973537) B1973537
theorem B1315745 : Blo 583288 1315745 := bstep (se 2 (by rfl) ⟨493404, by rfl⟩ : syracuseStep 1315745 = 986809) B986809
theorem B4330415 : Blo 583288 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2135041 : Blo 583288 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1971215 : Blo 583288 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B660559 : Blo 583288 660559 := bstep (se 1 (by rfl) ⟨495419, by rfl⟩ : syracuseStep 660559 = 990839) B990839
theorem B2954393 : Blo 583288 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B6657227 : Blo 583288 6657227 := bstep (se 1 (by rfl) ⟨4992920, by rfl⟩ : syracuseStep 6657227 = 9985841) B9985841
theorem B1316087 : Blo 583288 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B988409 : Blo 583288 988409 := bstep (se 2 (by rfl) ⟨370653, by rfl⟩ : syracuseStep 988409 = 741307) B741307
theorem B988591 : Blo 583288 988591 := bstep (se 1 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 988591 = 1482887) B1482887
theorem B988679 : Blo 583288 988679 := bstep (se 1 (by rfl) ⟨741509, by rfl⟩ : syracuseStep 988679 = 1483019) B1483019
theorem B1971809 : Blo 583288 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B1480315 : Blo 583288 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B2561675 : Blo 583288 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B1316681 : Blo 583288 1316681 := bstep (se 2 (by rfl) ⟨493755, by rfl⟩ : syracuseStep 1316681 = 987511) B987511
theorem B989023 : Blo 583288 989023 := bstep (se 1 (by rfl) ⟨741767, by rfl⟩ : syracuseStep 989023 = 1483535) B1483535
theorem B989111 : Blo 583288 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B989705 : Blo 583288 989705 := bstep (se 2 (by rfl) ⟨371139, by rfl⟩ : syracuseStep 989705 = 742279) B742279
theorem B1317473 : Blo 583288 1317473 := bstep (se 2 (by rfl) ⟨494052, by rfl⟩ : syracuseStep 1317473 = 988105) B988105
theorem B989867 : Blo 583288 989867 := bstep (se 1 (by rfl) ⟨742400, by rfl⟩ : syracuseStep 989867 = 1484801) B1484801
theorem B2103997 : Blo 583288 2103997 := bstep (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) B788999
theorem B1317815 : Blo 583288 1317815 := bstep (se 1 (by rfl) ⟨988361, by rfl⟩ : syracuseStep 1317815 = 1976723) B1976723
theorem B1973267 : Blo 583288 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B990265 : Blo 583288 990265 := bstep (se 2 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 990265 = 742699) B742699
theorem B1186987 : Blo 583288 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B990407 : Blo 583288 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B1973591 : Blo 583288 1973591 := bstep (se 1 (by rfl) ⟨1480193, by rfl⟩ : syracuseStep 1973591 = 2960387) B2960387
theorem B990569 : Blo 583288 990569 := bstep (se 2 (by rfl) ⟨371463, by rfl⟩ : syracuseStep 990569 = 742927) B742927
theorem B4431347 : Blo 583288 4431347 := bstep (se 1 (by rfl) ⟨3323510, by rfl⟩ : syracuseStep 4431347 = 6647021) B6647021
theorem B1318409 : Blo 583288 1318409 := bstep (se 2 (by rfl) ⟨494403, by rfl⟩ : syracuseStep 1318409 = 988807) B988807
theorem B990967 : Blo 583288 990967 := bstep (se 1 (by rfl) ⟨743225, by rfl⟩ : syracuseStep 990967 = 1486451) B1486451
theorem B1318751 : Blo 583288 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B15966071 : Blo 583288 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B1777583 : Blo 583288 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B46768141 : Blo 583288 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B1318931 : Blo 583288 1318931 := bstep (se 1 (by rfl) ⟨989198, by rfl⟩ : syracuseStep 1318931 = 1978397) B1978397
theorem B1581113 : Blo 583288 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B1876139 : Blo 583288 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B2171075 : Blo 583288 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B32579941 : Blo 583288 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B2498921 : Blo 583288 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1319273 : Blo 583288 1319273 := bstep (se 2 (by rfl) ⟨494727, by rfl⟩ : syracuseStep 1319273 = 989455) B989455
theorem B1974671 : Blo 583288 1974671 := bstep (se 1 (by rfl) ⟨1481003, by rfl⟩ : syracuseStep 1974671 = 2962007) B2962007
theorem B1188283 : Blo 583288 1188283 := bstep (se 1 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 1188283 = 1782425) B1782425
theorem B2105801 : Blo 583288 2105801 := bstep (se 2 (by rfl) ⟨789675, by rfl⟩ : syracuseStep 2105801 = 1579351) B1579351
theorem B3744281 : Blo 583288 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B1876679 : Blo 583288 1876679 := bstep (se 1 (by rfl) ⟨1407509, by rfl⟩ : syracuseStep 1876679 = 2815019) B2815019
theorem B1974995 : Blo 583288 1974995 := bstep (se 1 (by rfl) ⟨1481246, by rfl⟩ : syracuseStep 1974995 = 2962493) B2962493
theorem B1319867 : Blo 583288 1319867 := bstep (se 1 (by rfl) ⟨989900, by rfl⟩ : syracuseStep 1319867 = 1979801) B1979801
theorem B1319993 : Blo 583288 1319993 := bstep (se 2 (by rfl) ⟨494997, by rfl⟩ : syracuseStep 1319993 = 989995) B989995
theorem B1058039 : Blo 583288 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B1320335 : Blo 583288 1320335 := bstep (se 1 (by rfl) ⟨990251, by rfl⟩ : syracuseStep 1320335 = 1980503) B1980503
theorem B1320659 : Blo 583288 1320659 := bstep (se 1 (by rfl) ⟨990494, by rfl⟩ : syracuseStep 1320659 = 1980989) B1980989
theorem B117253973 : Blo 583288 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B1484639 : Blo 583288 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B2107255 : Blo 583288 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B1976183 : Blo 583288 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1189775 : Blo 583288 1189775 := bstep (se 1 (by rfl) ⟨892331, by rfl⟩ : syracuseStep 1189775 = 1784663) B1784663
theorem B8431553 : Blo 583288 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B1976399 : Blo 583288 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B2369803 : Blo 583288 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B4434263 : Blo 583288 4434263 := bstep (se 1 (by rfl) ⟨3325697, by rfl⟩ : syracuseStep 4434263 = 6651395) B6651395
theorem B1976777 : Blo 583288 1976777 := bstep (se 2 (by rfl) ⟨741291, by rfl⟩ : syracuseStep 1976777 = 1482583) B1482583
theorem B1485337 : Blo 583288 1485337 := bstep (se 2 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 1485337 = 1114003) B1114003
theorem B3746513 : Blo 583288 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B1977047 : Blo 583288 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B1583945 : Blo 583288 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B1485641 : Blo 583288 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B6663059 : Blo 583288 6663059 := bstep (se 1 (by rfl) ⟨4997294, by rfl⟩ : syracuseStep 6663059 = 9994589) B9994589
theorem B1977263 : Blo 583288 1977263 := bstep (se 1 (by rfl) ⟨1482947, by rfl⟩ : syracuseStep 1977263 = 2965895) B2965895
theorem B1780663 : Blo 583288 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B3157163 : Blo 583288 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B830827 : Blo 583288 830827 := bstep (se 1 (by rfl) ⟨623120, by rfl⟩ : syracuseStep 830827 = 1246241) B1246241
theorem B2108987 : Blo 583288 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B831055 : Blo 583288 831055 := bstep (se 1 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 831055 = 1246583) B1246583
theorem B2961035 : Blo 583288 2961035 := bstep (se 1 (by rfl) ⟨2220776, by rfl⟩ : syracuseStep 2961035 = 4441553) B4441553
theorem B2994029 : Blo 583288 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B1126457 : Blo 583288 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B3551321 : Blo 583288 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B2371699 : Blo 583288 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B832199 : Blo 583288 832199 := bstep (se 1 (by rfl) ⟨624149, by rfl⟩ : syracuseStep 832199 = 1248299) B1248299
theorem B1979639 : Blo 583288 1979639 := bstep (se 1 (by rfl) ⟨1484729, by rfl⟩ : syracuseStep 1979639 = 2969459) B2969459
theorem B4207909 : Blo 583288 4207909 := bstep (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) B788983
theorem B701803 : Blo 583288 701803 := bstep (se 1 (by rfl) ⟨526352, by rfl⟩ : syracuseStep 701803 = 1052705) B1052705
theorem B832951 : Blo 583288 832951 := bstep (se 1 (by rfl) ⟨624713, by rfl⟩ : syracuseStep 832951 = 1249427) B1249427
theorem B1979963 : Blo 583288 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B2373259 : Blo 583288 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B1980233 : Blo 583288 1980233 := bstep (se 2 (by rfl) ⟨742587, by rfl⟩ : syracuseStep 1980233 = 1485175) B1485175
theorem B17119289 : Blo 583288 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B1784359 : Blo 583288 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B4012753 : Blo 583288 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B834409 : Blo 583288 834409 := bstep (se 2 (by rfl) ⟨312903, by rfl⟩ : syracuseStep 834409 = 625807) B625807
theorem B1784759 : Blo 583288 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1981367 : Blo 583288 1981367 := bstep (se 1 (by rfl) ⟨1486025, by rfl⟩ : syracuseStep 1981367 = 2972051) B2972051
theorem B1981961 : Blo 583288 1981961 := bstep (se 2 (by rfl) ⟨743235, by rfl⟩ : syracuseStep 1981961 = 1486471) B1486471
theorem B2506439 : Blo 583288 2506439 := bstep (se 1 (by rfl) ⟨1879829, by rfl⟩ : syracuseStep 2506439 = 3759659) B3759659
theorem B2965409 : Blo 583288 2965409 := bstep (se 2 (by rfl) ⟨1112028, by rfl⟩ : syracuseStep 2965409 = 2224057) B2224057
theorem B10141625 : Blo 583288 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B3293729 : Blo 583288 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B934649 : Blo 583288 934649 := bstep (se 2 (by rfl) ⟨350493, by rfl⟩ : syracuseStep 934649 = 700987) B700987
theorem B2114579 : Blo 583288 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B2999467 : Blo 583288 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B3753611 : Blo 583288 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B2115503 : Blo 583288 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B65095987 : Blo 583288 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B4016699 : Blo 583288 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B740279 : Blo 583288 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B2378771 : Blo 583288 2378771 := bstep (se 1 (by rfl) ⟨1784078, by rfl⟩ : syracuseStep 2378771 = 3568157) B3568157
theorem B740431 : Blo 583288 740431 := bstep (se 1 (by rfl) ⟨555323, by rfl⟩ : syracuseStep 740431 = 1110647) B1110647
theorem B9653593 : Blo 583288 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B2215613 : Blo 583288 2215613 := bstep (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) B830855
theorem B7130861 : Blo 583288 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B8408947 : Blo 583288 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B3755969 : Blo 583288 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B937993 : Blo 583288 937993 := bstep (se 2 (by rfl) ⟨351747, by rfl⟩ : syracuseStep 937993 = 703495) B703495
theorem B741575 : Blo 583288 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B8540477 : Blo 583288 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B5001533 : Blo 583288 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B741727 : Blo 583288 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B4280779 : Blo 583288 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B6410963 : Blo 583288 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B3429427 : Blo 583288 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B2217041 : Blo 583288 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B3757175 : Blo 583288 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B36591587 : Blo 583288 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B2218529 : Blo 583288 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B875087 : Blo 583288 875087 := bstep (se 1 (by rfl) ⟨656315, by rfl⟩ : syracuseStep 875087 = 1312631) B1312631
theorem B875207 : Blo 583288 875207 := bstep (se 1 (by rfl) ⟨656405, by rfl⟩ : syracuseStep 875207 = 1312811) B1312811
theorem B2218711 : Blo 583288 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B875369 : Blo 583288 875369 := bstep (se 2 (by rfl) ⟨328263, by rfl⟩ : syracuseStep 875369 = 656527) B656527
theorem B875447 : Blo 583288 875447 := bstep (se 1 (by rfl) ⟨656585, by rfl⟩ : syracuseStep 875447 = 1313171) B1313171
theorem B875483 : Blo 583288 875483 := bstep (se 1 (by rfl) ⟨656612, by rfl⟩ : syracuseStep 875483 = 1313225) B1313225
theorem B2219015 : Blo 583288 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B4742297 : Blo 583288 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B4447385 : Blo 583288 4447385 := bstep (se 2 (by rfl) ⟨1667769, by rfl⟩ : syracuseStep 4447385 = 3335539) B3335539
theorem B4742489 : Blo 583288 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B875951 : Blo 583288 875951 := bstep (se 1 (by rfl) ⟨656963, by rfl⟩ : syracuseStep 875951 = 1313927) B1313927
theorem B4218313 : Blo 583288 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B2219501 : Blo 583288 2219501 := bstep (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) B832313
theorem B876041 : Blo 583288 876041 := bstep (se 2 (by rfl) ⟨328515, by rfl⟩ : syracuseStep 876041 = 657031) B657031
theorem B876071 : Blo 583288 876071 := bstep (se 1 (by rfl) ⟨657053, by rfl⟩ : syracuseStep 876071 = 1314107) B1314107
theorem B2809441 : Blo 583288 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B876155 : Blo 583288 876155 := bstep (se 1 (by rfl) ⟨657116, by rfl⟩ : syracuseStep 876155 = 1314233) B1314233
theorem B1662713 : Blo 583288 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B876281 : Blo 583288 876281 := bstep (se 2 (by rfl) ⟨328605, by rfl⟩ : syracuseStep 876281 = 657211) B657211
theorem B9002785 : Blo 583288 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B6348577 : Blo 583288 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B876383 : Blo 583288 876383 := bstep (se 1 (by rfl) ⟨657287, by rfl⟩ : syracuseStep 876383 = 1314575) B1314575
theorem B876395 : Blo 583288 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B3334081 : Blo 583288 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B2252801 : Blo 583288 2252801 := bstep (se 2 (by rfl) ⟨844800, by rfl⟩ : syracuseStep 2252801 = 1689601) B1689601
theorem B1663055 : Blo 583288 1663055 := bstep (se 1 (by rfl) ⟨1247291, by rfl⟩ : syracuseStep 1663055 = 2494583) B2494583
theorem B876623 : Blo 583288 876623 := bstep (se 1 (by rfl) ⟨657467, by rfl⟩ : syracuseStep 876623 = 1314935) B1314935
theorem B876743 : Blo 583288 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B876905 : Blo 583288 876905 := bstep (se 2 (by rfl) ⟨328839, by rfl⟩ : syracuseStep 876905 = 657679) B657679
theorem B876983 : Blo 583288 876983 := bstep (se 1 (by rfl) ⟨657737, by rfl⟩ : syracuseStep 876983 = 1315475) B1315475
theorem B877019 : Blo 583288 877019 := bstep (se 1 (by rfl) ⟨657764, by rfl⟩ : syracuseStep 877019 = 1315529) B1315529
theorem B2220641 : Blo 583288 2220641 := bstep (se 2 (by rfl) ⟨832740, by rfl⟩ : syracuseStep 2220641 = 1665481) B1665481
theorem B35971913 : Blo 583288 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1401761 : Blo 583288 1401761 := bstep (se 2 (by rfl) ⟨525660, by rfl⟩ : syracuseStep 1401761 = 1051321) B1051321
theorem B877487 : Blo 583288 877487 := bstep (se 1 (by rfl) ⟨658115, by rfl⟩ : syracuseStep 877487 = 1316231) B1316231
theorem B877577 : Blo 583288 877577 := bstep (se 2 (by rfl) ⟨329091, by rfl⟩ : syracuseStep 877577 = 658183) B658183
theorem B877607 : Blo 583288 877607 := bstep (se 1 (by rfl) ⟨658205, by rfl⟩ : syracuseStep 877607 = 1316411) B1316411
theorem B4449329 : Blo 583288 4449329 := bstep (se 2 (by rfl) ⟨1668498, by rfl⟩ : syracuseStep 4449329 = 3336997) B3336997
theorem B1664057 : Blo 583288 1664057 := bstep (se 2 (by rfl) ⟨624021, by rfl⟩ : syracuseStep 1664057 = 1248043) B1248043
theorem B877691 : Blo 583288 877691 := bstep (se 1 (by rfl) ⟨658268, by rfl⟩ : syracuseStep 877691 = 1316537) B1316537
theorem B1664171 : Blo 583288 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B877817 : Blo 583288 877817 := bstep (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) B658363
theorem B877919 : Blo 583288 877919 := bstep (se 1 (by rfl) ⟨658439, by rfl⟩ : syracuseStep 877919 = 1316879) B1316879
theorem B877931 : Blo 583288 877931 := bstep (se 1 (by rfl) ⟨658448, by rfl⟩ : syracuseStep 877931 = 1316897) B1316897
theorem B1500659 : Blo 583288 1500659 := bstep (se 1 (by rfl) ⟨1125494, by rfl⟩ : syracuseStep 1500659 = 2250989) B2250989
theorem B3565043 : Blo 583288 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B2221627 : Blo 583288 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B878159 : Blo 583288 878159 := bstep (se 1 (by rfl) ⟨658619, by rfl⟩ : syracuseStep 878159 = 1317239) B1317239
theorem B3761761 : Blo 583288 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B583291 : Blo 583288 583291 := bstep (se 1 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 583291 = 874937) B874937
theorem B3991187 : Blo 583288 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B583343 : Blo 583288 583343 := bstep (se 1 (by rfl) ⟨437507, by rfl⟩ : syracuseStep 583343 = 875015) B875015
theorem B583367 : Blo 583288 583367 := bstep (se 1 (by rfl) ⟨437525, by rfl⟩ : syracuseStep 583367 = 875051) B875051
theorem B878279 : Blo 583288 878279 := bstep (se 1 (by rfl) ⟨658709, by rfl⟩ : syracuseStep 878279 = 1317419) B1317419
theorem B1205959 : Blo 583288 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B6317783 : Blo 583288 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B583387 : Blo 583288 583387 := bstep (se 1 (by rfl) ⟨437540, by rfl⟩ : syracuseStep 583387 = 875081) B875081
theorem B583463 : Blo 583288 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B6645563 : Blo 583288 6645563 := bstep (se 1 (by rfl) ⟨4984172, by rfl⟩ : syracuseStep 6645563 = 9968345) B9968345
theorem B583503 : Blo 583288 583503 := bstep (se 1 (by rfl) ⟨437627, by rfl⟩ : syracuseStep 583503 = 875255) B875255
theorem B583519 : Blo 583288 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B878441 : Blo 583288 878441 := bstep (se 2 (by rfl) ⟨329415, by rfl⟩ : syracuseStep 878441 = 658831) B658831
theorem B2221931 : Blo 583288 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B583547 : Blo 583288 583547 := bstep (se 1 (by rfl) ⟨437660, by rfl⟩ : syracuseStep 583547 = 875321) B875321
theorem B12838817 : Blo 583288 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B583599 : Blo 583288 583599 := bstep (se 1 (by rfl) ⟨437699, by rfl⟩ : syracuseStep 583599 = 875399) B875399
theorem B878519 : Blo 583288 878519 := bstep (se 1 (by rfl) ⟨658889, by rfl⟩ : syracuseStep 878519 = 1317779) B1317779
theorem B583623 : Blo 583288 583623 := bstep (se 1 (by rfl) ⟨437717, by rfl⟩ : syracuseStep 583623 = 875435) B875435
theorem B583643 : Blo 583288 583643 := bstep (se 1 (by rfl) ⟨437732, by rfl⟩ : syracuseStep 583643 = 875465) B875465
theorem B878555 : Blo 583288 878555 := bstep (se 1 (by rfl) ⟨658916, by rfl⟩ : syracuseStep 878555 = 1317833) B1317833
theorem B2222099 : Blo 583288 2222099 := bstep (se 1 (by rfl) ⟨1666574, by rfl⟩ : syracuseStep 2222099 = 3333149) B3333149
theorem B583719 : Blo 583288 583719 := bstep (se 1 (by rfl) ⟨437789, by rfl⟩ : syracuseStep 583719 = 875579) B875579
theorem B583759 : Blo 583288 583759 := bstep (se 1 (by rfl) ⟨437819, by rfl⟩ : syracuseStep 583759 = 875639) B875639
theorem B583775 : Blo 583288 583775 := bstep (se 1 (by rfl) ⟨437831, by rfl⟩ : syracuseStep 583775 = 875663) B875663
theorem B583803 : Blo 583288 583803 := bstep (se 1 (by rfl) ⟨437852, by rfl⟩ : syracuseStep 583803 = 875705) B875705
theorem B583855 : Blo 583288 583855 := bstep (se 1 (by rfl) ⟨437891, by rfl⟩ : syracuseStep 583855 = 875783) B875783
theorem B583879 : Blo 583288 583879 := bstep (se 1 (by rfl) ⟨437909, by rfl⟩ : syracuseStep 583879 = 875819) B875819
theorem B583899 : Blo 583288 583899 := bstep (se 1 (by rfl) ⟨437924, by rfl⟩ : syracuseStep 583899 = 875849) B875849
theorem B1108217 : Blo 583288 1108217 := bstep (se 2 (by rfl) ⟨415581, by rfl⟩ : syracuseStep 1108217 = 831163) B831163
theorem B583975 : Blo 583288 583975 := bstep (se 1 (by rfl) ⟨437981, by rfl⟩ : syracuseStep 583975 = 875963) B875963
theorem B584015 : Blo 583288 584015 := bstep (se 1 (by rfl) ⟨438011, by rfl⟩ : syracuseStep 584015 = 876023) B876023
theorem B584031 : Blo 583288 584031 := bstep (se 1 (by rfl) ⟨438023, by rfl⟩ : syracuseStep 584031 = 876047) B876047
theorem B584059 : Blo 583288 584059 := bstep (se 1 (by rfl) ⟨438044, by rfl⟩ : syracuseStep 584059 = 876089) B876089
theorem B1108399 : Blo 583288 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B584111 : Blo 583288 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B879023 : Blo 583288 879023 := bstep (se 1 (by rfl) ⟨659267, by rfl⟩ : syracuseStep 879023 = 1318535) B1318535
theorem B584135 : Blo 583288 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B584155 : Blo 583288 584155 := bstep (se 1 (by rfl) ⟨438116, by rfl⟩ : syracuseStep 584155 = 876233) B876233
theorem B879113 : Blo 583288 879113 := bstep (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) B659335
theorem B2812441 : Blo 583288 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B584231 : Blo 583288 584231 := bstep (se 1 (by rfl) ⟨438173, by rfl⟩ : syracuseStep 584231 = 876347) B876347
theorem B879143 : Blo 583288 879143 := bstep (se 1 (by rfl) ⟨659357, by rfl⟩ : syracuseStep 879143 = 1318715) B1318715
theorem B1108559 : Blo 583288 1108559 := bstep (se 1 (by rfl) ⟨831419, by rfl⟩ : syracuseStep 1108559 = 1662839) B1662839
theorem B584271 : Blo 583288 584271 := bstep (se 1 (by rfl) ⟨438203, by rfl⟩ : syracuseStep 584271 = 876407) B876407
theorem B584287 : Blo 583288 584287 := bstep (se 1 (by rfl) ⟨438215, by rfl⟩ : syracuseStep 584287 = 876431) B876431
theorem B584315 : Blo 583288 584315 := bstep (se 1 (by rfl) ⟨438236, by rfl⟩ : syracuseStep 584315 = 876473) B876473
theorem B879227 : Blo 583288 879227 := bstep (se 1 (by rfl) ⟨659420, by rfl⟩ : syracuseStep 879227 = 1318841) B1318841
theorem B1403531 : Blo 583288 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B584367 : Blo 583288 584367 := bstep (se 1 (by rfl) ⟨438275, by rfl⟩ : syracuseStep 584367 = 876551) B876551
theorem B584391 : Blo 583288 584391 := bstep (se 1 (by rfl) ⟨438293, by rfl⟩ : syracuseStep 584391 = 876587) B876587
theorem B584411 : Blo 583288 584411 := bstep (se 1 (by rfl) ⟨438308, by rfl⟩ : syracuseStep 584411 = 876617) B876617
theorem B879353 : Blo 583288 879353 := bstep (se 2 (by rfl) ⟨329757, by rfl⟩ : syracuseStep 879353 = 659515) B659515
theorem B584487 : Blo 583288 584487 := bstep (se 1 (by rfl) ⟨438365, by rfl⟩ : syracuseStep 584487 = 876731) B876731
theorem B584527 : Blo 583288 584527 := bstep (se 1 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 584527 = 876791) B876791
theorem B584543 : Blo 583288 584543 := bstep (se 1 (by rfl) ⟨438407, by rfl⟩ : syracuseStep 584543 = 876815) B876815
theorem B879455 : Blo 583288 879455 := bstep (se 1 (by rfl) ⟨659591, by rfl⟩ : syracuseStep 879455 = 1319183) B1319183
theorem B879467 : Blo 583288 879467 := bstep (se 1 (by rfl) ⟨659600, by rfl⟩ : syracuseStep 879467 = 1319201) B1319201
theorem B584571 : Blo 583288 584571 := bstep (se 1 (by rfl) ⟨438428, by rfl⟩ : syracuseStep 584571 = 876857) B876857
theorem B584623 : Blo 583288 584623 := bstep (se 1 (by rfl) ⟨438467, by rfl⟩ : syracuseStep 584623 = 876935) B876935
theorem B584647 : Blo 583288 584647 := bstep (se 1 (by rfl) ⟨438485, by rfl⟩ : syracuseStep 584647 = 876971) B876971
theorem B584667 : Blo 583288 584667 := bstep (se 1 (by rfl) ⟨438500, by rfl⟩ : syracuseStep 584667 = 877001) B877001
theorem B584743 : Blo 583288 584743 := bstep (se 1 (by rfl) ⟨438557, by rfl⟩ : syracuseStep 584743 = 877115) B877115
theorem B584783 : Blo 583288 584783 := bstep (se 1 (by rfl) ⟨438587, by rfl⟩ : syracuseStep 584783 = 877175) B877175
theorem B879695 : Blo 583288 879695 := bstep (se 1 (by rfl) ⟨659771, by rfl⟩ : syracuseStep 879695 = 1319543) B1319543
theorem B584799 : Blo 583288 584799 := bstep (se 1 (by rfl) ⟨438599, by rfl⟩ : syracuseStep 584799 = 877199) B877199
theorem B584827 : Blo 583288 584827 := bstep (se 1 (by rfl) ⟨438620, by rfl⟩ : syracuseStep 584827 = 877241) B877241
theorem B584879 : Blo 583288 584879 := bstep (se 1 (by rfl) ⟨438659, by rfl⟩ : syracuseStep 584879 = 877319) B877319
theorem B584903 : Blo 583288 584903 := bstep (se 1 (by rfl) ⟨438677, by rfl⟩ : syracuseStep 584903 = 877355) B877355
theorem B879815 : Blo 583288 879815 := bstep (se 1 (by rfl) ⟨659861, by rfl⟩ : syracuseStep 879815 = 1319723) B1319723
theorem B584923 : Blo 583288 584923 := bstep (se 1 (by rfl) ⟨438692, by rfl⟩ : syracuseStep 584923 = 877385) B877385
theorem B584999 : Blo 583288 584999 := bstep (se 1 (by rfl) ⟨438749, by rfl⟩ : syracuseStep 584999 = 877499) B877499
theorem B585039 : Blo 583288 585039 := bstep (se 1 (by rfl) ⟨438779, by rfl⟩ : syracuseStep 585039 = 877559) B877559
theorem B585055 : Blo 583288 585055 := bstep (se 1 (by rfl) ⟨438791, by rfl⟩ : syracuseStep 585055 = 877583) B877583
theorem B879977 : Blo 583288 879977 := bstep (se 2 (by rfl) ⟨329991, by rfl⟩ : syracuseStep 879977 = 659983) B659983
theorem B585083 : Blo 583288 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B5074319 : Blo 583288 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B585135 : Blo 583288 585135 := bstep (se 1 (by rfl) ⟨438851, by rfl⟩ : syracuseStep 585135 = 877703) B877703
theorem B880055 : Blo 583288 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B585159 : Blo 583288 585159 := bstep (se 1 (by rfl) ⟨438869, by rfl⟩ : syracuseStep 585159 = 877739) B877739
theorem B585179 : Blo 583288 585179 := bstep (se 1 (by rfl) ⟨438884, by rfl⟩ : syracuseStep 585179 = 877769) B877769
theorem B880091 : Blo 583288 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B1666585 : Blo 583288 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B585255 : Blo 583288 585255 := bstep (se 1 (by rfl) ⟨438941, by rfl⟩ : syracuseStep 585255 = 877883) B877883
theorem B585295 : Blo 583288 585295 := bstep (se 1 (by rfl) ⟨438971, by rfl⟩ : syracuseStep 585295 = 877943) B877943
theorem B585311 : Blo 583288 585311 := bstep (se 1 (by rfl) ⟨438983, by rfl⟩ : syracuseStep 585311 = 877967) B877967
theorem B585339 : Blo 583288 585339 := bstep (se 1 (by rfl) ⟨439004, by rfl⟩ : syracuseStep 585339 = 878009) B878009
theorem B1109675 : Blo 583288 1109675 := bstep (se 1 (by rfl) ⟨832256, by rfl⟩ : syracuseStep 1109675 = 1664513) B1664513
theorem B585391 : Blo 583288 585391 := bstep (se 1 (by rfl) ⟨439043, by rfl⟩ : syracuseStep 585391 = 878087) B878087
theorem B585415 : Blo 583288 585415 := bstep (se 1 (by rfl) ⟨439061, by rfl⟩ : syracuseStep 585415 = 878123) B878123
theorem B585435 : Blo 583288 585435 := bstep (se 1 (by rfl) ⟨439076, by rfl⟩ : syracuseStep 585435 = 878153) B878153
theorem B22802141 : Blo 583288 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B1404665 : Blo 583288 1404665 := bstep (se 2 (by rfl) ⟨526749, by rfl⟩ : syracuseStep 1404665 = 1053499) B1053499
theorem B585511 : Blo 583288 585511 := bstep (se 1 (by rfl) ⟨439133, by rfl⟩ : syracuseStep 585511 = 878267) B878267
theorem B585551 : Blo 583288 585551 := bstep (se 1 (by rfl) ⟨439163, by rfl⟩ : syracuseStep 585551 = 878327) B878327
theorem B585567 : Blo 583288 585567 := bstep (se 1 (by rfl) ⟨439175, by rfl⟩ : syracuseStep 585567 = 878351) B878351
theorem B585595 : Blo 583288 585595 := bstep (se 1 (by rfl) ⟨439196, by rfl⟩ : syracuseStep 585595 = 878393) B878393
theorem B585647 : Blo 583288 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B880559 : Blo 583288 880559 := bstep (se 1 (by rfl) ⟨660419, by rfl⟩ : syracuseStep 880559 = 1320839) B1320839
theorem B585671 : Blo 583288 585671 := bstep (se 1 (by rfl) ⟨439253, by rfl⟩ : syracuseStep 585671 = 878507) B878507
theorem B585691 : Blo 583288 585691 := bstep (se 1 (by rfl) ⟨439268, by rfl⟩ : syracuseStep 585691 = 878537) B878537
theorem B880649 : Blo 583288 880649 := bstep (se 2 (by rfl) ⟨330243, by rfl⟩ : syracuseStep 880649 = 660487) B660487
theorem B585767 : Blo 583288 585767 := bstep (se 1 (by rfl) ⟨439325, by rfl⟩ : syracuseStep 585767 = 878651) B878651
theorem B880679 : Blo 583288 880679 := bstep (se 1 (by rfl) ⟨660509, by rfl⟩ : syracuseStep 880679 = 1321019) B1321019
theorem B585807 : Blo 583288 585807 := bstep (se 1 (by rfl) ⟨439355, by rfl⟩ : syracuseStep 585807 = 878711) B878711
theorem B585823 : Blo 583288 585823 := bstep (se 1 (by rfl) ⟨439367, by rfl⟩ : syracuseStep 585823 = 878735) B878735
theorem B585851 : Blo 583288 585851 := bstep (se 1 (by rfl) ⟨439388, by rfl⟩ : syracuseStep 585851 = 878777) B878777
theorem B880763 : Blo 583288 880763 := bstep (se 1 (by rfl) ⟨660572, by rfl⟩ : syracuseStep 880763 = 1321145) B1321145
theorem B585903 : Blo 583288 585903 := bstep (se 1 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 585903 = 878855) B878855
theorem B585927 : Blo 583288 585927 := bstep (se 1 (by rfl) ⟨439445, by rfl⟩ : syracuseStep 585927 = 878891) B878891
theorem B585947 : Blo 583288 585947 := bstep (se 1 (by rfl) ⟨439460, by rfl⟩ : syracuseStep 585947 = 878921) B878921
theorem B880889 : Blo 583288 880889 := bstep (se 2 (by rfl) ⟨330333, by rfl⟩ : syracuseStep 880889 = 660667) B660667
theorem B586023 : Blo 583288 586023 := bstep (se 1 (by rfl) ⟨439517, by rfl⟩ : syracuseStep 586023 = 879035) B879035
theorem B586063 : Blo 583288 586063 := bstep (se 1 (by rfl) ⟨439547, by rfl⟩ : syracuseStep 586063 = 879095) B879095
theorem B586079 : Blo 583288 586079 := bstep (se 1 (by rfl) ⟨439559, by rfl⟩ : syracuseStep 586079 = 879119) B879119
theorem B586107 : Blo 583288 586107 := bstep (se 1 (by rfl) ⟨439580, by rfl⟩ : syracuseStep 586107 = 879161) B879161
theorem B586159 : Blo 583288 586159 := bstep (se 1 (by rfl) ⟨439619, by rfl⟩ : syracuseStep 586159 = 879239) B879239
theorem B586183 : Blo 583288 586183 := bstep (se 1 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 586183 = 879275) B879275
theorem B586203 : Blo 583288 586203 := bstep (se 1 (by rfl) ⟨439652, by rfl⟩ : syracuseStep 586203 = 879305) B879305
theorem B586279 : Blo 583288 586279 := bstep (se 1 (by rfl) ⟨439709, by rfl⟩ : syracuseStep 586279 = 879419) B879419
theorem B586319 : Blo 583288 586319 := bstep (se 1 (by rfl) ⟨439739, by rfl⟩ : syracuseStep 586319 = 879479) B879479
theorem B586335 : Blo 583288 586335 := bstep (se 1 (by rfl) ⟨439751, by rfl⟩ : syracuseStep 586335 = 879503) B879503
theorem B586363 : Blo 583288 586363 := bstep (se 1 (by rfl) ⟨439772, by rfl⟩ : syracuseStep 586363 = 879545) B879545
theorem B586415 : Blo 583288 586415 := bstep (se 1 (by rfl) ⟨439811, by rfl⟩ : syracuseStep 586415 = 879623) B879623
theorem B586439 : Blo 583288 586439 := bstep (se 1 (by rfl) ⟨439829, by rfl⟩ : syracuseStep 586439 = 879659) B879659
theorem B586459 : Blo 583288 586459 := bstep (se 1 (by rfl) ⟨439844, by rfl⟩ : syracuseStep 586459 = 879689) B879689
theorem B586535 : Blo 583288 586535 := bstep (se 1 (by rfl) ⟨439901, by rfl⟩ : syracuseStep 586535 = 879803) B879803
theorem B586575 : Blo 583288 586575 := bstep (se 1 (by rfl) ⟨439931, by rfl⟩ : syracuseStep 586575 = 879863) B879863
theorem B586591 : Blo 583288 586591 := bstep (se 1 (by rfl) ⟨439943, by rfl⟩ : syracuseStep 586591 = 879887) B879887
theorem B2225015 : Blo 583288 2225015 := bstep (se 1 (by rfl) ⟨1668761, by rfl⟩ : syracuseStep 2225015 = 3337523) B3337523
theorem B586619 : Blo 583288 586619 := bstep (se 1 (by rfl) ⟨439964, by rfl⟩ : syracuseStep 586619 = 879929) B879929
theorem B586671 : Blo 583288 586671 := bstep (se 1 (by rfl) ⟨440003, by rfl⟩ : syracuseStep 586671 = 880007) B880007
theorem B586695 : Blo 583288 586695 := bstep (se 1 (by rfl) ⟨440021, by rfl⟩ : syracuseStep 586695 = 880043) B880043
theorem B586715 : Blo 583288 586715 := bstep (se 1 (by rfl) ⟨440036, by rfl⟩ : syracuseStep 586715 = 880073) B880073
theorem B586791 : Blo 583288 586791 := bstep (se 1 (by rfl) ⟨440093, by rfl⟩ : syracuseStep 586791 = 880187) B880187
theorem B586831 : Blo 583288 586831 := bstep (se 1 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 586831 = 880247) B880247
theorem B586847 : Blo 583288 586847 := bstep (se 1 (by rfl) ⟨440135, by rfl⟩ : syracuseStep 586847 = 880271) B880271
theorem B586875 : Blo 583288 586875 := bstep (se 1 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 586875 = 880313) B880313
theorem B586927 : Blo 583288 586927 := bstep (se 1 (by rfl) ⟨440195, by rfl⟩ : syracuseStep 586927 = 880391) B880391
theorem B586951 : Blo 583288 586951 := bstep (se 1 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 586951 = 880427) B880427
theorem B586971 : Blo 583288 586971 := bstep (se 1 (by rfl) ⟨440228, by rfl⟩ : syracuseStep 586971 = 880457) B880457
theorem B587047 : Blo 583288 587047 := bstep (se 1 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 587047 = 880571) B880571
theorem B587087 : Blo 583288 587087 := bstep (se 1 (by rfl) ⟨440315, by rfl⟩ : syracuseStep 587087 = 880631) B880631
theorem B1111391 : Blo 583288 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B587103 : Blo 583288 587103 := bstep (se 1 (by rfl) ⟨440327, by rfl⟩ : syracuseStep 587103 = 880655) B880655
theorem B17986931 : Blo 583288 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B15037811 : Blo 583288 15037811 := bstep (se 1 (by rfl) ⟨11278358, by rfl⟩ : syracuseStep 15037811 = 22556717) B22556717
theorem B587131 : Blo 583288 587131 := bstep (se 1 (by rfl) ⟨440348, by rfl⟩ : syracuseStep 587131 = 880697) B880697
theorem B587183 : Blo 583288 587183 := bstep (se 1 (by rfl) ⟨440387, by rfl⟩ : syracuseStep 587183 = 880775) B880775
theorem B587207 : Blo 583288 587207 := bstep (se 1 (by rfl) ⟨440405, by rfl⟩ : syracuseStep 587207 = 880811) B880811
theorem B587227 : Blo 583288 587227 := bstep (se 1 (by rfl) ⟨440420, by rfl⟩ : syracuseStep 587227 = 880841) B880841
theorem B1406489 : Blo 583288 1406489 := bstep (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) B1054867
theorem B2258579 : Blo 583288 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B1406663 : Blo 583288 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B1111801 : Blo 583288 1111801 := bstep (se 2 (by rfl) ⟨416925, by rfl⟩ : syracuseStep 1111801 = 833851) B833851
theorem B2225987 : Blo 583288 2225987 := bstep (se 1 (by rfl) ⟨1669490, by rfl⟩ : syracuseStep 2225987 = 3338981) B3338981
theorem B1112143 : Blo 583288 1112143 := bstep (se 1 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 1112143 = 1668215) B1668215
theorem B1112393 : Blo 583288 1112393 := bstep (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) B834295
theorem B1669501 : Blo 583288 1669501 := bstep (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) B626063
theorem B13728203 : Blo 583288 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B1407451 : Blo 583288 1407451 := bstep (se 1 (by rfl) ⟨1055588, by rfl⟩ : syracuseStep 1407451 = 2111177) B2111177
theorem B5994989 : Blo 583288 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B1997345 : Blo 583288 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1669729 : Blo 583288 1669729 := bstep (se 2 (by rfl) ⟨626148, by rfl⟩ : syracuseStep 1669729 = 1252297) B1252297
theorem B2226973 : Blo 583288 2226973 := bstep (se 3 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 2226973 = 835115) B835115
theorem B1670071 : Blo 583288 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B1113259 : Blo 583288 1113259 := bstep (se 1 (by rfl) ⟨834944, by rfl⟩ : syracuseStep 1113259 = 1669889) B1669889
theorem B1113335 : Blo 583288 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B1113563 : Blo 583288 1113563 := bstep (se 1 (by rfl) ⟨835172, by rfl⟩ : syracuseStep 1113563 = 1670345) B1670345
theorem B2817575 : Blo 583288 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B4226849 : Blo 583288 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B16023415 : Blo 583288 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B14221241 : Blo 583288 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B5636105 : Blo 583288 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B62357521 : Blo 583288 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B45547541 : Blo 583288 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B2228249 : Blo 583288 2228249 := bstep (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) B1671187
theorem B9470189 : Blo 583288 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B2195819 : Blo 583288 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B1114535 : Blo 583288 1114535 := bstep (se 1 (by rfl) ⟨835901, by rfl⟩ : syracuseStep 1114535 = 1671803) B1671803
theorem B2228705 : Blo 583288 2228705 := bstep (se 2 (by rfl) ⟨835764, by rfl⟩ : syracuseStep 2228705 = 1671529) B1671529
theorem B623099 : Blo 583288 623099 := bstep (se 1 (by rfl) ⟨467324, by rfl⟩ : syracuseStep 623099 = 934649) B934649
theorem B12649061 : Blo 583288 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B4457105 : Blo 583288 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B1409719 : Blo 583288 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B656671 : Blo 583288 656671 := bstep (se 1 (by rfl) ⟨492503, by rfl⟩ : syracuseStep 656671 = 985007) B985007
theorem B1410335 : Blo 583288 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B984359 : Blo 583288 984359 := bstep (se 1 (by rfl) ⟨738269, by rfl⟩ : syracuseStep 984359 = 1476539) B1476539
theorem B1246727 : Blo 583288 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B3999289 : Blo 583288 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B656959 : Blo 583288 656959 := bstep (se 1 (by rfl) ⟨492719, by rfl⟩ : syracuseStep 656959 = 985439) B985439
theorem B5637721 : Blo 583288 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B984811 : Blo 583288 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B1312559 : Blo 583288 1312559 := bstep (se 1 (by rfl) ⟨984419, by rfl⟩ : syracuseStep 1312559 = 1968839) B1968839
theorem B5015681 : Blo 583288 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B6424771 : Blo 583288 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B1607945 : Blo 583288 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B1313135 : Blo 583288 1313135 := bstep (se 1 (by rfl) ⟨984851, by rfl⟩ : syracuseStep 1313135 = 1969703) B1969703
theorem B657787 : Blo 583288 657787 := bstep (se 1 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 657787 = 986681) B986681
theorem B1313207 : Blo 583288 1313207 := bstep (se 1 (by rfl) ⟨984905, by rfl⟩ : syracuseStep 1313207 = 1969811) B1969811
theorem B1477075 : Blo 583288 1477075 := bstep (se 1 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 1477075 = 2215613) B2215613
theorem B4753907 : Blo 583288 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B1313351 : Blo 583288 1313351 := bstep (se 1 (by rfl) ⟨985013, by rfl⟩ : syracuseStep 1313351 = 1970027) B1970027
theorem B1313387 : Blo 583288 1313387 := bstep (se 1 (by rfl) ⟨985040, by rfl⟩ : syracuseStep 1313387 = 1970081) B1970081
theorem B985783 : Blo 583288 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B658255 : Blo 583288 658255 := bstep (se 1 (by rfl) ⟨493691, by rfl⟩ : syracuseStep 658255 = 987383) B987383
theorem B986087 : Blo 583288 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B1313783 : Blo 583288 1313783 := bstep (se 1 (by rfl) ⟨985337, by rfl⟩ : syracuseStep 1313783 = 1970675) B1970675
theorem B4459535 : Blo 583288 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B12651659 : Blo 583288 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B2493659 : Blo 583288 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B658651 : Blo 583288 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B1477865 : Blo 583288 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B2886943 : Blo 583288 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1314143 : Blo 583288 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B1478027 : Blo 583288 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1969595 : Blo 583288 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B658939 : Blo 583288 658939 := bstep (se 1 (by rfl) ⟨494204, by rfl⟩ : syracuseStep 658939 = 988409) B988409
theorem B659119 : Blo 583288 659119 := bstep (se 1 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 659119 = 988679) B988679
theorem B1314539 : Blo 583288 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B1314665 : Blo 583288 1314665 := bstep (se 2 (by rfl) ⟨492999, by rfl⟩ : syracuseStep 1314665 = 985999) B985999
theorem B659407 : Blo 583288 659407 := bstep (se 1 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 659407 = 989111) B989111
theorem B987241 : Blo 583288 987241 := bstep (se 2 (by rfl) ⟨370215, by rfl⟩ : syracuseStep 987241 = 740431) B740431
theorem B659803 : Blo 583288 659803 := bstep (se 1 (by rfl) ⟨494852, by rfl⟩ : syracuseStep 659803 = 989705) B989705
theorem B1479019 : Blo 583288 1479019 := bstep (se 1 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 1479019 = 2218529) B2218529
theorem B659911 : Blo 583288 659911 := bstep (se 1 (by rfl) ⟨494933, by rfl⟩ : syracuseStep 659911 = 989867) B989867
theorem B1479343 : Blo 583288 1479343 := bstep (se 1 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 1479343 = 2219015) B2219015
theorem B1315511 : Blo 583288 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B660271 : Blo 583288 660271 := bstep (se 1 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 660271 = 990407) B990407
theorem B1315727 : Blo 583288 1315727 := bstep (se 1 (by rfl) ⟨986795, by rfl⟩ : syracuseStep 1315727 = 1973591) B1973591
theorem B660379 : Blo 583288 660379 := bstep (se 1 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 660379 = 990569) B990569
theorem B1479667 : Blo 583288 1479667 := bstep (se 1 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 1479667 = 2219501) B2219501
theorem B2954231 : Blo 583288 2954231 := bstep (se 1 (by rfl) ⟨2215673, by rfl⟩ : syracuseStep 2954231 = 4431347) B4431347
theorem B11211929 : Blo 583288 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B1250657 : Blo 583288 1250657 := bstep (se 2 (by rfl) ⟨468996, by rfl⟩ : syracuseStep 1250657 = 937993) B937993
theorem B1054075 : Blo 583288 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B1250759 : Blo 583288 1250759 := bstep (se 1 (by rfl) ⟨938069, by rfl⟩ : syracuseStep 1250759 = 1876139) B1876139
theorem B1316447 : Blo 583288 1316447 := bstep (se 1 (by rfl) ⟨987335, by rfl⟩ : syracuseStep 1316447 = 1974671) B1974671
theorem B5641913 : Blo 583288 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B2496187 : Blo 583288 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B1480427 : Blo 583288 1480427 := bstep (se 1 (by rfl) ⟨1110320, by rfl⟩ : syracuseStep 1480427 = 2220641) B2220641
theorem B988969 : Blo 583288 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B1251119 : Blo 583288 1251119 := bstep (se 1 (by rfl) ⟨938339, by rfl⟩ : syracuseStep 1251119 = 1876679) B1876679
theorem B1316663 : Blo 583288 1316663 := bstep (se 1 (by rfl) ⟨987497, by rfl⟩ : syracuseStep 1316663 = 1974995) B1974995
theorem B5707705 : Blo 583288 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B1316969 : Blo 583288 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B2660791 : Blo 583288 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B4430375 : Blo 583288 4430375 := bstep (se 1 (by rfl) ⟨3322781, by rfl⟩ : syracuseStep 4430375 = 6645563) B6645563
theorem B989759 : Blo 583288 989759 := bstep (se 1 (by rfl) ⟨742319, by rfl⟩ : syracuseStep 989759 = 1484639) B1484639
theorem B1481287 : Blo 583288 1481287 := bstep (se 1 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 1481287 = 2221931) B2221931
theorem B1317455 : Blo 583288 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B793183 : Blo 583288 793183 := bstep (se 1 (by rfl) ⟨594887, by rfl⟩ : syracuseStep 793183 = 1189775) B1189775
theorem B1481399 : Blo 583288 1481399 := bstep (se 1 (by rfl) ⟨1111049, by rfl⟩ : syracuseStep 1481399 = 2222099) B2222099
theorem B1317599 : Blo 583288 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B2956175 : Blo 583288 2956175 := bstep (se 1 (by rfl) ⟨2217131, by rfl⟩ : syracuseStep 2956175 = 4434263) B4434263
theorem B1317851 : Blo 583288 1317851 := bstep (se 1 (by rfl) ⟨988388, by rfl⟩ : syracuseStep 1317851 = 1976777) B1976777
theorem B5610545 : Blo 583288 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B2497675 : Blo 583288 2497675 := bstep (se 1 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 2497675 = 3746513) B3746513
theorem B1318031 : Blo 583288 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B1055963 : Blo 583288 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B990427 : Blo 583288 990427 := bstep (se 1 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 990427 = 1485641) B1485641
theorem B3742949 : Blo 583288 3742949 := bstep (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) B701803
theorem B1318121 : Blo 583288 1318121 := bstep (se 2 (by rfl) ⟨494295, by rfl⟩ : syracuseStep 1318121 = 988591) B988591
theorem B1318175 : Blo 583288 1318175 := bstep (se 1 (by rfl) ⟨988631, by rfl⟩ : syracuseStep 1318175 = 1977263) B1977263
theorem B2104775 : Blo 583288 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B1973753 : Blo 583288 1973753 := bstep (se 2 (by rfl) ⟨740157, by rfl⟩ : syracuseStep 1973753 = 1480315) B1480315
theorem B3382879 : Blo 583288 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B1482401 : Blo 583288 1482401 := bstep (se 2 (by rfl) ⟨555900, by rfl⟩ : syracuseStep 1482401 = 1111801) B1111801
theorem B1974023 : Blo 583288 1974023 := bstep (se 1 (by rfl) ⟨1480517, by rfl⟩ : syracuseStep 1974023 = 2961035) B2961035
theorem B1318697 : Blo 583288 1318697 := bstep (se 2 (by rfl) ⟨494511, by rfl⟩ : syracuseStep 1318697 = 989023) B989023
theorem B1974077 : Blo 583288 1974077 := bstep (se 3 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 1974077 = 740279) B740279
theorem B4759357 : Blo 583288 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B1482857 : Blo 583288 1482857 := bstep (se 2 (by rfl) ⟨556071, by rfl⟩ : syracuseStep 1482857 = 1112143) B1112143
theorem B1483343 : Blo 583288 1483343 := bstep (se 1 (by rfl) ⟨1112507, by rfl⟩ : syracuseStep 1483343 = 2225015) B2225015
theorem B1876601 : Blo 583288 1876601 := bstep (se 2 (by rfl) ⟨703725, by rfl⟩ : syracuseStep 1876601 = 1407451) B1407451
theorem B1319759 : Blo 583288 1319759 := bstep (se 1 (by rfl) ⟨989819, by rfl⟩ : syracuseStep 1319759 = 1979639) B1979639
theorem B5350337 : Blo 583288 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B2958281 : Blo 583288 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B1319975 : Blo 583288 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B1483991 : Blo 583288 1483991 := bstep (se 1 (by rfl) ⟨1112993, by rfl⟩ : syracuseStep 1483991 = 2225987) B2225987
theorem B1320155 : Blo 583288 1320155 := bstep (se 1 (by rfl) ⟨990116, by rfl⟩ : syracuseStep 1320155 = 1980233) B1980233
theorem B11412859 : Blo 583288 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B1320353 : Blo 583288 1320353 := bstep (se 2 (by rfl) ⟨495132, by rfl⟩ : syracuseStep 1320353 = 990265) B990265
theorem B1582649 : Blo 583288 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B1484345 : Blo 583288 1484345 := bstep (se 2 (by rfl) ⟨556629, by rfl⟩ : syracuseStep 1484345 = 1113259) B1113259
theorem B9152135 : Blo 583288 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B1320911 : Blo 583288 1320911 := bstep (se 1 (by rfl) ⟨990683, by rfl⟩ : syracuseStep 1320911 = 1981367) B1981367
theorem B3745921 : Blo 583288 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B1321289 : Blo 583288 1321289 := bstep (se 2 (by rfl) ⟨495483, by rfl⟩ : syracuseStep 1321289 = 990967) B990967
theorem B1321307 : Blo 583288 1321307 := bstep (se 1 (by rfl) ⟨990980, by rfl⟩ : syracuseStep 1321307 = 1981961) B1981961
theorem B1878383 : Blo 583288 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B12003713 : Blo 583288 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B8464769 : Blo 583288 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B1976939 : Blo 583288 1976939 := bstep (se 1 (by rfl) ⟨1482704, by rfl⟩ : syracuseStep 1976939 = 2965409) B2965409
theorem B9480827 : Blo 583288 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B6761083 : Blo 583288 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B6335603 : Blo 583288 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B1977533 : Blo 583288 1977533 := bstep (se 3 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 1977533 = 741575) B741575
theorem B1584377 : Blo 583288 1584377 := bstep (se 2 (by rfl) ⟨594141, by rfl⟩ : syracuseStep 1584377 = 1188283) B1188283
theorem B2502407 : Blo 583288 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B700871 : Blo 583288 700871 := bstep (se 1 (by rfl) ⟨525653, by rfl⟩ : syracuseStep 700871 = 1051307) B1051307
theorem B1585847 : Blo 583288 1585847 := bstep (se 1 (by rfl) ⟨1189385, by rfl⟩ : syracuseStep 1585847 = 2378771) B2378771
theorem B2962169 : Blo 583288 2962169 := bstep (se 2 (by rfl) ⟨1110813, by rfl⟩ : syracuseStep 2962169 = 2221627) B2221627
theorem B1357019 : Blo 583288 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B2503979 : Blo 583288 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B4208165 : Blo 583288 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B3159737 : Blo 583288 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B4273975 : Blo 583288 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B3749921 : Blo 583288 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B1980449 : Blo 583288 1980449 := bstep (se 2 (by rfl) ⟨742668, by rfl⟩ : syracuseStep 1980449 = 1485337) B1485337
theorem B2504783 : Blo 583288 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B4438151 : Blo 583288 4438151 := bstep (se 1 (by rfl) ⟨3328613, by rfl⟩ : syracuseStep 4438151 = 6657227) B6657227
theorem B2374217 : Blo 583288 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B24394391 : Blo 583288 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B3750637 : Blo 583288 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B3161531 : Blo 583288 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B2964923 : Blo 583288 2964923 := bstep (se 1 (by rfl) ⟨2223692, by rfl⟩ : syracuseStep 2964923 = 4447385) B4447385
theorem B934507 : Blo 583288 934507 := bstep (se 1 (by rfl) ⟨700880, by rfl⟩ : syracuseStep 934507 = 1401761) B1401761
theorem B3326609 : Blo 583288 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2966219 : Blo 583288 2966219 := bstep (se 1 (by rfl) ⟨2224664, by rfl⟩ : syracuseStep 2966219 = 4449329) B4449329
theorem B705359 : Blo 583288 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B2966381 : Blo 583288 2966381 := bstep (se 3 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 2966381 = 1112393) B1112393
theorem B1000439 : Blo 583288 1000439 := bstep (se 1 (by rfl) ⟨750329, by rfl⟩ : syracuseStep 1000439 = 1500659) B1500659
theorem B2376695 : Blo 583288 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B4211855 : Blo 583288 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B78169315 : Blo 583288 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B5621035 : Blo 583288 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B4572569 : Blo 583288 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B738811 : Blo 583288 738811 := bstep (se 1 (by rfl) ⟨554108, by rfl⟩ : syracuseStep 738811 = 1108217) B1108217
theorem B739039 : Blo 583288 739039 := bstep (se 1 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 739039 = 1108559) B1108559
theorem B935687 : Blo 583288 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B4442039 : Blo 583288 4442039 := bstep (se 1 (by rfl) ⟨3331529, by rfl⟩ : syracuseStep 4442039 = 6663059) B6663059
theorem B3164345 : Blo 583288 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B739783 : Blo 583288 739783 := bstep (se 1 (by rfl) ⟨554837, by rfl⟩ : syracuseStep 739783 = 1109675) B1109675
theorem B936443 : Blo 583288 936443 := bstep (se 1 (by rfl) ⟨702332, by rfl⟩ : syracuseStep 936443 = 1404665) B1404665
theorem B2379145 : Blo 583288 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B740927 : Blo 583288 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B2805329 : Blo 583288 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B2969297 : Blo 583288 2969297 := bstep (se 2 (by rfl) ⟨1113486, by rfl⟩ : syracuseStep 2969297 = 2226973) B2226973
theorem B937775 : Blo 583288 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B1331563 : Blo 583288 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B5624417 : Blo 583288 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B742223 : Blo 583288 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B742375 : Blo 583288 742375 := bstep (se 1 (by rfl) ⟨556781, by rfl⟩ : syracuseStep 742375 = 1113563) B1113563
theorem B4740221 : Blo 583288 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B4445441 : Blo 583288 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B677243 : Blo 583288 677243 := bstep (se 1 (by rfl) ⟨507932, by rfl⟩ : syracuseStep 677243 = 1015865) B1015865
theorem B1922617 : Blo 583288 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B43439921 : Blo 583288 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B2971727 : Blo 583288 2971727 := bstep (se 1 (by rfl) ⟨2228795, by rfl⟩ : syracuseStep 2971727 = 4457591) B4457591
theorem B875003 : Blo 583288 875003 := bstep (se 1 (by rfl) ⟨656252, by rfl⟩ : syracuseStep 875003 = 1312505) B1312505
theorem B875129 : Blo 583288 875129 := bstep (se 2 (by rfl) ⟨328173, by rfl⟩ : syracuseStep 875129 = 656347) B656347
theorem B875183 : Blo 583288 875183 := bstep (se 1 (by rfl) ⟨656387, by rfl⟩ : syracuseStep 875183 = 1312775) B1312775
theorem B875231 : Blo 583288 875231 := bstep (se 1 (by rfl) ⟨656423, by rfl⟩ : syracuseStep 875231 = 1312847) B1312847
theorem B9001847 : Blo 583288 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B875495 : Blo 583288 875495 := bstep (se 1 (by rfl) ⟨656621, by rfl⟩ : syracuseStep 875495 = 1313243) B1313243
theorem B1203175 : Blo 583288 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B2677799 : Blo 583288 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B2219197 : Blo 583288 2219197 := bstep (se 3 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 2219197 = 832199) B832199
theorem B2972861 : Blo 583288 2972861 := bstep (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) B1114823
theorem B875753 : Blo 583288 875753 := bstep (se 2 (by rfl) ⟨328407, by rfl⟩ : syracuseStep 875753 = 656815) B656815
theorem B875807 : Blo 583288 875807 := bstep (se 1 (by rfl) ⟨656855, by rfl⟩ : syracuseStep 875807 = 1313711) B1313711
theorem B23158133 : Blo 583288 23158133 := bstep (se 5 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 23158133 = 2171075) B2171075
theorem B875975 : Blo 583288 875975 := bstep (se 1 (by rfl) ⟨656981, by rfl⟩ : syracuseStep 875975 = 1313963) B1313963
theorem B876329 : Blo 583288 876329 := bstep (se 2 (by rfl) ⟨328623, by rfl⟩ : syracuseStep 876329 = 657247) B657247
theorem B876335 : Blo 583288 876335 := bstep (se 1 (by rfl) ⟨657251, by rfl⟩ : syracuseStep 876335 = 1314503) B1314503
theorem B2809673 : Blo 583288 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B5693651 : Blo 583288 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B3334355 : Blo 583288 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B876809 : Blo 583288 876809 := bstep (se 2 (by rfl) ⟨328803, by rfl⟩ : syracuseStep 876809 = 657607) B657607
theorem B876911 : Blo 583288 876911 := bstep (se 1 (by rfl) ⟨657683, by rfl⟩ : syracuseStep 876911 = 1315367) B1315367
theorem B86794649 : Blo 583288 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B5988833 : Blo 583288 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B877127 : Blo 583288 877127 := bstep (se 1 (by rfl) ⟨657845, by rfl⟩ : syracuseStep 877127 = 1315691) B1315691
theorem B877163 : Blo 583288 877163 := bstep (se 1 (by rfl) ⟨657872, by rfl⟩ : syracuseStep 877163 = 1315745) B1315745
theorem B877391 : Blo 583288 877391 := bstep (se 1 (by rfl) ⟨658043, by rfl⟩ : syracuseStep 877391 = 1316087) B1316087
theorem B877787 : Blo 583288 877787 := bstep (se 1 (by rfl) ⟨658340, by rfl⟩ : syracuseStep 877787 = 1316681) B1316681
theorem B877961 : Blo 583288 877961 := bstep (se 2 (by rfl) ⟨329235, by rfl⟩ : syracuseStep 877961 = 658471) B658471
theorem B583391 : Blo 583288 583391 := bstep (se 1 (by rfl) ⟨437543, by rfl⟩ : syracuseStep 583391 = 875087) B875087
theorem B878315 : Blo 583288 878315 := bstep (se 1 (by rfl) ⟨658736, by rfl⟩ : syracuseStep 878315 = 1317473) B1317473
theorem B12871457 : Blo 583288 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B583471 : Blo 583288 583471 := bstep (se 1 (by rfl) ⟨437603, by rfl⟩ : syracuseStep 583471 = 875207) B875207
theorem B1107769 : Blo 583288 1107769 := bstep (se 2 (by rfl) ⟨415413, by rfl⟩ : syracuseStep 1107769 = 830827) B830827
theorem B583579 : Blo 583288 583579 := bstep (se 1 (by rfl) ⟨437684, by rfl⟩ : syracuseStep 583579 = 875369) B875369
theorem B583631 : Blo 583288 583631 := bstep (se 1 (by rfl) ⟨437723, by rfl⟩ : syracuseStep 583631 = 875447) B875447
theorem B878543 : Blo 583288 878543 := bstep (se 1 (by rfl) ⟨658907, by rfl⟩ : syracuseStep 878543 = 1317815) B1317815
theorem B583655 : Blo 583288 583655 := bstep (se 1 (by rfl) ⟨437741, by rfl⟩ : syracuseStep 583655 = 875483) B875483
theorem B2222113 : Blo 583288 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B1108073 : Blo 583288 1108073 := bstep (se 2 (by rfl) ⟨415527, by rfl⟩ : syracuseStep 1108073 = 831055) B831055
theorem B583967 : Blo 583288 583967 := bstep (se 1 (by rfl) ⟨437975, by rfl⟩ : syracuseStep 583967 = 875951) B875951
theorem B584027 : Blo 583288 584027 := bstep (se 1 (by rfl) ⟨438020, by rfl⟩ : syracuseStep 584027 = 876041) B876041
theorem B878939 : Blo 583288 878939 := bstep (se 1 (by rfl) ⟨659204, by rfl⟩ : syracuseStep 878939 = 1318409) B1318409
theorem B584047 : Blo 583288 584047 := bstep (se 1 (by rfl) ⟨438035, by rfl⟩ : syracuseStep 584047 = 876071) B876071
theorem B584103 : Blo 583288 584103 := bstep (se 1 (by rfl) ⟨438077, by rfl⟩ : syracuseStep 584103 = 876155) B876155
theorem B34236845 : Blo 583288 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B1108475 : Blo 583288 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B584187 : Blo 583288 584187 := bstep (se 1 (by rfl) ⟨438140, by rfl⟩ : syracuseStep 584187 = 876281) B876281
theorem B584255 : Blo 583288 584255 := bstep (se 1 (by rfl) ⟨438191, by rfl⟩ : syracuseStep 584255 = 876383) B876383
theorem B879167 : Blo 583288 879167 := bstep (se 1 (by rfl) ⟨659375, by rfl⟩ : syracuseStep 879167 = 1318751) B1318751
theorem B584263 : Blo 583288 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B10644047 : Blo 583288 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B1501867 : Blo 583288 1501867 := bstep (se 1 (by rfl) ⟨1126400, by rfl⟩ : syracuseStep 1501867 = 2252801) B2252801
theorem B879287 : Blo 583288 879287 := bstep (se 1 (by rfl) ⟨659465, by rfl⟩ : syracuseStep 879287 = 1318931) B1318931
theorem B1108703 : Blo 583288 1108703 := bstep (se 1 (by rfl) ⟨831527, by rfl⟩ : syracuseStep 1108703 = 1663055) B1663055
theorem B584415 : Blo 583288 584415 := bstep (se 1 (by rfl) ⟨438311, by rfl⟩ : syracuseStep 584415 = 876623) B876623
theorem B584495 : Blo 583288 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B584603 : Blo 583288 584603 := bstep (se 1 (by rfl) ⟨438452, by rfl⟩ : syracuseStep 584603 = 876905) B876905
theorem B1665947 : Blo 583288 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B879515 : Blo 583288 879515 := bstep (se 1 (by rfl) ⟨659636, by rfl⟩ : syracuseStep 879515 = 1319273) B1319273
theorem B584655 : Blo 583288 584655 := bstep (se 1 (by rfl) ⟨438491, by rfl⟩ : syracuseStep 584655 = 876983) B876983
theorem B1403867 : Blo 583288 1403867 := bstep (se 1 (by rfl) ⟨1052900, by rfl⟩ : syracuseStep 1403867 = 2105801) B2105801
theorem B584679 : Blo 583288 584679 := bstep (se 1 (by rfl) ⟨438509, by rfl⟩ : syracuseStep 584679 = 877019) B877019
theorem B23981275 : Blo 583288 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B584991 : Blo 583288 584991 := bstep (se 1 (by rfl) ⟨438743, by rfl⟩ : syracuseStep 584991 = 877487) B877487
theorem B879911 : Blo 583288 879911 := bstep (se 1 (by rfl) ⟨659933, by rfl⟩ : syracuseStep 879911 = 1319867) B1319867
theorem B585051 : Blo 583288 585051 := bstep (se 1 (by rfl) ⟨438788, by rfl⟩ : syracuseStep 585051 = 877577) B877577
theorem B585071 : Blo 583288 585071 := bstep (se 1 (by rfl) ⟨438803, by rfl⟩ : syracuseStep 585071 = 877607) B877607
theorem B1109371 : Blo 583288 1109371 := bstep (se 1 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 1109371 = 1664057) B1664057
theorem B879995 : Blo 583288 879995 := bstep (se 1 (by rfl) ⟨659996, by rfl⟩ : syracuseStep 879995 = 1319993) B1319993
theorem B585127 : Blo 583288 585127 := bstep (se 1 (by rfl) ⟨438845, by rfl⟩ : syracuseStep 585127 = 877691) B877691
theorem B1109447 : Blo 583288 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B880121 : Blo 583288 880121 := bstep (se 2 (by rfl) ⟨330045, by rfl⟩ : syracuseStep 880121 = 660091) B660091
theorem B585211 : Blo 583288 585211 := bstep (se 1 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 585211 = 877817) B877817
theorem B585279 : Blo 583288 585279 := bstep (se 1 (by rfl) ⟨438959, by rfl⟩ : syracuseStep 585279 = 877919) B877919
theorem B585287 : Blo 583288 585287 := bstep (se 1 (by rfl) ⟨438965, by rfl⟩ : syracuseStep 585287 = 877931) B877931
theorem B880223 : Blo 583288 880223 := bstep (se 1 (by rfl) ⟨660167, by rfl⟩ : syracuseStep 880223 = 1320335) B1320335
theorem B585439 : Blo 583288 585439 := bstep (se 1 (by rfl) ⟨439079, by rfl⟩ : syracuseStep 585439 = 878159) B878159
theorem B585519 : Blo 583288 585519 := bstep (se 1 (by rfl) ⟨439139, by rfl⟩ : syracuseStep 585519 = 878279) B878279
theorem B880439 : Blo 583288 880439 := bstep (se 1 (by rfl) ⟨660329, by rfl⟩ : syracuseStep 880439 = 1320659) B1320659
theorem B585627 : Blo 583288 585627 := bstep (se 1 (by rfl) ⟨439220, by rfl⟩ : syracuseStep 585627 = 878441) B878441
theorem B1666973 : Blo 583288 1666973 := bstep (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) B625115
theorem B585679 : Blo 583288 585679 := bstep (se 1 (by rfl) ⟨439259, by rfl⟩ : syracuseStep 585679 = 878519) B878519
theorem B585703 : Blo 583288 585703 := bstep (se 1 (by rfl) ⟨439277, by rfl⟩ : syracuseStep 585703 = 878555) B878555
theorem B880745 : Blo 583288 880745 := bstep (se 2 (by rfl) ⟨330279, by rfl⟩ : syracuseStep 880745 = 660559) B660559
theorem B27324533 : Blo 583288 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B586015 : Blo 583288 586015 := bstep (se 1 (by rfl) ⟨439511, by rfl⟩ : syracuseStep 586015 = 879023) B879023
theorem B586075 : Blo 583288 586075 := bstep (se 1 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 586075 = 879113) B879113
theorem B586095 : Blo 583288 586095 := bstep (se 1 (by rfl) ⟨439571, by rfl⟩ : syracuseStep 586095 = 879143) B879143
theorem B586151 : Blo 583288 586151 := bstep (se 1 (by rfl) ⟨439613, by rfl⟩ : syracuseStep 586151 = 879227) B879227
theorem B586235 : Blo 583288 586235 := bstep (se 1 (by rfl) ⟨439676, by rfl⟩ : syracuseStep 586235 = 879353) B879353
theorem B586303 : Blo 583288 586303 := bstep (se 1 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 586303 = 879455) B879455
theorem B586311 : Blo 583288 586311 := bstep (se 1 (by rfl) ⟨439733, by rfl⟩ : syracuseStep 586311 = 879467) B879467
theorem B1110601 : Blo 583288 1110601 := bstep (se 2 (by rfl) ⟨416475, by rfl⟩ : syracuseStep 1110601 = 832951) B832951
theorem B586463 : Blo 583288 586463 := bstep (se 1 (by rfl) ⟨439847, by rfl⟩ : syracuseStep 586463 = 879695) B879695
theorem B586543 : Blo 583288 586543 := bstep (se 1 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 586543 = 879815) B879815
theorem B586651 : Blo 583288 586651 := bstep (se 1 (by rfl) ⟨439988, by rfl⟩ : syracuseStep 586651 = 879977) B879977
theorem B586703 : Blo 583288 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B586727 : Blo 583288 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B1405991 : Blo 583288 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B15201427 : Blo 583288 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B1996019 : Blo 583288 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B587039 : Blo 583288 587039 := bstep (se 1 (by rfl) ⟨440279, by rfl⟩ : syracuseStep 587039 = 880559) B880559
theorem B587099 : Blo 583288 587099 := bstep (se 1 (by rfl) ⟨440324, by rfl⟩ : syracuseStep 587099 = 880649) B880649
theorem B587119 : Blo 583288 587119 := bstep (se 1 (by rfl) ⟨440339, by rfl⟩ : syracuseStep 587119 = 880679) B880679
theorem B750971 : Blo 583288 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B587175 : Blo 583288 587175 := bstep (se 1 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 587175 = 880763) B880763
theorem B587259 : Blo 583288 587259 := bstep (se 1 (by rfl) ⟨440444, by rfl⟩ : syracuseStep 587259 = 880889) B880889
theorem B2226001 : Blo 583288 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B2226305 : Blo 583288 2226305 := bstep (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) B1669729
theorem B12646637 : Blo 583288 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B11991287 : Blo 583288 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B10025207 : Blo 583288 10025207 := bstep (se 1 (by rfl) ⟨7518905, by rfl⟩ : syracuseStep 10025207 = 15037811) B15037811
theorem B1505719 : Blo 583288 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B1112545 : Blo 583288 1112545 := bstep (se 2 (by rfl) ⟨417204, by rfl⟩ : syracuseStep 1112545 = 834409) B834409
theorem B2226761 : Blo 583288 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B3996659 : Blo 583288 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B1670959 : Blo 583288 1670959 := bstep (se 1 (by rfl) ⟨1253219, by rfl⟩ : syracuseStep 1670959 = 2506439) B2506439
theorem B21364553 : Blo 583288 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B2817899 : Blo 583288 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B656239 : Blo 583288 656239 := bstep (se 1 (by rfl) ⟨492179, by rfl⟩ : syracuseStep 656239 = 984359) B984359
theorem B623791 : Blo 583288 623791 := bstep (se 1 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 623791 = 935687) B935687
theorem B1868989 : Blo 583288 1868989 := bstep (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) B700871
theorem B3343787 : Blo 583288 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B624295 : Blo 583288 624295 := bstep (se 1 (by rfl) ⟨468221, by rfl⟩ : syracuseStep 624295 = 936443) B936443
theorem B657391 : Blo 583288 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B985081 : Blo 583288 985081 := bstep (se 2 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 985081 = 738811) B738811
theorem B985243 : Blo 583288 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B985351 : Blo 583288 985351 := bstep (se 1 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 985351 = 1478027) B1478027
theorem B1313063 : Blo 583288 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B985385 : Blo 583288 985385 := bstep (se 2 (by rfl) ⟨369519, by rfl⟩ : syracuseStep 985385 = 739039) B739039
theorem B1313081 : Blo 583288 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B1870219 : Blo 583288 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B1477025 : Blo 583288 1477025 := bstep (se 2 (by rfl) ⟨553884, by rfl⟩ : syracuseStep 1477025 = 1107769) B1107769
theorem B4984037 : Blo 583288 4984037 := bstep (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) B934507
theorem B986377 : Blo 583288 986377 := bstep (se 2 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 986377 = 739783) B739783
theorem B1969433 : Blo 583288 1969433 := bstep (se 2 (by rfl) ⟨738537, by rfl⟩ : syracuseStep 1969433 = 1477075) B1477075
theorem B1969487 : Blo 583288 1969487 := bstep (se 1 (by rfl) ⟨1477115, by rfl⟩ : syracuseStep 1969487 = 2954231) B2954231
theorem B7474619 : Blo 583288 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B9014777 : Blo 583288 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B2002489 : Blo 583288 2002489 := bstep (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) B1501867
theorem B1314377 : Blo 583288 1314377 := bstep (se 2 (by rfl) ⟨492891, by rfl⟩ : syracuseStep 1314377 = 985783) B985783
theorem B2002589 : Blo 583288 2002589 := bstep (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) B750971
theorem B1805981 : Blo 583288 1805981 := bstep (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) B677243
theorem B12193517 : Blo 583288 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B986951 : Blo 583288 986951 := bstep (se 1 (by rfl) ⟨740213, by rfl⟩ : syracuseStep 986951 = 1480427) B1480427
theorem B2953583 : Blo 583288 2953583 := bstep (se 1 (by rfl) ⟨2215187, by rfl⟩ : syracuseStep 2953583 = 4430375) B4430375
theorem B659839 : Blo 583288 659839 := bstep (se 1 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 659839 = 989759) B989759
theorem B987599 : Blo 583288 987599 := bstep (se 1 (by rfl) ⟨740699, by rfl⟩ : syracuseStep 987599 = 1481399) B1481399
theorem B1479161 : Blo 583288 1479161 := bstep (se 2 (by rfl) ⟨554685, by rfl⟩ : syracuseStep 1479161 = 1109371) B1109371
theorem B6001231 : Blo 583288 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B1970783 : Blo 583288 1970783 := bstep (se 1 (by rfl) ⟨1478087, by rfl⟩ : syracuseStep 1970783 = 2956175) B2956175
theorem B3740363 : Blo 583288 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B2495299 : Blo 583288 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B15438755 : Blo 583288 15438755 := bstep (se 1 (by rfl) ⟨11579066, by rfl⟩ : syracuseStep 15438755 = 23158133) B23158133
theorem B1315835 : Blo 583288 1315835 := bstep (se 1 (by rfl) ⟨986876, by rfl⟩ : syracuseStep 1315835 = 1973753) B1973753
theorem B988267 : Blo 583288 988267 := bstep (se 1 (by rfl) ⟨741200, by rfl⟩ : syracuseStep 988267 = 1482401) B1482401
theorem B1316015 : Blo 583288 1316015 := bstep (se 1 (by rfl) ⟨987011, by rfl⟩ : syracuseStep 1316015 = 1974023) B1974023
theorem B1316051 : Blo 583288 1316051 := bstep (se 1 (by rfl) ⟨987038, by rfl⟩ : syracuseStep 1316051 = 1974077) B1974077
theorem B1873115 : Blo 583288 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B988571 : Blo 583288 988571 := bstep (se 1 (by rfl) ⟨741428, by rfl⟩ : syracuseStep 988571 = 1482857) B1482857
theorem B1316321 : Blo 583288 1316321 := bstep (se 2 (by rfl) ⟨493620, by rfl⟩ : syracuseStep 1316321 = 987241) B987241
theorem B988895 : Blo 583288 988895 := bstep (se 1 (by rfl) ⟨741671, by rfl⟩ : syracuseStep 988895 = 1483343) B1483343
theorem B1251067 : Blo 583288 1251067 := bstep (se 1 (by rfl) ⟨938300, by rfl⟩ : syracuseStep 1251067 = 1876601) B1876601
theorem B1775417 : Blo 583288 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B1972025 : Blo 583288 1972025 := bstep (se 2 (by rfl) ⟨739509, by rfl⟩ : syracuseStep 1972025 = 1479019) B1479019
theorem B1972187 : Blo 583288 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B1480801 : Blo 583288 1480801 := bstep (se 2 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 1480801 = 1110601) B1110601
theorem B989327 : Blo 583288 989327 := bstep (se 1 (by rfl) ⟨741995, by rfl⟩ : syracuseStep 989327 = 1483991) B1483991
theorem B1972457 : Blo 583288 1972457 := bstep (se 2 (by rfl) ⟨739671, by rfl⟩ : syracuseStep 1972457 = 1479343) B1479343
theorem B1055099 : Blo 583288 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B989563 : Blo 583288 989563 := bstep (se 1 (by rfl) ⟨742172, by rfl⟩ : syracuseStep 989563 = 1484345) B1484345
theorem B6101423 : Blo 583288 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B989833 : Blo 583288 989833 := bstep (se 2 (by rfl) ⟨371187, by rfl⟩ : syracuseStep 989833 = 742375) B742375
theorem B1972889 : Blo 583288 1972889 := bstep (se 2 (by rfl) ⟨739833, by rfl⟩ : syracuseStep 1972889 = 1479667) B1479667
theorem B1252255 : Blo 583288 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B8002475 : Blo 583288 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B5643179 : Blo 583288 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B1317959 : Blo 583288 1317959 := bstep (se 1 (by rfl) ⟨988469, by rfl⟩ : syracuseStep 1317959 = 1976939) B1976939
theorem B2563489 : Blo 583288 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B1318355 : Blo 583288 1318355 := bstep (se 1 (by rfl) ⟨988766, by rfl⟩ : syracuseStep 1318355 = 1977533) B1977533
theorem B1056251 : Blo 583288 1056251 := bstep (se 1 (by rfl) ⟨792188, by rfl⟩ : syracuseStep 1056251 = 1584377) B1584377
theorem B1318625 : Blo 583288 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B7610273 : Blo 583288 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B10657757 : Blo 583288 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B1057231 : Blo 583288 1057231 := bstep (se 1 (by rfl) ⟨792923, by rfl⟩ : syracuseStep 1057231 = 1585847) B1585847
theorem B1974779 : Blo 583288 1974779 := bstep (se 1 (by rfl) ⟨1481084, by rfl⟩ : syracuseStep 1974779 = 2962169) B2962169
theorem B3547721 : Blo 583288 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B2007625 : Blo 583288 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B1483393 : Blo 583288 1483393 := bstep (se 2 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 1483393 = 1112545) B1112545
theorem B1975049 : Blo 583288 1975049 := bstep (se 2 (by rfl) ⟨740643, by rfl⟩ : syracuseStep 1975049 = 1481287) B1481287
theorem B1057577 : Blo 583288 1057577 := bstep (se 2 (by rfl) ⟨396591, by rfl⟩ : syracuseStep 1057577 = 793183) B793183
theorem B2106491 : Blo 583288 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B8430749 : Blo 583288 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B2499947 : Blo 583288 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B1320299 : Blo 583288 1320299 := bstep (se 1 (by rfl) ⟨990224, by rfl⟩ : syracuseStep 1320299 = 1980449) B1980449
theorem B1484203 : Blo 583288 1484203 := bstep (se 1 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 1484203 = 2226305) B2226305
theorem B2958767 : Blo 583288 2958767 := bstep (se 1 (by rfl) ⟨2219075, by rfl⟩ : syracuseStep 2958767 = 4438151) B4438151
theorem B8431091 : Blo 583288 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B1975805 : Blo 583288 1975805 := bstep (se 3 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 1975805 = 740927) B740927
theorem B2958929 : Blo 583288 2958929 := bstep (se 2 (by rfl) ⟨1109598, by rfl⟩ : syracuseStep 2958929 = 2219197) B2219197
theorem B1320569 : Blo 583288 1320569 := bstep (se 2 (by rfl) ⟨495213, by rfl⟩ : syracuseStep 1320569 = 990427) B990427
theorem B1582811 : Blo 583288 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B1484507 : Blo 583288 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B16262927 : Blo 583288 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B2500733 : Blo 583288 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B1976615 : Blo 583288 1976615 := bstep (se 1 (by rfl) ⟨1482461, by rfl⟩ : syracuseStep 1976615 = 2964923) B2964923
theorem B1878599 : Blo 583288 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B1485499 : Blo 583288 1485499 := bstep (se 1 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 1485499 = 2228249) B2228249
theorem B83143361 : Blo 583288 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B1485803 : Blo 583288 1485803 := bstep (se 1 (by rfl) ⟨1114352, by rfl⟩ : syracuseStep 1485803 = 2228705) B2228705
theorem B8432707 : Blo 583288 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B1977479 : Blo 583288 1977479 := bstep (se 1 (by rfl) ⟨1483109, by rfl⟩ : syracuseStep 1977479 = 2966219) B2966219
theorem B1977587 : Blo 583288 1977587 := bstep (se 1 (by rfl) ⟨1483190, by rfl⟩ : syracuseStep 1977587 = 2966381) B2966381
theorem B666959 : Blo 583288 666959 := bstep (se 1 (by rfl) ⟨500219, by rfl⟩ : syracuseStep 666959 = 1000439) B1000439
theorem B1584463 : Blo 583288 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B1879625 : Blo 583288 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B831151 : Blo 583288 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B2961359 : Blo 583288 2961359 := bstep (se 1 (by rfl) ⟨2221019, by rfl⟩ : syracuseStep 2961359 = 4442039) B4442039
theorem B2109563 : Blo 583288 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B15217145 : Blo 583288 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B8434439 : Blo 583288 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B7516961 : Blo 583288 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B1979261 : Blo 583288 1979261 := bstep (se 3 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 1979261 = 742223) B742223
theorem B1880957 : Blo 583288 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B1979531 : Blo 583288 1979531 := bstep (se 1 (by rfl) ⟨1484648, by rfl⟩ : syracuseStep 1979531 = 2969297) B2969297
theorem B2962817 : Blo 583288 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B4994561 : Blo 583288 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B8566361 : Blo 583288 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B3160147 : Blo 583288 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2963627 : Blo 583288 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B833771 : Blo 583288 833771 := bstep (se 1 (by rfl) ⟨625328, by rfl⟩ : syracuseStep 833771 = 1250657) B1250657
theorem B834079 : Blo 583288 834079 := bstep (se 1 (by rfl) ⟨625559, by rfl⟩ : syracuseStep 834079 = 1251119) B1251119
theorem B1981151 : Blo 583288 1981151 := bstep (se 1 (by rfl) ⟨1485863, by rfl⟩ : syracuseStep 1981151 = 2971727) B2971727
theorem B3849257 : Blo 583288 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1981907 : Blo 583288 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B703975 : Blo 583288 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B738715 : Blo 583288 738715 := bstep (se 1 (by rfl) ⟨554036, by rfl⟩ : syracuseStep 738715 = 1108073) B1108073
theorem B20268569 : Blo 583288 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B22824563 : Blo 583288 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B738983 : Blo 583288 738983 := bstep (se 1 (by rfl) ⟨554237, by rfl⟩ : syracuseStep 738983 = 1108475) B1108475
theorem B7096031 : Blo 583288 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B739135 : Blo 583288 739135 := bstep (se 1 (by rfl) ⟨554351, by rfl⟩ : syracuseStep 739135 = 1108703) B1108703
theorem B935911 : Blo 583288 935911 := bstep (se 1 (by rfl) ⟨701933, by rfl⟩ : syracuseStep 935911 = 1403867) B1403867
theorem B3328249 : Blo 583288 3328249 := bstep (se 2 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 3328249 = 2496187) B2496187
theorem B739631 : Blo 583288 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B4442525 : Blo 583288 4442525 := bstep (se 3 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 4442525 = 1665947) B1665947
theorem B2968001 : Blo 583288 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B937327 : Blo 583288 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B904679 : Blo 583288 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B1330679 : Blo 583288 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B5000849 : Blo 583288 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B2805443 : Blo 583288 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B3330233 : Blo 583288 3330233 := bstep (se 2 (by rfl) ⟨1248837, by rfl⟩ : syracuseStep 3330233 = 2497675) B2497675
theorem B22794533 : Blo 583288 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B4510505 : Blo 583288 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B6345809 : Blo 583288 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B14243035 : Blo 583288 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B3757403 : Blo 583288 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B30365027 : Blo 583288 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B6313459 : Blo 583288 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B1463879 : Blo 583288 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B743023 : Blo 583288 743023 := bstep (se 1 (by rfl) ⟨557267, by rfl⟩ : syracuseStep 743023 = 1114535) B1114535
theorem B2217739 : Blo 583288 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B2971403 : Blo 583288 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B2807903 : Blo 583288 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B940223 : Blo 583288 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B875039 : Blo 583288 875039 := bstep (se 1 (by rfl) ⟨656279, by rfl⟩ : syracuseStep 875039 = 1312559) B1312559
theorem B1661597 : Blo 583288 1661597 := bstep (se 3 (by rfl) ⟨311549, by rfl⟩ : syracuseStep 1661597 = 623099) B623099
theorem B875423 : Blo 583288 875423 := bstep (se 1 (by rfl) ⟨656567, by rfl⟩ : syracuseStep 875423 = 1313135) B1313135
theorem B14998445 : Blo 583288 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B875471 : Blo 583288 875471 := bstep (se 1 (by rfl) ⟨656603, by rfl⟩ : syracuseStep 875471 = 1313207) B1313207
theorem B104225753 : Blo 583288 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B3169271 : Blo 583288 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B875561 : Blo 583288 875561 := bstep (se 2 (by rfl) ⟨328335, by rfl⟩ : syracuseStep 875561 = 656671) B656671
theorem B875567 : Blo 583288 875567 := bstep (se 1 (by rfl) ⟨656675, by rfl⟩ : syracuseStep 875567 = 1313351) B1313351
theorem B7494713 : Blo 583288 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B875591 : Blo 583288 875591 := bstep (se 1 (by rfl) ⟨656693, by rfl⟩ : syracuseStep 875591 = 1313387) B1313387
theorem B875855 : Blo 583288 875855 := bstep (se 1 (by rfl) ⟨656891, by rfl⟩ : syracuseStep 875855 = 1313783) B1313783
theorem B2973023 : Blo 583288 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B5332385 : Blo 583288 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B875945 : Blo 583288 875945 := bstep (se 2 (by rfl) ⟨328479, by rfl⟩ : syracuseStep 875945 = 656959) B656959
theorem B1662439 : Blo 583288 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B876095 : Blo 583288 876095 := bstep (se 1 (by rfl) ⟨657071, by rfl⟩ : syracuseStep 876095 = 1314143) B1314143
theorem B876359 : Blo 583288 876359 := bstep (se 1 (by rfl) ⟨657269, by rfl⟩ : syracuseStep 876359 = 1314539) B1314539
theorem B876443 : Blo 583288 876443 := bstep (se 1 (by rfl) ⟨657332, by rfl⟩ : syracuseStep 876443 = 1314665) B1314665
theorem B877007 : Blo 583288 877007 := bstep (se 1 (by rfl) ⟨657755, by rfl⟩ : syracuseStep 877007 = 1315511) B1315511
theorem B877049 : Blo 583288 877049 := bstep (se 2 (by rfl) ⟨328893, by rfl⟩ : syracuseStep 877049 = 657787) B657787
theorem B877151 : Blo 583288 877151 := bstep (se 1 (by rfl) ⟨657863, by rfl⟩ : syracuseStep 877151 = 1315727) B1315727
theorem B877631 : Blo 583288 877631 := bstep (se 1 (by rfl) ⟨658223, by rfl⟩ : syracuseStep 877631 = 1316447) B1316447
theorem B877673 : Blo 583288 877673 := bstep (se 2 (by rfl) ⟨329127, by rfl⟩ : syracuseStep 877673 = 658255) B658255
theorem B3761275 : Blo 583288 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B3335357 : Blo 583288 3335357 := bstep (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) B1250759
theorem B28959947 : Blo 583288 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B877775 : Blo 583288 877775 := bstep (se 1 (by rfl) ⟨658331, by rfl⟩ : syracuseStep 877775 = 1316663) B1316663
theorem B877979 : Blo 583288 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B31975033 : Blo 583288 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B878201 : Blo 583288 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B583335 : Blo 583288 583335 := bstep (se 1 (by rfl) ⟨437501, by rfl⟩ : syracuseStep 583335 = 875003) B875003
theorem B878303 : Blo 583288 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B583419 : Blo 583288 583419 := bstep (se 1 (by rfl) ⟨437564, by rfl⟩ : syracuseStep 583419 = 875129) B875129
theorem B583455 : Blo 583288 583455 := bstep (se 1 (by rfl) ⟨437591, by rfl⟩ : syracuseStep 583455 = 875183) B875183
theorem B583487 : Blo 583288 583487 := bstep (se 1 (by rfl) ⟨437615, by rfl⟩ : syracuseStep 583487 = 875231) B875231
theorem B878399 : Blo 583288 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B3172193 : Blo 583288 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B878567 : Blo 583288 878567 := bstep (se 1 (by rfl) ⟨658925, by rfl⟩ : syracuseStep 878567 = 1317851) B1317851
theorem B583663 : Blo 583288 583663 := bstep (se 1 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 583663 = 875495) B875495
theorem B878585 : Blo 583288 878585 := bstep (se 2 (by rfl) ⟨329469, by rfl⟩ : syracuseStep 878585 = 658939) B658939
theorem B878687 : Blo 583288 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B583835 : Blo 583288 583835 := bstep (se 1 (by rfl) ⟨437876, by rfl⟩ : syracuseStep 583835 = 875753) B875753
theorem B878747 : Blo 583288 878747 := bstep (se 1 (by rfl) ⟨659060, by rfl⟩ : syracuseStep 878747 = 1318121) B1318121
theorem B583871 : Blo 583288 583871 := bstep (se 1 (by rfl) ⟨437903, by rfl⟩ : syracuseStep 583871 = 875807) B875807
theorem B878783 : Blo 583288 878783 := bstep (se 1 (by rfl) ⟨659087, by rfl⟩ : syracuseStep 878783 = 1318175) B1318175
theorem B878825 : Blo 583288 878825 := bstep (se 2 (by rfl) ⟨329559, by rfl⟩ : syracuseStep 878825 = 659119) B659119
theorem B583983 : Blo 583288 583983 := bstep (se 1 (by rfl) ⟨437987, by rfl⟩ : syracuseStep 583983 = 875975) B875975
theorem B1403183 : Blo 583288 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B584219 : Blo 583288 584219 := bstep (se 1 (by rfl) ⟨438164, by rfl⟩ : syracuseStep 584219 = 876329) B876329
theorem B879131 : Blo 583288 879131 := bstep (se 1 (by rfl) ⟨659348, by rfl⟩ : syracuseStep 879131 = 1318697) B1318697
theorem B584223 : Blo 583288 584223 := bstep (se 1 (by rfl) ⟨438167, by rfl⟩ : syracuseStep 584223 = 876335) B876335
theorem B879209 : Blo 583288 879209 := bstep (se 2 (by rfl) ⟨329703, by rfl⟩ : syracuseStep 879209 = 659407) B659407
theorem B3795767 : Blo 583288 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B2222903 : Blo 583288 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B584539 : Blo 583288 584539 := bstep (se 1 (by rfl) ⟨438404, by rfl⟩ : syracuseStep 584539 = 876809) B876809
theorem B584607 : Blo 583288 584607 := bstep (se 1 (by rfl) ⟨438455, by rfl⟩ : syracuseStep 584607 = 876911) B876911
theorem B57863099 : Blo 583288 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B3992555 : Blo 583288 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B584751 : Blo 583288 584751 := bstep (se 1 (by rfl) ⟨438563, by rfl⟩ : syracuseStep 584751 = 877127) B877127
theorem B584775 : Blo 583288 584775 := bstep (se 1 (by rfl) ⟨438581, by rfl⟩ : syracuseStep 584775 = 877163) B877163
theorem B879737 : Blo 583288 879737 := bstep (se 2 (by rfl) ⟨329901, by rfl⟩ : syracuseStep 879737 = 659803) B659803
theorem B584927 : Blo 583288 584927 := bstep (se 1 (by rfl) ⟨438695, by rfl⟩ : syracuseStep 584927 = 877391) B877391
theorem B879839 : Blo 583288 879839 := bstep (se 1 (by rfl) ⟨659879, by rfl⟩ : syracuseStep 879839 = 1319759) B1319759
theorem B879881 : Blo 583288 879881 := bstep (se 2 (by rfl) ⟨329955, by rfl⟩ : syracuseStep 879881 = 659911) B659911
theorem B3566891 : Blo 583288 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B31976765 : Blo 583288 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B4287853 : Blo 583288 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B879983 : Blo 583288 879983 := bstep (se 1 (by rfl) ⟨659987, by rfl⟩ : syracuseStep 879983 = 1319975) B1319975
theorem B585191 : Blo 583288 585191 := bstep (se 1 (by rfl) ⟨438893, by rfl⟩ : syracuseStep 585191 = 877787) B877787
theorem B880103 : Blo 583288 880103 := bstep (se 1 (by rfl) ⟨660077, by rfl⟩ : syracuseStep 880103 = 1320155) B1320155
theorem B585307 : Blo 583288 585307 := bstep (se 1 (by rfl) ⟨438980, by rfl⟩ : syracuseStep 585307 = 877961) B877961
theorem B880235 : Blo 583288 880235 := bstep (se 1 (by rfl) ⟨660176, by rfl⟩ : syracuseStep 880235 = 1320353) B1320353
theorem B880361 : Blo 583288 880361 := bstep (se 2 (by rfl) ⟨330135, by rfl⟩ : syracuseStep 880361 = 660271) B660271
theorem B585543 : Blo 583288 585543 := bstep (se 1 (by rfl) ⟨439157, by rfl⟩ : syracuseStep 585543 = 878315) B878315
theorem B8580971 : Blo 583288 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B880505 : Blo 583288 880505 := bstep (se 2 (by rfl) ⟨330189, by rfl⟩ : syracuseStep 880505 = 660379) B660379
theorem B585695 : Blo 583288 585695 := bstep (se 1 (by rfl) ⟨439271, by rfl⟩ : syracuseStep 585695 = 878543) B878543
theorem B880607 : Blo 583288 880607 := bstep (se 1 (by rfl) ⟨660455, by rfl⟩ : syracuseStep 880607 = 1320911) B1320911
theorem B880859 : Blo 583288 880859 := bstep (se 1 (by rfl) ⟨660644, by rfl⟩ : syracuseStep 880859 = 1321289) B1321289
theorem B585959 : Blo 583288 585959 := bstep (se 1 (by rfl) ⟨439469, by rfl⟩ : syracuseStep 585959 = 878939) B878939
theorem B880871 : Blo 583288 880871 := bstep (se 1 (by rfl) ⟨660653, by rfl⟩ : syracuseStep 880871 = 1321307) B1321307
theorem B586111 : Blo 583288 586111 := bstep (se 1 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 586111 = 879167) B879167
theorem B6320551 : Blo 583288 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B586191 : Blo 583288 586191 := bstep (se 1 (by rfl) ⟨439643, by rfl⟩ : syracuseStep 586191 = 879287) B879287
theorem B1405433 : Blo 583288 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B586343 : Blo 583288 586343 := bstep (se 1 (by rfl) ⟨439757, by rfl⟩ : syracuseStep 586343 = 879515) B879515
theorem B4223735 : Blo 583288 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B586607 : Blo 583288 586607 := bstep (se 1 (by rfl) ⟨439955, by rfl⟩ : syracuseStep 586607 = 879911) B879911
theorem B586663 : Blo 583288 586663 := bstep (se 1 (by rfl) ⟨439997, by rfl⟩ : syracuseStep 586663 = 879995) B879995
theorem B586747 : Blo 583288 586747 := bstep (se 1 (by rfl) ⟨440060, by rfl⟩ : syracuseStep 586747 = 880121) B880121
theorem B586815 : Blo 583288 586815 := bstep (se 1 (by rfl) ⟨440111, by rfl⟩ : syracuseStep 586815 = 880223) B880223
theorem B1668271 : Blo 583288 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B586959 : Blo 583288 586959 := bstep (se 1 (by rfl) ⟨440219, by rfl⟩ : syracuseStep 586959 = 880439) B880439
theorem B1111315 : Blo 583288 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B587163 : Blo 583288 587163 := bstep (se 1 (by rfl) ⟨440372, by rfl⟩ : syracuseStep 587163 = 880745) B880745
theorem B18216355 : Blo 583288 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B7140797 : Blo 583288 7140797 := bstep (se 3 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 7140797 = 2677799) B2677799
theorem B1669319 : Blo 583288 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B1604233 : Blo 583288 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B1669855 : Blo 583288 1669855 := bstep (se 1 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 1669855 = 2504783) B2504783
theorem B6683471 : Blo 583288 6683471 := bstep (se 1 (by rfl) ⟨5012603, by rfl⟩ : syracuseStep 6683471 = 10025207) B10025207
theorem B2227945 : Blo 583288 2227945 := bstep (se 2 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 2227945 = 1670959) B1670959
theorem B2229191 : Blo 583288 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B5015033 : Blo 583288 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B656923 : Blo 583288 656923 := bstep (se 1 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 656923 = 985385) B985385
theorem B2491985 : Blo 583288 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B984683 : Blo 583288 984683 := bstep (se 1 (by rfl) ⟨738512, by rfl⟩ : syracuseStep 984683 = 1477025) B1477025
theorem B984953 : Blo 583288 984953 := bstep (se 2 (by rfl) ⟨369357, by rfl⟩ : syracuseStep 984953 = 738715) B738715
theorem B2820205 : Blo 583288 2820205 := bstep (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) B1057577
theorem B42633377 : Blo 583288 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B1312955 : Blo 583288 1312955 := bstep (se 1 (by rfl) ⟨984716, by rfl⟩ : syracuseStep 1312955 = 1969433) B1969433
theorem B1312991 : Blo 583288 1312991 := bstep (se 1 (by rfl) ⟨984743, by rfl⟩ : syracuseStep 1312991 = 1969487) B1969487
theorem B4983079 : Blo 583288 4983079 := bstep (se 1 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 4983079 = 7474619) B7474619
theorem B887119 : Blo 583288 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B5638565 : Blo 583288 5638565 := bstep (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) B1057231
theorem B985513 : Blo 583288 985513 := bstep (se 2 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 985513 = 739135) B739135
theorem B1870295 : Blo 583288 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B8129011 : Blo 583288 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B657967 : Blo 583288 657967 := bstep (se 1 (by rfl) ⟨493475, by rfl⟩ : syracuseStep 657967 = 986951) B986951
theorem B1247881 : Blo 583288 1247881 := bstep (se 2 (by rfl) ⟨467955, by rfl⟩ : syracuseStep 1247881 = 935911) B935911
theorem B1313441 : Blo 583288 1313441 := bstep (se 2 (by rfl) ⟨492540, by rfl⟩ : syracuseStep 1313441 = 985081) B985081
theorem B1313657 : Blo 583288 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B1969055 : Blo 583288 1969055 := bstep (se 1 (by rfl) ⟨1476791, by rfl⟩ : syracuseStep 1969055 = 2953583) B2953583
theorem B658399 : Blo 583288 658399 := bstep (se 1 (by rfl) ⟨493799, by rfl⟩ : syracuseStep 658399 = 987599) B987599
theorem B986107 : Blo 583288 986107 := bstep (se 1 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 986107 = 1479161) B1479161
theorem B1313801 : Blo 583288 1313801 := bstep (se 2 (by rfl) ⟨492675, by rfl⟩ : syracuseStep 1313801 = 985351) B985351
theorem B1313855 : Blo 583288 1313855 := bstep (se 1 (by rfl) ⟨985391, by rfl⟩ : syracuseStep 1313855 = 1970783) B1970783
theorem B2493575 : Blo 583288 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B2493625 : Blo 583288 2493625 := bstep (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) B1870219
theorem B10292503 : Blo 583288 10292503 := bstep (se 1 (by rfl) ⟨7719377, by rfl⟩ : syracuseStep 10292503 = 15438755) B15438755
theorem B4230539 : Blo 583288 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B1248743 : Blo 583288 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B7114229 : Blo 583288 7114229 := bstep (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) B666959
theorem B659047 : Blo 583288 659047 := bstep (se 1 (by rfl) ⟨494285, by rfl⟩ : syracuseStep 659047 = 988571) B988571
theorem B659263 : Blo 583288 659263 := bstep (se 1 (by rfl) ⟨494447, by rfl⟩ : syracuseStep 659263 = 988895) B988895
theorem B1314683 : Blo 583288 1314683 := bstep (se 1 (by rfl) ⟨986012, by rfl⟩ : syracuseStep 1314683 = 1972025) B1972025
theorem B1314791 : Blo 583288 1314791 := bstep (se 1 (by rfl) ⟨986093, by rfl⟩ : syracuseStep 1314791 = 1972187) B1972187
theorem B11243609 : Blo 583288 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B659551 : Blo 583288 659551 := bstep (se 1 (by rfl) ⟨494663, by rfl⟩ : syracuseStep 659551 = 989327) B989327
theorem B626815 : Blo 583288 626815 := bstep (se 1 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 626815 = 940223) B940223
theorem B1314971 : Blo 583288 1314971 := bstep (se 1 (by rfl) ⟨986228, by rfl⟩ : syracuseStep 1314971 = 1972457) B1972457
theorem B3903677 : Blo 583288 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B4067615 : Blo 583288 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B1315169 : Blo 583288 1315169 := bstep (se 2 (by rfl) ⟨493188, by rfl⟩ : syracuseStep 1315169 = 986377) B986377
theorem B1315259 : Blo 583288 1315259 := bstep (se 1 (by rfl) ⟨986444, by rfl⟩ : syracuseStep 1315259 = 1972889) B1972889
theorem B1970621 : Blo 583288 1970621 := bstep (se 3 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 1970621 = 738983) B738983
theorem B1249769 : Blo 583288 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B9998963 : Blo 583288 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B1316519 : Blo 583288 1316519 := bstep (se 1 (by rfl) ⟨987389, by rfl⟩ : syracuseStep 1316519 = 1974779) B1974779
theorem B2365147 : Blo 583288 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B1316699 : Blo 583288 1316699 := bstep (se 1 (by rfl) ⟨987524, by rfl⟩ : syracuseStep 1316699 = 1975049) B1975049
theorem B8427401 : Blo 583288 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B8001641 : Blo 583288 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B3741821 : Blo 583288 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B1972349 : Blo 583288 1972349 := bstep (se 3 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 1972349 = 739631) B739631
theorem B19306631 : Blo 583288 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B1972511 : Blo 583288 1972511 := bstep (se 1 (by rfl) ⟨1479383, by rfl⟩ : syracuseStep 1972511 = 2958767) B2958767
theorem B1317203 : Blo 583288 1317203 := bstep (se 1 (by rfl) ⟨987902, by rfl⟩ : syracuseStep 1317203 = 1975805) B1975805
theorem B1972619 : Blo 583288 1972619 := bstep (se 1 (by rfl) ⟨1479464, by rfl⟩ : syracuseStep 1972619 = 2958929) B2958929
theorem B1055207 : Blo 583288 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B989671 : Blo 583288 989671 := bstep (se 1 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 989671 = 1484507) B1484507
theorem B1317689 : Blo 583288 1317689 := bstep (se 2 (by rfl) ⟨494133, by rfl⟩ : syracuseStep 1317689 = 988267) B988267
theorem B1317743 : Blo 583288 1317743 := bstep (se 1 (by rfl) ⟨988307, by rfl⟩ : syracuseStep 1317743 = 1976615) B1976615
theorem B1481753 : Blo 583288 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B2530511 : Blo 583288 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B1481935 : Blo 583288 1481935 := bstep (se 1 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 1481935 = 2222903) B2222903
theorem B24288473 : Blo 583288 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B38575399 : Blo 583288 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B2661703 : Blo 583288 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B990535 : Blo 583288 990535 := bstep (se 1 (by rfl) ⟨742901, by rfl⟩ : syracuseStep 990535 = 1485803) B1485803
theorem B1318319 : Blo 583288 1318319 := bstep (se 1 (by rfl) ⟨988739, by rfl⟩ : syracuseStep 1318319 = 1977479) B1977479
theorem B990697 : Blo 583288 990697 := bstep (se 2 (by rfl) ⟨371511, by rfl⟩ : syracuseStep 990697 = 743023) B743023
theorem B1318391 : Blo 583288 1318391 := bstep (se 1 (by rfl) ⟨988793, by rfl⟩ : syracuseStep 1318391 = 1977587) B1977587
theorem B2956985 : Blo 583288 2956985 := bstep (se 2 (by rfl) ⟨1108869, by rfl⟩ : syracuseStep 2956985 = 2217739) B2217739
theorem B1253083 : Blo 583288 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B1974239 : Blo 583288 1974239 := bstep (se 1 (by rfl) ⟨1480679, by rfl⟩ : syracuseStep 1974239 = 2961359) B2961359
theorem B1974401 : Blo 583288 1974401 := bstep (se 2 (by rfl) ⟨740400, by rfl⟩ : syracuseStep 1974401 = 1480801) B1480801
theorem B1319417 : Blo 583288 1319417 := bstep (se 2 (by rfl) ⟨494781, by rfl⟩ : syracuseStep 1319417 = 989563) B989563
theorem B1319507 : Blo 583288 1319507 := bstep (se 1 (by rfl) ⟨989630, by rfl⟩ : syracuseStep 1319507 = 1979261) B1979261
theorem B1253971 : Blo 583288 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B1319687 : Blo 583288 1319687 := bstep (se 1 (by rfl) ⟨989765, by rfl⟩ : syracuseStep 1319687 = 1979531) B1979531
theorem B2138977 : Blo 583288 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B1319777 : Blo 583288 1319777 := bstep (se 2 (by rfl) ⟨494916, by rfl⟩ : syracuseStep 1319777 = 989833) B989833
theorem B4432805 : Blo 583288 4432805 := bstep (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) B831151
theorem B1975211 : Blo 583288 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B4760531 : Blo 583288 4760531 := bstep (se 1 (by rfl) ⟨3570398, by rfl⟩ : syracuseStep 4760531 = 7140797) B7140797
theorem B5710907 : Blo 583288 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B1975751 : Blo 583288 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B1320767 : Blo 583288 1320767 := bstep (se 1 (by rfl) ⟨990575, by rfl⟩ : syracuseStep 1320767 = 1981151) B1981151
theorem B3417985 : Blo 583288 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B2566171 : Blo 583288 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B1321271 : Blo 583288 1321271 := bstep (se 1 (by rfl) ⟨990953, by rfl⟩ : syracuseStep 1321271 = 1981907) B1981907
theorem B1977857 : Blo 583288 1977857 := bstep (se 2 (by rfl) ⟨741696, by rfl⟩ : syracuseStep 1977857 = 1483393) B1483393
theorem B13512379 : Blo 583288 13512379 := bstep (se 1 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 13512379 = 20268569) B20268569
theorem B4730687 : Blo 583288 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B831721 : Blo 583288 831721 := bstep (se 2 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 831721 = 623791) B623791
theorem B2961683 : Blo 583288 2961683 := bstep (se 1 (by rfl) ⟨2221262, by rfl⟩ : syracuseStep 2961683 = 4442525) B4442525
theorem B1978667 : Blo 583288 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B1978937 : Blo 583288 1978937 := bstep (se 2 (by rfl) ⟨742101, by rfl⟩ : syracuseStep 1978937 = 1484203) B1484203
theorem B3322691 : Blo 583288 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B832393 : Blo 583288 832393 := bstep (se 2 (by rfl) ⟨312147, by rfl⟩ : syracuseStep 832393 = 624295) B624295
theorem B603119 : Blo 583288 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B6009851 : Blo 583288 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B5617309 : Blo 583288 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B4437665 : Blo 583288 4437665 := bstep (se 2 (by rfl) ⟨1664124, by rfl⟩ : syracuseStep 4437665 = 3328249) B3328249
theorem B2504935 : Blo 583288 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B1980665 : Blo 583288 1980665 := bstep (se 2 (by rfl) ⟨742749, by rfl⟩ : syracuseStep 1980665 = 1485499) B1485499
theorem B1980935 : Blo 583288 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B703399 : Blo 583288 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B60865501 : Blo 583288 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B2112617 : Blo 583288 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B5717137 : Blo 583288 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B69483835 : Blo 583288 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B2112847 : Blo 583288 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B4996475 : Blo 583288 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B4734445 : Blo 583288 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B1982015 : Blo 583288 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B3554923 : Blo 583288 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B7487741 : Blo 583288 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B5620499 : Blo 583288 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B5620727 : Blo 583288 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B3327065 : Blo 583288 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B2114795 : Blo 583288 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B18990713 : Blo 583288 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B55428907 : Blo 583288 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B2377927 : Blo 583288 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B21317843 : Blo 583288 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B5720647 : Blo 583288 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B4213529 : Blo 583288 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B936955 : Blo 583288 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B10144763 : Blo 583288 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B5622959 : Blo 583288 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B3329707 : Blo 583288 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B2216585 : Blo 583288 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B938633 : Blo 583288 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B2970593 : Blo 583288 2970593 := bstep (se 2 (by rfl) ⟨1113972, by rfl⟩ : syracuseStep 2970593 = 2227945) B2227945
theorem B2676833 : Blo 583288 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B874985 : Blo 583288 874985 := bstep (se 2 (by rfl) ⟨328119, by rfl⟩ : syracuseStep 874985 = 656239) B656239
theorem B875375 : Blo 583288 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B875387 : Blo 583288 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B876251 : Blo 583288 876251 := bstep (se 1 (by rfl) ⟨657188, by rfl⟩ : syracuseStep 876251 = 1314377) B1314377
theorem B3333899 : Blo 583288 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B1335059 : Blo 583288 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B876521 : Blo 583288 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B2220155 : Blo 583288 2220155 := bstep (se 1 (by rfl) ⟨1665116, by rfl⟩ : syracuseStep 2220155 = 3330233) B3330233
theorem B15196355 : Blo 583288 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B3007003 : Blo 583288 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B877223 : Blo 583288 877223 := bstep (se 1 (by rfl) ⟨657917, by rfl⟩ : syracuseStep 877223 = 1315835) B1315835
theorem B877343 : Blo 583288 877343 := bstep (se 1 (by rfl) ⟨658007, by rfl⟩ : syracuseStep 877343 = 1316015) B1316015
theorem B877367 : Blo 583288 877367 := bstep (se 1 (by rfl) ⟨658025, by rfl⟩ : syracuseStep 877367 = 1316051) B1316051
theorem B20243351 : Blo 583288 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B877547 : Blo 583288 877547 := bstep (se 1 (by rfl) ⟨658160, by rfl⟩ : syracuseStep 877547 = 1316321) B1316321
theorem B583359 : Blo 583288 583359 := bstep (se 1 (by rfl) ⟨437519, by rfl⟩ : syracuseStep 583359 = 875039) B875039
theorem B1107731 : Blo 583288 1107731 := bstep (se 1 (by rfl) ⟨830798, by rfl⟩ : syracuseStep 1107731 = 1661597) B1661597
theorem B583615 : Blo 583288 583615 := bstep (se 1 (by rfl) ⟨437711, by rfl⟩ : syracuseStep 583615 = 875423) B875423
theorem B5334983 : Blo 583288 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B3762119 : Blo 583288 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B583647 : Blo 583288 583647 := bstep (se 1 (by rfl) ⟨437735, by rfl⟩ : syracuseStep 583647 = 875471) B875471
theorem B583707 : Blo 583288 583707 := bstep (se 1 (by rfl) ⟨437780, by rfl⟩ : syracuseStep 583707 = 875561) B875561
theorem B583711 : Blo 583288 583711 := bstep (se 1 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 583711 = 875567) B875567
theorem B583727 : Blo 583288 583727 := bstep (se 1 (by rfl) ⟨437795, by rfl⟩ : syracuseStep 583727 = 875591) B875591
theorem B878639 : Blo 583288 878639 := bstep (se 1 (by rfl) ⟨658979, by rfl⟩ : syracuseStep 878639 = 1317959) B1317959
theorem B583903 : Blo 583288 583903 := bstep (se 1 (by rfl) ⟨437927, by rfl⟩ : syracuseStep 583903 = 875855) B875855
theorem B583963 : Blo 583288 583963 := bstep (se 1 (by rfl) ⟨437972, by rfl⟩ : syracuseStep 583963 = 875945) B875945
theorem B878903 : Blo 583288 878903 := bstep (se 1 (by rfl) ⟨659177, by rfl⟩ : syracuseStep 878903 = 1318355) B1318355
theorem B584063 : Blo 583288 584063 := bstep (se 1 (by rfl) ⟨438047, by rfl⟩ : syracuseStep 584063 = 876095) B876095
theorem B879083 : Blo 583288 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B584239 : Blo 583288 584239 := bstep (se 1 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 584239 = 876359) B876359
theorem B584295 : Blo 583288 584295 := bstep (se 1 (by rfl) ⟨438221, by rfl⟩ : syracuseStep 584295 = 876443) B876443
theorem B5073515 : Blo 583288 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B7105171 : Blo 583288 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B584671 : Blo 583288 584671 := bstep (se 1 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 584671 = 877007) B877007
theorem B584699 : Blo 583288 584699 := bstep (se 1 (by rfl) ⟨438524, by rfl⟩ : syracuseStep 584699 = 877049) B877049
theorem B584767 : Blo 583288 584767 := bstep (se 1 (by rfl) ⟨438575, by rfl⟩ : syracuseStep 584767 = 877151) B877151
theorem B879785 : Blo 583288 879785 := bstep (se 2 (by rfl) ⟨329919, by rfl⟩ : syracuseStep 879785 = 659839) B659839
theorem B2223389 : Blo 583288 2223389 := bstep (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) B833771
theorem B585087 : Blo 583288 585087 := bstep (se 1 (by rfl) ⟨438815, by rfl⟩ : syracuseStep 585087 = 877631) B877631
theorem B585115 : Blo 583288 585115 := bstep (se 1 (by rfl) ⟨438836, by rfl⟩ : syracuseStep 585115 = 877673) B877673
theorem B2223571 : Blo 583288 2223571 := bstep (se 1 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 2223571 = 3335357) B3335357
theorem B585183 : Blo 583288 585183 := bstep (se 1 (by rfl) ⟨438887, by rfl⟩ : syracuseStep 585183 = 877775) B877775
theorem B1666631 : Blo 583288 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B880199 : Blo 583288 880199 := bstep (se 1 (by rfl) ⟨660149, by rfl⟩ : syracuseStep 880199 = 1320299) B1320299
theorem B585319 : Blo 583288 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B585467 : Blo 583288 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B880379 : Blo 583288 880379 := bstep (se 1 (by rfl) ⟨660284, by rfl⟩ : syracuseStep 880379 = 1320569) B1320569
theorem B585535 : Blo 583288 585535 := bstep (se 1 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 585535 = 878303) B878303
theorem B10841951 : Blo 583288 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B585599 : Blo 583288 585599 := bstep (se 1 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 585599 = 878399) B878399
theorem B585711 : Blo 583288 585711 := bstep (se 1 (by rfl) ⟨439283, by rfl⟩ : syracuseStep 585711 = 878567) B878567
theorem B585723 : Blo 583288 585723 := bstep (se 1 (by rfl) ⟨439292, by rfl⟩ : syracuseStep 585723 = 878585) B878585
theorem B585791 : Blo 583288 585791 := bstep (se 1 (by rfl) ⟨439343, by rfl⟩ : syracuseStep 585791 = 878687) B878687
theorem B1667155 : Blo 583288 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B585831 : Blo 583288 585831 := bstep (se 1 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 585831 = 878747) B878747
theorem B585855 : Blo 583288 585855 := bstep (se 1 (by rfl) ⟨439391, by rfl⟩ : syracuseStep 585855 = 878783) B878783
theorem B585883 : Blo 583288 585883 := bstep (se 1 (by rfl) ⟨439412, by rfl⟩ : syracuseStep 585883 = 878825) B878825
theorem B5009597 : Blo 583288 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B2224361 : Blo 583288 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B586087 : Blo 583288 586087 := bstep (se 1 (by rfl) ⟨439565, by rfl⟩ : syracuseStep 586087 = 879131) B879131
theorem B586139 : Blo 583288 586139 := bstep (se 1 (by rfl) ⟨439604, by rfl⟩ : syracuseStep 586139 = 879209) B879209
theorem B8417945 : Blo 583288 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B586491 : Blo 583288 586491 := bstep (se 1 (by rfl) ⟨439868, by rfl⟩ : syracuseStep 586491 = 879737) B879737
theorem B586559 : Blo 583288 586559 := bstep (se 1 (by rfl) ⟨439919, by rfl⟩ : syracuseStep 586559 = 879839) B879839
theorem B586587 : Blo 583288 586587 := bstep (se 1 (by rfl) ⟨439940, by rfl⟩ : syracuseStep 586587 = 879881) B879881
theorem B586655 : Blo 583288 586655 := bstep (se 1 (by rfl) ⟨439991, by rfl⟩ : syracuseStep 586655 = 879983) B879983
theorem B586735 : Blo 583288 586735 := bstep (se 1 (by rfl) ⟨440051, by rfl⟩ : syracuseStep 586735 = 880103) B880103
theorem B1668089 : Blo 583288 1668089 := bstep (se 2 (by rfl) ⟨625533, by rfl⟩ : syracuseStep 1668089 = 1251067) B1251067
theorem B586823 : Blo 583288 586823 := bstep (se 1 (by rfl) ⟨440117, by rfl⟩ : syracuseStep 586823 = 880235) B880235
theorem B586907 : Blo 583288 586907 := bstep (se 1 (by rfl) ⟨440180, by rfl⟩ : syracuseStep 586907 = 880361) B880361
theorem B587003 : Blo 583288 587003 := bstep (se 1 (by rfl) ⟨440252, by rfl⟩ : syracuseStep 587003 = 880505) B880505
theorem B587071 : Blo 583288 587071 := bstep (se 1 (by rfl) ⟨440303, by rfl⟩ : syracuseStep 587071 = 880607) B880607
theorem B1406375 : Blo 583288 1406375 := bstep (se 1 (by rfl) ⟨1054781, by rfl⟩ : syracuseStep 1406375 = 2109563) B2109563
theorem B587239 : Blo 583288 587239 := bstep (se 1 (by rfl) ⟨440429, by rfl⟩ : syracuseStep 587239 = 880859) B880859
theorem B587247 : Blo 583288 587247 := bstep (se 1 (by rfl) ⟨440435, by rfl⟩ : syracuseStep 587247 = 880871) B880871
theorem B10679941 : Blo 583288 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B2815823 : Blo 583288 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B5011307 : Blo 583288 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B1112105 : Blo 583288 1112105 := bstep (se 2 (by rfl) ⟨417039, by rfl⟩ : syracuseStep 1112105 = 834079) B834079
theorem B2226473 : Blo 583288 2226473 := bstep (se 2 (by rfl) ⟨834927, by rfl⟩ : syracuseStep 2226473 = 1669855) B1669855
theorem B1669673 : Blo 583288 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B2816669 : Blo 583288 2816669 := bstep (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) B1056251
theorem B1112879 : Blo 583288 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B4815949 : Blo 583288 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B4455647 : Blo 583288 4455647 := bstep (se 1 (by rfl) ⟨3341735, by rfl⟩ : syracuseStep 4455647 = 6683471) B6683471
theorem B10846973 : Blo 583288 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B3343355 : Blo 583288 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B12682277 : Blo 583288 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B656455 : Blo 583288 656455 := bstep (se 1 (by rfl) ⟨492341, by rfl⟩ : syracuseStep 656455 = 984683) B984683
theorem B2851969 : Blo 583288 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B656635 : Blo 583288 656635 := bstep (se 1 (by rfl) ⟨492476, by rfl⟩ : syracuseStep 656635 = 984953) B984953
theorem B1312703 : Blo 583288 1312703 := bstep (se 1 (by rfl) ⟨984527, by rfl⟩ : syracuseStep 1312703 = 1969055) B1969055
theorem B2820359 : Blo 583288 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B4557313 : Blo 583288 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B1608317 : Blo 583288 1608317 := bstep (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) B603119
theorem B1313747 : Blo 583288 1313747 := bstep (se 1 (by rfl) ⟨985310, by rfl⟩ : syracuseStep 1313747 = 1970621) B1970621
theorem B1477723 : Blo 583288 1477723 := bstep (se 1 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 1477723 = 2216585) B2216585
theorem B6687845 : Blo 583288 6687845 := bstep (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) B1253971
theorem B1314017 : Blo 583288 1314017 := bstep (se 2 (by rfl) ⟨492756, by rfl⟩ : syracuseStep 1314017 = 985513) B985513
theorem B5639453 : Blo 583288 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B9473561 : Blo 583288 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B1314809 : Blo 583288 1314809 := bstep (se 2 (by rfl) ⟨493053, by rfl⟩ : syracuseStep 1314809 = 986107) B986107
theorem B1249273 : Blo 583288 1249273 := bstep (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) B936955
theorem B2494547 : Blo 583288 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B1314899 : Blo 583288 1314899 := bstep (se 1 (by rfl) ⟨986174, by rfl⟩ : syracuseStep 1314899 = 1972349) B1972349
theorem B1315007 : Blo 583288 1315007 := bstep (se 1 (by rfl) ⟨986255, by rfl⟩ : syracuseStep 1315007 = 1972511) B1972511
theorem B1315079 : Blo 583288 1315079 := bstep (se 1 (by rfl) ⟨986309, by rfl⟩ : syracuseStep 1315079 = 1972619) B1972619
theorem B987835 : Blo 583288 987835 := bstep (se 1 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 987835 = 1481753) B1481753
theorem B16192315 : Blo 583288 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B7508861 : Blo 583288 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B1971323 : Blo 583288 1971323 := bstep (se 1 (by rfl) ⟨1478492, by rfl⟩ : syracuseStep 1971323 = 2956985) B2956985
theorem B890039 : Blo 583288 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B1316159 : Blo 583288 1316159 := bstep (se 1 (by rfl) ⟨987119, by rfl⟩ : syracuseStep 1316159 = 1974239) B1974239
theorem B1480103 : Blo 583288 1480103 := bstep (se 1 (by rfl) ⟨1110077, by rfl⟩ : syracuseStep 1480103 = 2220155) B2220155
theorem B1316267 : Blo 583288 1316267 := bstep (se 1 (by rfl) ⟨987200, by rfl⟩ : syracuseStep 1316267 = 1974401) B1974401
theorem B10130903 : Blo 583288 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B51484349 : Blo 583288 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B2955203 : Blo 583288 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B1316807 : Blo 583288 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B3807271 : Blo 583288 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B1317167 : Blo 583288 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B4987453 : Blo 583288 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B370580453 : Blo 583288 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B14195749 : Blo 583288 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B3382343 : Blo 583288 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B1482259 : Blo 583288 1482259 := bstep (se 1 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 1482259 = 2223389) B2223389
theorem B3153529 : Blo 583288 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B1318571 : Blo 583288 1318571 := bstep (se 1 (by rfl) ⟨988928, by rfl⟩ : syracuseStep 1318571 = 1977857) B1977857
theorem B3153791 : Blo 583288 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B1482907 : Blo 583288 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B1974455 : Blo 583288 1974455 := bstep (se 1 (by rfl) ⟨1480841, by rfl⟩ : syracuseStep 1974455 = 2961683) B2961683
theorem B1319111 : Blo 583288 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B1319291 : Blo 583288 1319291 := bstep (se 1 (by rfl) ⟨989468, by rfl⟩ : syracuseStep 1319291 = 1978937) B1978937
theorem B5611963 : Blo 583288 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B1319561 : Blo 583288 1319561 := bstep (se 2 (by rfl) ⟨494835, by rfl⟩ : syracuseStep 1319561 = 989671) B989671
theorem B4006567 : Blo 583288 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B56959685 : Blo 583288 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B2958443 : Blo 583288 2958443 := bstep (se 1 (by rfl) ⟨2218832, by rfl⟩ : syracuseStep 2958443 = 4437665) B4437665
theorem B1320443 : Blo 583288 1320443 := bstep (se 1 (by rfl) ⟨990332, by rfl⟩ : syracuseStep 1320443 = 1980665) B1980665
theorem B1484315 : Blo 583288 1484315 := bstep (se 1 (by rfl) ⟨1113236, by rfl⟩ : syracuseStep 1484315 = 2226473) B2226473
theorem B1975913 : Blo 583288 1975913 := bstep (se 2 (by rfl) ⟨740967, by rfl⟩ : syracuseStep 1975913 = 1481935) B1481935
theorem B1320623 : Blo 583288 1320623 := bstep (se 1 (by rfl) ⟨990467, by rfl⟩ : syracuseStep 1320623 = 1980935) B1980935
theorem B1320713 : Blo 583288 1320713 := bstep (se 2 (by rfl) ⟨495267, by rfl⟩ : syracuseStep 1320713 = 990535) B990535
theorem B1877779 : Blo 583288 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B1320929 : Blo 583288 1320929 := bstep (se 2 (by rfl) ⟨495348, by rfl⟩ : syracuseStep 1320929 = 990697) B990697
theorem B1321343 : Blo 583288 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B4991827 : Blo 583288 4991827 := bstep (se 1 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 4991827 = 7487741) B7487741
theorem B3746999 : Blo 583288 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B1486127 : Blo 583288 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B3747151 : Blo 583288 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B4009337 : Blo 583288 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B12660475 : Blo 583288 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B28422251 : Blo 583288 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B4731301 : Blo 583288 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B6763175 : Blo 583288 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B3748639 : Blo 583288 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B73905209 : Blo 583288 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B2602451 : Blo 583288 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B833179 : Blo 583288 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B6665975 : Blo 583288 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B1980395 : Blo 583288 1980395 := bstep (se 1 (by rfl) ⟨1485296, by rfl⟩ : syracuseStep 1980395 = 2970593) B2970593
theorem B5618267 : Blo 583288 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B1784555 : Blo 583288 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B3324833 : Blo 583288 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B2964761 : Blo 583288 2964761 := bstep (se 2 (by rfl) ⟨1111785, by rfl⟩ : syracuseStep 2964761 = 2223571) B2223571
theorem B1687007 : Blo 583288 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B4439609 : Blo 583288 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B835753 : Blo 583288 835753 := bstep (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) B626815
theorem B738487 : Blo 583288 738487 := bstep (se 1 (by rfl) ⟨553865, by rfl⟩ : syracuseStep 738487 = 1107731) B1107731
theorem B3556655 : Blo 583288 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B2508079 : Blo 583288 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B10012085 : Blo 583288 10012085 := bstep (se 5 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 10012085 = 938633) B938633
theorem B2967677 : Blo 583288 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B7489745 : Blo 583288 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B7227967 : Blo 583288 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B2215127 : Blo 583288 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B937583 : Blo 583288 937583 := bstep (se 1 (by rfl) ⟨703187, by rfl⟩ : syracuseStep 937583 = 1406375) B1406375
theorem B937865 : Blo 583288 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B3329981 : Blo 583288 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B81154001 : Blo 583288 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B741403 : Blo 583288 741403 := bstep (se 1 (by rfl) ⟨556052, by rfl⟩ : syracuseStep 741403 = 1112105) B1112105
theorem B7622849 : Blo 583288 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B51433865 : Blo 583288 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B6312593 : Blo 583288 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B4739897 : Blo 583288 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B2970431 : Blo 583288 2970431 := bstep (se 1 (by rfl) ⟨2227823, by rfl⟩ : syracuseStep 2970431 = 4455647) B4455647
theorem B3330983 : Blo 583288 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B13686245 : Blo 583288 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B2218043 : Blo 583288 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B1661323 : Blo 583288 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B875303 : Blo 583288 875303 := bstep (se 1 (by rfl) ⟨656477, by rfl⟩ : syracuseStep 875303 = 1312955) B1312955
theorem B875327 : Blo 583288 875327 := bstep (se 1 (by rfl) ⟨656495, by rfl⟩ : syracuseStep 875327 = 1312991) B1312991
theorem B3759043 : Blo 583288 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B875627 : Blo 583288 875627 := bstep (se 1 (by rfl) ⟨656720, by rfl⟩ : syracuseStep 875627 = 1313441) B1313441
theorem B2809019 : Blo 583288 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B875771 : Blo 583288 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B875867 : Blo 583288 875867 := bstep (se 1 (by rfl) ⟨656900, by rfl⟩ : syracuseStep 875867 = 1313801) B1313801
theorem B875897 : Blo 583288 875897 := bstep (se 2 (by rfl) ⟨328461, by rfl⟩ : syracuseStep 875897 = 656923) B656923
theorem B875903 : Blo 583288 875903 := bstep (se 1 (by rfl) ⟨656927, by rfl⟩ : syracuseStep 875903 = 1313855) B1313855
theorem B1662383 : Blo 583288 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B4742819 : Blo 583288 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B876455 : Blo 583288 876455 := bstep (se 1 (by rfl) ⟨657341, by rfl⟩ : syracuseStep 876455 = 1314683) B1314683
theorem B876527 : Blo 583288 876527 := bstep (se 1 (by rfl) ⟨657395, by rfl⟩ : syracuseStep 876527 = 1314791) B1314791
theorem B7495739 : Blo 583288 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B876647 : Blo 583288 876647 := bstep (se 1 (by rfl) ⟨657485, by rfl⟩ : syracuseStep 876647 = 1314971) B1314971
theorem B3760273 : Blo 583288 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B876779 : Blo 583288 876779 := bstep (se 1 (by rfl) ⟨657584, by rfl⟩ : syracuseStep 876779 = 1315169) B1315169
theorem B876839 : Blo 583288 876839 := bstep (se 1 (by rfl) ⟨657629, by rfl⟩ : syracuseStep 876839 = 1315259) B1315259
theorem B6644105 : Blo 583288 6644105 := bstep (se 2 (by rfl) ⟨2491539, by rfl⟩ : syracuseStep 6644105 = 4983079) B4983079
theorem B10838681 : Blo 583288 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B877289 : Blo 583288 877289 := bstep (se 2 (by rfl) ⟨328983, by rfl⟩ : syracuseStep 877289 = 657967) B657967
theorem B7627529 : Blo 583288 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B1663841 : Blo 583288 1663841 := bstep (se 2 (by rfl) ⟨623940, by rfl⟩ : syracuseStep 1663841 = 1247881) B1247881
theorem B877679 : Blo 583288 877679 := bstep (se 1 (by rfl) ⟨658259, by rfl⟩ : syracuseStep 877679 = 1316519) B1316519
theorem B877799 : Blo 583288 877799 := bstep (se 1 (by rfl) ⟨658349, by rfl⟩ : syracuseStep 877799 = 1316699) B1316699
theorem B877865 : Blo 583288 877865 := bstep (se 2 (by rfl) ⟨329199, by rfl⟩ : syracuseStep 877865 = 658399) B658399
theorem B5334427 : Blo 583288 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B878135 : Blo 583288 878135 := bstep (se 1 (by rfl) ⟨658601, by rfl⟩ : syracuseStep 878135 = 1317203) B1317203
theorem B583323 : Blo 583288 583323 := bstep (se 1 (by rfl) ⟨437492, by rfl⟩ : syracuseStep 583323 = 874985) B874985
theorem B13723337 : Blo 583288 13723337 := bstep (se 2 (by rfl) ⟨5146251, by rfl⟩ : syracuseStep 13723337 = 10292503) B10292503
theorem B878459 : Blo 583288 878459 := bstep (se 1 (by rfl) ⟨658844, by rfl⟩ : syracuseStep 878459 = 1317689) B1317689
theorem B583583 : Blo 583288 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B878495 : Blo 583288 878495 := bstep (se 1 (by rfl) ⟨658871, by rfl⟩ : syracuseStep 878495 = 1317743) B1317743
theorem B583591 : Blo 583288 583591 := bstep (se 1 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 583591 = 875387) B875387
theorem B878729 : Blo 583288 878729 := bstep (se 2 (by rfl) ⟨329523, by rfl⟩ : syracuseStep 878729 = 659047) B659047
theorem B18016505 : Blo 583288 18016505 := bstep (se 2 (by rfl) ⟨6756189, by rfl⟩ : syracuseStep 18016505 = 13512379) B13512379
theorem B878879 : Blo 583288 878879 := bstep (se 1 (by rfl) ⟨659159, by rfl⟩ : syracuseStep 878879 = 1318319) B1318319
theorem B878927 : Blo 583288 878927 := bstep (se 1 (by rfl) ⟨659195, by rfl⟩ : syracuseStep 878927 = 1318391) B1318391
theorem B879017 : Blo 583288 879017 := bstep (se 2 (by rfl) ⟨329631, by rfl⟩ : syracuseStep 879017 = 659263) B659263
theorem B584167 : Blo 583288 584167 := bstep (se 1 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 584167 = 876251) B876251
theorem B2222599 : Blo 583288 2222599 := bstep (se 1 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 2222599 = 3333899) B3333899
theorem B584347 : Blo 583288 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B2222873 : Blo 583288 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B879401 : Blo 583288 879401 := bstep (se 2 (by rfl) ⟨329775, by rfl⟩ : syracuseStep 879401 = 659551) B659551
theorem B1108961 : Blo 583288 1108961 := bstep (se 2 (by rfl) ⟨415860, by rfl⟩ : syracuseStep 1108961 = 831721) B831721
theorem B879611 : Blo 583288 879611 := bstep (se 1 (by rfl) ⟨659708, by rfl⟩ : syracuseStep 879611 = 1319417) B1319417
theorem B879671 : Blo 583288 879671 := bstep (se 1 (by rfl) ⟨659753, by rfl⟩ : syracuseStep 879671 = 1319507) B1319507
theorem B584815 : Blo 583288 584815 := bstep (se 1 (by rfl) ⟨438611, by rfl⟩ : syracuseStep 584815 = 877223) B877223
theorem B879791 : Blo 583288 879791 := bstep (se 1 (by rfl) ⟨659843, by rfl⟩ : syracuseStep 879791 = 1319687) B1319687
theorem B584895 : Blo 583288 584895 := bstep (se 1 (by rfl) ⟨438671, by rfl⟩ : syracuseStep 584895 = 877343) B877343
theorem B584911 : Blo 583288 584911 := bstep (se 1 (by rfl) ⟨438683, by rfl⟩ : syracuseStep 584911 = 877367) B877367
theorem B56847581 : Blo 583288 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B879851 : Blo 583288 879851 := bstep (se 1 (by rfl) ⟨659888, by rfl⟩ : syracuseStep 879851 = 1319777) B1319777
theorem B13495567 : Blo 583288 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B3173687 : Blo 583288 3173687 := bstep (se 1 (by rfl) ⟨2380265, by rfl⟩ : syracuseStep 3173687 = 4760531) B4760531
theorem B585031 : Blo 583288 585031 := bstep (se 1 (by rfl) ⟨438773, by rfl⟩ : syracuseStep 585031 = 877547) B877547
theorem B1109857 : Blo 583288 1109857 := bstep (se 2 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 1109857 = 832393) B832393
theorem B880511 : Blo 583288 880511 := bstep (se 1 (by rfl) ⟨660383, by rfl⟩ : syracuseStep 880511 = 1320767) B1320767
theorem B2813885 : Blo 583288 2813885 := bstep (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) B1055207
theorem B585759 : Blo 583288 585759 := bstep (se 1 (by rfl) ⟨439319, by rfl⟩ : syracuseStep 585759 = 878639) B878639
theorem B585935 : Blo 583288 585935 := bstep (se 1 (by rfl) ⟨439451, by rfl⟩ : syracuseStep 585935 = 878903) B878903
theorem B880847 : Blo 583288 880847 := bstep (se 1 (by rfl) ⟨660635, by rfl⟩ : syracuseStep 880847 = 1321271) B1321271
theorem B586055 : Blo 583288 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B11268517 : Blo 583288 11268517 := bstep (se 4 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 11268517 = 2112847) B2112847
theorem B586523 : Blo 583288 586523 := bstep (se 1 (by rfl) ⟨439892, by rfl⟩ : syracuseStep 586523 = 879785) B879785
theorem B1111087 : Blo 583288 1111087 := bstep (se 1 (by rfl) ⟨833315, by rfl⟩ : syracuseStep 1111087 = 1666631) B1666631
theorem B586799 : Blo 583288 586799 := bstep (se 1 (by rfl) ⟨440099, by rfl⟩ : syracuseStep 586799 = 880199) B880199
theorem B586919 : Blo 583288 586919 := bstep (se 1 (by rfl) ⟨440189, by rfl⟩ : syracuseStep 586919 = 880379) B880379
theorem B3339731 : Blo 583288 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B3339913 : Blo 583288 3339913 := bstep (se 2 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 3339913 = 2504935) B2504935
theorem B1112059 : Blo 583288 1112059 := bstep (se 1 (by rfl) ⟨834044, by rfl⟩ : syracuseStep 1112059 = 1668089) B1668089
theorem B3340871 : Blo 583288 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B6421265 : Blo 583288 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B1113115 : Blo 583288 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B1408411 : Blo 583288 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B1670777 : Blo 583288 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B5013697 : Blo 583288 5013697 := bstep (se 2 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 5013697 = 3760273) B3760273
theorem B1114337 : Blo 583288 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B2228903 : Blo 583288 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B8454851 : Blo 583288 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B3802625 : Blo 583288 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B984649 : Blo 583288 984649 := bstep (se 2 (by rfl) ⟨369243, by rfl⟩ : syracuseStep 984649 = 738487) B738487
theorem B3344105 : Blo 583288 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B7112569 : Blo 583288 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B4458563 : Blo 583288 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B1476751 : Blo 583288 1476751 := bstep (se 1 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 1476751 = 2215127) B2215127
theorem B25233605 : Blo 583288 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B625055 : Blo 583288 625055 := bstep (se 1 (by rfl) ⟨468791, by rfl⟩ : syracuseStep 625055 = 937583) B937583
theorem B625243 : Blo 583288 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B54102667 : Blo 583288 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B1314215 : Blo 583288 1314215 := bstep (se 1 (by rfl) ⟨985661, by rfl⟩ : syracuseStep 1314215 = 1971323) B1971323
theorem B9637289 : Blo 583288 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B21368357 : Blo 583288 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B986735 : Blo 583288 986735 := bstep (se 1 (by rfl) ⟨740051, by rfl⟩ : syracuseStep 986735 = 1480103) B1480103
theorem B6753935 : Blo 583288 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B6655769 : Blo 583288 6655769 := bstep (se 2 (by rfl) ⟨2495913, by rfl⟩ : syracuseStep 6655769 = 4991827) B4991827
theorem B1970135 : Blo 583288 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B1478695 : Blo 583288 1478695 := bstep (se 1 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 1478695 = 2218043) B2218043
theorem B1970297 : Blo 583288 1970297 := bstep (se 2 (by rfl) ⟨738861, by rfl⟩ : syracuseStep 1970297 = 1477723) B1477723
theorem B17994089 : Blo 583288 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B16880633 : Blo 583288 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B1479809 : Blo 583288 1479809 := bstep (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) B1109857
theorem B2102527 : Blo 583288 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B988537 : Blo 583288 988537 := bstep (se 2 (by rfl) ⟨370701, by rfl⟩ : syracuseStep 988537 = 741403) B741403
theorem B1316303 : Blo 583288 1316303 := bstep (se 1 (by rfl) ⟨987227, by rfl⟩ : syracuseStep 1316303 = 1974455) B1974455
theorem B4429403 : Blo 583288 4429403 := bstep (se 1 (by rfl) ⟨3322052, by rfl⟩ : syracuseStep 4429403 = 6644105) B6644105
theorem B5085019 : Blo 583288 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B1972295 : Blo 583288 1972295 := bstep (se 1 (by rfl) ⟨1479221, by rfl⟩ : syracuseStep 1972295 = 2958443) B2958443
theorem B1317113 : Blo 583288 1317113 := bstep (se 2 (by rfl) ⟨493917, by rfl⟩ : syracuseStep 1317113 = 987835) B987835
theorem B989543 : Blo 583288 989543 := bstep (se 1 (by rfl) ⟨742157, by rfl⟩ : syracuseStep 989543 = 1484315) B1484315
theorem B1317275 : Blo 583288 1317275 := bstep (se 1 (by rfl) ⟨987956, by rfl⟩ : syracuseStep 1317275 = 1975913) B1975913
theorem B9148891 : Blo 583288 9148891 := bstep (se 1 (by rfl) ⟨6861668, by rfl⟩ : syracuseStep 9148891 = 13723337) B13723337
theorem B1481449 : Blo 583288 1481449 := bstep (se 2 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 1481449 = 1111087) B1111087
theorem B1481915 : Blo 583288 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B2497999 : Blo 583288 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B7511525 : Blo 583288 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B990751 : Blo 583288 990751 := bstep (se 1 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 990751 = 1486127) B1486127
theorem B1875923 : Blo 583288 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1482745 : Blo 583288 1482745 := bstep (se 2 (by rfl) ⟨556029, by rfl⟩ : syracuseStep 1482745 = 1112059) B1112059
theorem B18948167 : Blo 583288 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B1320263 : Blo 583288 1320263 := bstep (se 1 (by rfl) ⟨990197, by rfl⟩ : syracuseStep 1320263 = 1980395) B1980395
theorem B1484153 : Blo 583288 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B3745511 : Blo 583288 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B1189703 : Blo 583288 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B1976345 : Blo 583288 1976345 := bstep (se 2 (by rfl) ⟨741129, by rfl⟩ : syracuseStep 1976345 = 1482259) B1482259
theorem B4204705 : Blo 583288 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B1976507 : Blo 583288 1976507 := bstep (se 1 (by rfl) ⟨1482380, by rfl⟩ : syracuseStep 1976507 = 2964761) B2964761
theorem B1124671 : Blo 583288 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B2959739 : Blo 583288 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B1977209 : Blo 583288 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B20327597 : Blo 583288 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B7482617 : Blo 583288 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B2371103 : Blo 583288 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1978451 : Blo 583288 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B4993163 : Blo 583288 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B2503705 : Blo 583288 2503705 := bstep (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) B1877779
theorem B34289243 : Blo 583288 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B2373437 : Blo 583288 2373437 := bstep (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) B890039
theorem B3159931 : Blo 583288 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B1980287 : Blo 583288 1980287 := bstep (se 1 (by rfl) ⟨1485215, by rfl⟩ : syracuseStep 1980287 = 2970431) B2970431
theorem B6076417 : Blo 583288 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B2963465 : Blo 583288 2963465 := bstep (se 2 (by rfl) ⟨1111299, by rfl⟩ : syracuseStep 2963465 = 2222599) B2222599
theorem B9124163 : Blo 583288 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B34322899 : Blo 583288 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B4996201 : Blo 583288 4996201 := bstep (se 2 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 4996201 = 3747151) B3747151
theorem B247053635 : Blo 583288 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B3161879 : Blo 583288 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B4997159 : Blo 583288 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B7225787 : Blo 583288 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B15024689 : Blo 583288 15024689 := bstep (se 2 (by rfl) ⟨5634258, by rfl⟩ : syracuseStep 15024689 = 11268517) B11268517
theorem B7520957 : Blo 583288 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B4998185 : Blo 583288 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B12011003 : Blo 583288 12011003 := bstep (se 1 (by rfl) ⟨9008252, by rfl⟩ : syracuseStep 12011003 = 18016505) B18016505
theorem B739307 : Blo 583288 739307 := bstep (se 1 (by rfl) ⟨554480, by rfl⟩ : syracuseStep 739307 = 1108961) B1108961
theorem B37898387 : Blo 583288 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B2115791 : Blo 583288 2115791 := bstep (se 1 (by rfl) ⟨1586843, by rfl⟩ : syracuseStep 2115791 = 3173687) B3173687
theorem B2672891 : Blo 583288 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B4508783 : Blo 583288 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B7490717 : Blo 583288 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B2215097 : Blo 583288 2215097 := bstep (se 2 (by rfl) ⟨830661, by rfl⟩ : syracuseStep 2215097 = 1661323) B1661323
theorem B49270139 : Blo 583288 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B4443983 : Blo 583288 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B18927665 : Blo 583288 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B4280843 : Blo 583288 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B2216555 : Blo 583288 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B7231315 : Blo 583288 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B6674723 : Blo 583288 6674723 := bstep (se 1 (by rfl) ⟨5006042, by rfl⟩ : syracuseStep 6674723 = 10012085) B10012085
theorem B875135 : Blo 583288 875135 := bstep (se 1 (by rfl) ⟨656351, by rfl⟩ : syracuseStep 875135 = 1312703) B1312703
theorem B875273 : Blo 583288 875273 := bstep (se 2 (by rfl) ⟨328227, by rfl⟩ : syracuseStep 875273 = 656455) B656455
theorem B875513 : Blo 583288 875513 := bstep (se 2 (by rfl) ⟨328317, by rfl⟩ : syracuseStep 875513 = 656635) B656635
theorem B16833581 : Blo 583288 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B1072211 : Blo 583288 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B875831 : Blo 583288 875831 := bstep (se 1 (by rfl) ⟨656873, by rfl⟩ : syracuseStep 875831 = 1313747) B1313747
theorem B876011 : Blo 583288 876011 := bstep (se 1 (by rfl) ⟨657008, by rfl⟩ : syracuseStep 876011 = 1314017) B1314017
theorem B3759635 : Blo 583288 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B6315707 : Blo 583288 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B2219987 : Blo 583288 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B876539 : Blo 583288 876539 := bstep (se 1 (by rfl) ⟨657404, by rfl⟩ : syracuseStep 876539 = 1314809) B1314809
theorem B1663031 : Blo 583288 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B876599 : Blo 583288 876599 := bstep (se 1 (by rfl) ⟨657449, by rfl⟩ : syracuseStep 876599 = 1314899) B1314899
theorem B876671 : Blo 583288 876671 := bstep (se 1 (by rfl) ⟨657503, by rfl⟩ : syracuseStep 876671 = 1315007) B1315007
theorem B876719 : Blo 583288 876719 := bstep (se 1 (by rfl) ⟨657539, by rfl⟩ : syracuseStep 876719 = 1315079) B1315079
theorem B5005907 : Blo 583288 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B2220655 : Blo 583288 2220655 := bstep (se 1 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 2220655 = 3330983) B3330983
theorem B877439 : Blo 583288 877439 := bstep (se 1 (by rfl) ⟨658079, by rfl⟩ : syracuseStep 877439 = 1316159) B1316159
theorem B877511 : Blo 583288 877511 := bstep (se 1 (by rfl) ⟨658133, by rfl⟩ : syracuseStep 877511 = 1316267) B1316267
theorem B877871 : Blo 583288 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B878111 : Blo 583288 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B583535 : Blo 583288 583535 := bstep (se 1 (by rfl) ⟨437651, by rfl⟩ : syracuseStep 583535 = 875303) B875303
theorem B583551 : Blo 583288 583551 := bstep (se 1 (by rfl) ⟨437663, by rfl⟩ : syracuseStep 583551 = 875327) B875327
theorem B2254895 : Blo 583288 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B583751 : Blo 583288 583751 := bstep (se 1 (by rfl) ⟨437813, by rfl⟩ : syracuseStep 583751 = 875627) B875627
theorem B583847 : Blo 583288 583847 := bstep (se 1 (by rfl) ⟨437885, by rfl⟩ : syracuseStep 583847 = 875771) B875771
theorem B583911 : Blo 583288 583911 := bstep (se 1 (by rfl) ⟨437933, by rfl⟩ : syracuseStep 583911 = 875867) B875867
theorem B583931 : Blo 583288 583931 := bstep (se 1 (by rfl) ⟨437948, by rfl⟩ : syracuseStep 583931 = 875897) B875897
theorem B583935 : Blo 583288 583935 := bstep (se 1 (by rfl) ⟨437951, by rfl⟩ : syracuseStep 583935 = 875903) B875903
theorem B1108255 : Blo 583288 1108255 := bstep (se 1 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 1108255 = 1662383) B1662383
theorem B879047 : Blo 583288 879047 := bstep (se 1 (by rfl) ⟨659285, by rfl⟩ : syracuseStep 879047 = 1318571) B1318571
theorem B584303 : Blo 583288 584303 := bstep (se 1 (by rfl) ⟨438227, by rfl⟩ : syracuseStep 584303 = 876455) B876455
theorem B584351 : Blo 583288 584351 := bstep (se 1 (by rfl) ⟨438263, by rfl⟩ : syracuseStep 584351 = 876527) B876527
theorem B1665697 : Blo 583288 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B584431 : Blo 583288 584431 := bstep (se 1 (by rfl) ⟨438323, by rfl⟩ : syracuseStep 584431 = 876647) B876647
theorem B879407 : Blo 583288 879407 := bstep (se 1 (by rfl) ⟨659555, by rfl⟩ : syracuseStep 879407 = 1319111) B1319111
theorem B584519 : Blo 583288 584519 := bstep (se 1 (by rfl) ⟨438389, by rfl⟩ : syracuseStep 584519 = 876779) B876779
theorem B584559 : Blo 583288 584559 := bstep (se 1 (by rfl) ⟨438419, by rfl⟩ : syracuseStep 584559 = 876839) B876839
theorem B879527 : Blo 583288 879527 := bstep (se 1 (by rfl) ⟨659645, by rfl⟩ : syracuseStep 879527 = 1319291) B1319291
theorem B879707 : Blo 583288 879707 := bstep (se 1 (by rfl) ⟨659780, by rfl⟩ : syracuseStep 879707 = 1319561) B1319561
theorem B37973123 : Blo 583288 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B584859 : Blo 583288 584859 := bstep (se 1 (by rfl) ⟨438644, by rfl⟩ : syracuseStep 584859 = 877289) B877289
theorem B1109227 : Blo 583288 1109227 := bstep (se 1 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 1109227 = 1663841) B1663841
theorem B585119 : Blo 583288 585119 := bstep (se 1 (by rfl) ⟨438839, by rfl⟩ : syracuseStep 585119 = 877679) B877679
theorem B585199 : Blo 583288 585199 := bstep (se 1 (by rfl) ⟨438899, by rfl⟩ : syracuseStep 585199 = 877799) B877799
theorem B585243 : Blo 583288 585243 := bstep (se 1 (by rfl) ⟨438932, by rfl⟩ : syracuseStep 585243 = 877865) B877865
theorem B880295 : Blo 583288 880295 := bstep (se 1 (by rfl) ⟨660221, by rfl⟩ : syracuseStep 880295 = 1320443) B1320443
theorem B585423 : Blo 583288 585423 := bstep (se 1 (by rfl) ⟨439067, by rfl⟩ : syracuseStep 585423 = 878135) B878135
theorem B21589753 : Blo 583288 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B880415 : Blo 583288 880415 := bstep (se 1 (by rfl) ⟨660311, by rfl⟩ : syracuseStep 880415 = 1320623) B1320623
theorem B880475 : Blo 583288 880475 := bstep (se 1 (by rfl) ⟨660356, by rfl⟩ : syracuseStep 880475 = 1320713) B1320713
theorem B585639 : Blo 583288 585639 := bstep (se 1 (by rfl) ⟨439229, by rfl⟩ : syracuseStep 585639 = 878459) B878459
theorem B585663 : Blo 583288 585663 := bstep (se 1 (by rfl) ⟨439247, by rfl⟩ : syracuseStep 585663 = 878495) B878495
theorem B880619 : Blo 583288 880619 := bstep (se 1 (by rfl) ⟨660464, by rfl⟩ : syracuseStep 880619 = 1320929) B1320929
theorem B585819 : Blo 583288 585819 := bstep (se 1 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 585819 = 878729) B878729
theorem B585919 : Blo 583288 585919 := bstep (se 1 (by rfl) ⟨439439, by rfl⟩ : syracuseStep 585919 = 878879) B878879
theorem B585951 : Blo 583288 585951 := bstep (se 1 (by rfl) ⟨439463, by rfl⟩ : syracuseStep 585951 = 878927) B878927
theorem B880895 : Blo 583288 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B586011 : Blo 583288 586011 := bstep (se 1 (by rfl) ⟨439508, by rfl⟩ : syracuseStep 586011 = 879017) B879017
theorem B586267 : Blo 583288 586267 := bstep (se 1 (by rfl) ⟨439700, by rfl⟩ : syracuseStep 586267 = 879401) B879401
theorem B586407 : Blo 583288 586407 := bstep (se 1 (by rfl) ⟨439805, by rfl⟩ : syracuseStep 586407 = 879611) B879611
theorem B586447 : Blo 583288 586447 := bstep (se 1 (by rfl) ⟨439835, by rfl⟩ : syracuseStep 586447 = 879671) B879671
theorem B586527 : Blo 583288 586527 := bstep (se 1 (by rfl) ⟨439895, by rfl⟩ : syracuseStep 586527 = 879791) B879791
theorem B586567 : Blo 583288 586567 := bstep (se 1 (by rfl) ⟨439925, by rfl⟩ : syracuseStep 586567 = 879851) B879851
theorem B4453217 : Blo 583288 4453217 := bstep (se 2 (by rfl) ⟨1669956, by rfl⟩ : syracuseStep 4453217 = 3339913) B3339913
theorem B1110905 : Blo 583288 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B587007 : Blo 583288 587007 := bstep (se 1 (by rfl) ⟨440255, by rfl⟩ : syracuseStep 587007 = 880511) B880511
theorem B5076361 : Blo 583288 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B587231 : Blo 583288 587231 := bstep (se 1 (by rfl) ⟨440423, by rfl⟩ : syracuseStep 587231 = 880847) B880847
theorem B6649937 : Blo 583288 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B1734967 : Blo 583288 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B2226487 : Blo 583288 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B5012057 : Blo 583288 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B2227247 : Blo 583288 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B1113851 : Blo 583288 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B6684929 : Blo 583288 6684929 := bstep (se 2 (by rfl) ⟨2506848, by rfl⟩ : syracuseStep 6684929 = 5013697) B5013697
theorem B4817191 : Blo 583288 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B5013971 : Blo 583288 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B5636567 : Blo 583288 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B2229403 : Blo 583288 2229403 := bstep (se 1 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 2229403 = 3344105) B3344105
theorem B25265591 : Blo 583288 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B1410527 : Blo 583288 1410527 := bstep (se 1 (by rfl) ⟨1057895, by rfl⟩ : syracuseStep 1410527 = 2115791) B2115791
theorem B1312865 : Blo 583288 1312865 := bstep (se 2 (by rfl) ⟨492324, by rfl⟩ : syracuseStep 1312865 = 984649) B984649
theorem B1476731 : Blo 583288 1476731 := bstep (se 1 (by rfl) ⟨1107548, by rfl⟩ : syracuseStep 1476731 = 2215097) B2215097
theorem B6424859 : Blo 583288 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B657823 : Blo 583288 657823 := bstep (se 1 (by rfl) ⟨493367, by rfl⟩ : syracuseStep 657823 = 986735) B986735
theorem B1313423 : Blo 583288 1313423 := bstep (se 1 (by rfl) ⟨985067, by rfl⟩ : syracuseStep 1313423 = 1970135) B1970135
theorem B12618443 : Blo 583288 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B1313531 : Blo 583288 1313531 := bstep (se 1 (by rfl) ⟨985148, by rfl⟩ : syracuseStep 1313531 = 1970297) B1970297
theorem B1969001 : Blo 583288 1969001 := bstep (se 2 (by rfl) ⟨738375, by rfl⟩ : syracuseStep 1969001 = 1476751) B1476751
theorem B5606273 : Blo 583288 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B2853895 : Blo 583288 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B1477673 : Blo 583288 1477673 := bstep (se 2 (by rfl) ⟨554127, by rfl⟩ : syracuseStep 1477673 = 1108255) B1108255
theorem B1477703 : Blo 583288 1477703 := bstep (se 1 (by rfl) ⟨1108277, by rfl⟩ : syracuseStep 1477703 = 2216555) B2216555
theorem B986539 : Blo 583288 986539 := bstep (se 1 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 986539 = 1479809) B1479809
theorem B2952935 : Blo 583288 2952935 := bstep (se 1 (by rfl) ⟨2214701, by rfl⟩ : syracuseStep 2952935 = 4429403) B4429403
theorem B1314863 : Blo 583288 1314863 := bstep (se 1 (by rfl) ⟨986147, by rfl⟩ : syracuseStep 1314863 = 1972295) B1972295
theorem B659695 : Blo 583288 659695 := bstep (se 1 (by rfl) ⟨494771, by rfl⟩ : syracuseStep 659695 = 989543) B989543
theorem B1478969 : Blo 583288 1478969 := bstep (se 2 (by rfl) ⟨554613, by rfl⟩ : syracuseStep 1478969 = 1109227) B1109227
theorem B987943 : Blo 583288 987943 := bstep (se 1 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 987943 = 1481915) B1481915
theorem B1971485 : Blo 583288 1971485 := bstep (se 3 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 1971485 = 739307) B739307
theorem B1479991 : Blo 583288 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B1250615 : Blo 583288 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B1971593 : Blo 583288 1971593 := bstep (se 2 (by rfl) ⟨739347, by rfl⟩ : syracuseStep 1971593 = 1478695) B1478695
theorem B989435 : Blo 583288 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B2497007 : Blo 583288 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B793135 : Blo 583288 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B1317563 : Blo 583288 1317563 := bstep (se 1 (by rfl) ⟨988172, by rfl⟩ : syracuseStep 1317563 = 1976345) B1976345
theorem B1317671 : Blo 583288 1317671 := bstep (se 1 (by rfl) ⟨988253, by rfl⟩ : syracuseStep 1317671 = 1976507) B1976507
theorem B1973159 : Blo 583288 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B1318049 : Blo 583288 1318049 := bstep (se 2 (by rfl) ⟨494268, by rfl⟩ : syracuseStep 1318049 = 988537) B988537
theorem B1318139 : Blo 583288 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B4988411 : Blo 583288 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B1580735 : Blo 583288 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B9641753 : Blo 583288 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B8101889 : Blo 583288 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B1318967 : Blo 583288 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B2859229 : Blo 583288 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B12198521 : Blo 583288 12198521 := bstep (se 2 (by rfl) ⟨4574445, by rfl⟩ : syracuseStep 12198521 = 9148891) B9148891
theorem B1975265 : Blo 583288 1975265 := bstep (se 2 (by rfl) ⟨740724, by rfl⟩ : syracuseStep 1975265 = 1481449) B1481449
theorem B1582291 : Blo 583288 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1320191 : Blo 583288 1320191 := bstep (se 1 (by rfl) ⟨990143, by rfl⟩ : syracuseStep 1320191 = 1980287) B1980287
theorem B1975643 : Blo 583288 1975643 := bstep (se 1 (by rfl) ⟨1481732, by rfl⟩ : syracuseStep 1975643 = 2963465) B2963465
theorem B4433291 : Blo 583288 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B6661601 : Blo 583288 6661601 := bstep (se 2 (by rfl) ⟨2498100, by rfl⟩ : syracuseStep 6661601 = 4996201) B4996201
theorem B1484831 : Blo 583288 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B1321001 : Blo 583288 1321001 := bstep (se 2 (by rfl) ⟨495375, by rfl⟩ : syracuseStep 1321001 = 990751) B990751
theorem B164702423 : Blo 583288 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B2107919 : Blo 583288 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B1976993 : Blo 583288 1976993 := bstep (se 2 (by rfl) ⟨741372, by rfl⟩ : syracuseStep 1976993 = 1482745) B1482745
theorem B4434749 : Blo 583288 4434749 := bstep (se 3 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 4434749 = 1663031) B1663031
theorem B1485935 : Blo 583288 1485935 := bstep (se 1 (by rfl) ⟨1114451, by rfl⟩ : syracuseStep 1485935 = 2228903) B2228903
theorem B2960873 : Blo 583288 2960873 := bstep (se 2 (by rfl) ⟨1110327, by rfl⟩ : syracuseStep 2960873 = 2220655) B2220655
theorem B47984237 : Blo 583288 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B8007335 : Blo 583288 8007335 := bstep (se 1 (by rfl) ⟨6005501, by rfl⟩ : syracuseStep 8007335 = 12011003) B12011003
theorem B2535083 : Blo 583288 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B16822403 : Blo 583288 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B1781927 : Blo 583288 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B4993811 : Blo 583288 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B32846759 : Blo 583288 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B4502623 : Blo 583288 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B9483425 : Blo 583288 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B4437179 : Blo 583288 4437179 := bstep (se 1 (by rfl) ⟨3327884, by rfl⟩ : syracuseStep 4437179 = 6655769) B6655769
theorem B2962655 : Blo 583288 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B11253755 : Blo 583288 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B833657 : Blo 583288 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B72136889 : Blo 583288 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B11222387 : Blo 583288 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B28786337 : Blo 583288 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B2506423 : Blo 583288 2506423 := bstep (se 1 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 2506423 = 3759635) B3759635
theorem B4210471 : Blo 583288 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B12632111 : Blo 583288 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B2803369 : Blo 583288 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B6768481 : Blo 583288 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B25315415 : Blo 583288 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B13551731 : Blo 583288 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B4213241 : Blo 583288 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B3328775 : Blo 583288 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B2313289 : Blo 583288 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B2968649 : Blo 583288 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B2968811 : Blo 583288 2968811 := bstep (se 1 (by rfl) ⟨2226608, by rfl⟩ : syracuseStep 2968811 = 4453217) B4453217
theorem B740603 : Blo 583288 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B45763865 : Blo 583288 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B22859495 : Blo 583288 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B6082775 : Blo 583288 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B3330665 : Blo 583288 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B2970269 : Blo 583288 2970269 := bstep (se 3 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 2970269 = 1113851) B1113851
theorem B3331439 : Blo 583288 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B10016459 : Blo 583288 10016459 := bstep (se 1 (by rfl) ⟨7512344, by rfl⟩ : syracuseStep 10016459 = 15024689) B15024689
theorem B2971565 : Blo 583288 2971565 := bstep (se 3 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 2971565 = 1114337) B1114337
theorem B3332123 : Blo 583288 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B2972375 : Blo 583288 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B3005855 : Blo 583288 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B876143 : Blo 583288 876143 := bstep (se 1 (by rfl) ⟨657107, by rfl⟩ : syracuseStep 876143 = 1314215) B1314215
theorem B14245571 : Blo 583288 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B1499561 : Blo 583288 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B2220929 : Blo 583288 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B877535 : Blo 583288 877535 := bstep (se 1 (by rfl) ⟨658151, by rfl⟩ : syracuseStep 877535 = 1316303) B1316303
theorem B878075 : Blo 583288 878075 := bstep (se 1 (by rfl) ⟨658556, by rfl⟩ : syracuseStep 878075 = 1317113) B1317113
theorem B4449815 : Blo 583288 4449815 := bstep (se 1 (by rfl) ⟨3337361, by rfl⟩ : syracuseStep 4449815 = 6674723) B6674723
theorem B878183 : Blo 583288 878183 := bstep (se 1 (by rfl) ⟨658637, by rfl⟩ : syracuseStep 878183 = 1317275) B1317275
theorem B583423 : Blo 583288 583423 := bstep (se 1 (by rfl) ⟨437567, by rfl⟩ : syracuseStep 583423 = 875135) B875135
theorem B583515 : Blo 583288 583515 := bstep (se 1 (by rfl) ⟨437636, by rfl⟩ : syracuseStep 583515 = 875273) B875273
theorem B583675 : Blo 583288 583675 := bstep (se 1 (by rfl) ⟨437756, by rfl⟩ : syracuseStep 583675 = 875513) B875513
theorem B583887 : Blo 583288 583887 := bstep (se 1 (by rfl) ⟨437915, by rfl⟩ : syracuseStep 583887 = 875831) B875831
theorem B5007683 : Blo 583288 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B584007 : Blo 583288 584007 := bstep (se 1 (by rfl) ⟨438005, by rfl⟩ : syracuseStep 584007 = 876011) B876011
theorem B584359 : Blo 583288 584359 := bstep (se 1 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 584359 = 876539) B876539
theorem B584399 : Blo 583288 584399 := bstep (se 1 (by rfl) ⟨438299, by rfl⟩ : syracuseStep 584399 = 876599) B876599
theorem B584447 : Blo 583288 584447 := bstep (se 1 (by rfl) ⟨438335, by rfl⟩ : syracuseStep 584447 = 876671) B876671
theorem B584479 : Blo 583288 584479 := bstep (se 1 (by rfl) ⟨438359, by rfl⟩ : syracuseStep 584479 = 876719) B876719
theorem B3337271 : Blo 583288 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B584959 : Blo 583288 584959 := bstep (se 1 (by rfl) ⟨438719, by rfl⟩ : syracuseStep 584959 = 877439) B877439
theorem B585007 : Blo 583288 585007 := bstep (se 1 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 585007 = 877511) B877511
theorem B585247 : Blo 583288 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B880175 : Blo 583288 880175 := bstep (se 1 (by rfl) ⟨660131, by rfl⟩ : syracuseStep 880175 = 1320263) B1320263
theorem B585407 : Blo 583288 585407 := bstep (se 1 (by rfl) ⟨439055, by rfl⟩ : syracuseStep 585407 = 878111) B878111
theorem B1666813 : Blo 583288 1666813 := bstep (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) B625055
theorem B1503263 : Blo 583288 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B3338273 : Blo 583288 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B586031 : Blo 583288 586031 := bstep (se 1 (by rfl) ⟨439523, by rfl⟩ : syracuseStep 586031 = 879047) B879047
theorem B586271 : Blo 583288 586271 := bstep (se 1 (by rfl) ⟨439703, by rfl⟩ : syracuseStep 586271 = 879407) B879407
theorem B586351 : Blo 583288 586351 := bstep (se 1 (by rfl) ⟨439763, by rfl⟩ : syracuseStep 586351 = 879527) B879527
theorem B586471 : Blo 583288 586471 := bstep (se 1 (by rfl) ⟨439853, by rfl⟩ : syracuseStep 586471 = 879707) B879707
theorem B586863 : Blo 583288 586863 := bstep (se 1 (by rfl) ⟨440147, by rfl⟩ : syracuseStep 586863 = 880295) B880295
theorem B6780025 : Blo 583288 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B586943 : Blo 583288 586943 := bstep (se 1 (by rfl) ⟨440207, by rfl⟩ : syracuseStep 586943 = 880415) B880415
theorem B586983 : Blo 583288 586983 := bstep (se 1 (by rfl) ⟨440237, by rfl⟩ : syracuseStep 586983 = 880475) B880475
theorem B587079 : Blo 583288 587079 := bstep (se 1 (by rfl) ⟨440309, by rfl⟩ : syracuseStep 587079 = 880619) B880619
theorem B587263 : Blo 583288 587263 := bstep (se 1 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 587263 = 880895) B880895
theorem B3341371 : Blo 583288 3341371 := bstep (se 1 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 3341371 = 5012057) B5012057
theorem B8421407 : Blo 583288 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B4456619 : Blo 583288 4456619 := bstep (se 1 (by rfl) ⟨3342464, by rfl⟩ : syracuseStep 4456619 = 6684929) B6684929
theorem B3342647 : Blo 583288 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B6422921 : Blo 583288 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B16843727 : Blo 583288 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B16876943 : Blo 583288 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B984487 : Blo 583288 984487 := bstep (se 1 (by rfl) ⟨738365, by rfl⟩ : syracuseStep 984487 = 1476731) B1476731
theorem B1312667 : Blo 583288 1312667 := bstep (se 1 (by rfl) ⟨984500, by rfl⟩ : syracuseStep 1312667 = 1969001) B1969001
theorem B3737515 : Blo 583288 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B985115 : Blo 583288 985115 := bstep (se 1 (by rfl) ⟨738836, by rfl⟩ : syracuseStep 985115 = 1477673) B1477673
theorem B985135 : Blo 583288 985135 := bstep (se 1 (by rfl) ⟨738851, by rfl⟩ : syracuseStep 985135 = 1477703) B1477703
theorem B30509243 : Blo 583288 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B3737825 : Blo 583288 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B1968623 : Blo 583288 1968623 := bstep (se 1 (by rfl) ⟨1476467, by rfl⟩ : syracuseStep 1968623 = 2952935) B2952935
theorem B15239663 : Blo 583288 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B985979 : Blo 583288 985979 := bstep (se 1 (by rfl) ⟨739484, by rfl⟩ : syracuseStep 985979 = 1478969) B1478969
theorem B4230053 : Blo 583288 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B1314323 : Blo 583288 1314323 := bstep (se 1 (by rfl) ⟨985742, by rfl⟩ : syracuseStep 1314323 = 1971485) B1971485
theorem B1314395 : Blo 583288 1314395 := bstep (se 1 (by rfl) ⟨985796, by rfl⟩ : syracuseStep 1314395 = 1971593) B1971593
theorem B3805193 : Blo 583288 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B659623 : Blo 583288 659623 := bstep (se 1 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 659623 = 989435) B989435
theorem B1315385 : Blo 583288 1315385 := bstep (se 2 (by rfl) ⟨493269, by rfl⟩ : syracuseStep 1315385 = 986539) B986539
theorem B1315439 : Blo 583288 1315439 := bstep (se 1 (by rfl) ⟨986579, by rfl⟩ : syracuseStep 1315439 = 1973159) B1973159
theorem B2003903 : Blo 583288 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B1053823 : Blo 583288 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B6427835 : Blo 583288 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B8132347 : Blo 583288 8132347 := bstep (se 1 (by rfl) ⟨6099260, by rfl⟩ : syracuseStep 8132347 = 12198521) B12198521
theorem B1480619 : Blo 583288 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B1316843 : Blo 583288 1316843 := bstep (se 1 (by rfl) ⟨987632, by rfl⟩ : syracuseStep 1316843 = 1975265) B1975265
theorem B1317095 : Blo 583288 1317095 := bstep (se 1 (by rfl) ⟨987821, by rfl⟩ : syracuseStep 1317095 = 1975643) B1975643
theorem B2955527 : Blo 583288 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B1317257 : Blo 583288 1317257 := bstep (se 2 (by rfl) ⟨493971, by rfl⟩ : syracuseStep 1317257 = 987943) B987943
theorem B6658685 : Blo 583288 6658685 := bstep (se 3 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 6658685 = 2497007) B2497007
theorem B989887 : Blo 583288 989887 := bstep (se 1 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 989887 = 1484831) B1484831
theorem B6003497 : Blo 583288 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B1973321 : Blo 583288 1973321 := bstep (se 2 (by rfl) ⟨739995, by rfl⟩ : syracuseStep 1973321 = 1479991) B1479991
theorem B1317995 : Blo 583288 1317995 := bstep (se 1 (by rfl) ⟨988496, by rfl⟩ : syracuseStep 1317995 = 1976993) B1976993
theorem B2956499 : Blo 583288 2956499 := bstep (se 1 (by rfl) ⟨2217374, by rfl⟩ : syracuseStep 2956499 = 4434749) B4434749
theorem B990623 : Blo 583288 990623 := bstep (se 1 (by rfl) ⟨742967, by rfl⟩ : syracuseStep 990623 = 1485935) B1485935
theorem B1973915 : Blo 583288 1973915 := bstep (se 1 (by rfl) ⟨1480436, by rfl⟩ : syracuseStep 1973915 = 2960873) B2960873
theorem B31989491 : Blo 583288 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B11214935 : Blo 583288 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B1187951 : Blo 583288 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B21897839 : Blo 583288 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B1974941 : Blo 583288 1974941 := bstep (se 3 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 1974941 = 740603) B740603
theorem B2958119 : Blo 583288 2958119 := bstep (se 1 (by rfl) ⟨2218589, by rfl⟩ : syracuseStep 2958119 = 4437179) B4437179
theorem B1975103 : Blo 583288 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B37988189 : Blo 583288 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B7481591 : Blo 583288 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B5613961 : Blo 583288 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B4008701 : Blo 583288 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B15249221 : Blo 583288 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2109721 : Blo 583288 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B1979099 : Blo 583288 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B1979207 : Blo 583288 1979207 := bstep (se 1 (by rfl) ⟨1484405, by rfl⟩ : syracuseStep 1979207 = 2968811) B2968811
theorem B9024641 : Blo 583288 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B1980179 : Blo 583288 1980179 := bstep (se 1 (by rfl) ⟨1485134, by rfl⟩ : syracuseStep 1980179 = 2970269) B2970269
theorem B833743 : Blo 583288 833743 := bstep (se 1 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 833743 = 1250615) B1250615
theorem B1981043 : Blo 583288 1981043 := bstep (se 1 (by rfl) ⟨1485782, by rfl⟩ : syracuseStep 1981043 = 2971565) B2971565
theorem B1981583 : Blo 583288 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B3325607 : Blo 583288 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B999707 : Blo 583288 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B12337541 : Blo 583288 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B4441067 : Blo 583288 4441067 := bstep (se 1 (by rfl) ⟨3330800, by rfl⟩ : syracuseStep 4441067 = 6661601) B6661601
theorem B2966543 : Blo 583288 2966543 := bstep (se 1 (by rfl) ⟨2224907, by rfl⟩ : syracuseStep 2966543 = 4449815) B4449815
theorem B1690055 : Blo 583288 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B3329207 : Blo 583288 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B48091259 : Blo 583288 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B19190891 : Blo 583288 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B3757711 : Blo 583288 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B940351 : Blo 583288 940351 := bstep (se 1 (by rfl) ⟨705263, by rfl⟩ : syracuseStep 940351 = 1410527) B1410527
theorem B875243 : Blo 583288 875243 := bstep (se 1 (by rfl) ⟨656432, by rfl⟩ : syracuseStep 875243 = 1312865) B1312865
theorem B9034487 : Blo 583288 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B4283239 : Blo 583288 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B2972537 : Blo 583288 2972537 := bstep (se 2 (by rfl) ⟨1114701, by rfl⟩ : syracuseStep 2972537 = 2229403) B2229403
theorem B2808827 : Blo 583288 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B875615 : Blo 583288 875615 := bstep (se 1 (by rfl) ⟨656711, by rfl⟩ : syracuseStep 875615 = 1313423) B1313423
theorem B8412295 : Blo 583288 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B875687 : Blo 583288 875687 := bstep (se 1 (by rfl) ⟨656765, by rfl⟩ : syracuseStep 875687 = 1313531) B1313531
theorem B2219183 : Blo 583288 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B876575 : Blo 583288 876575 := bstep (se 1 (by rfl) ⟨657431, by rfl⟩ : syracuseStep 876575 = 1314863) B1314863
theorem B4055183 : Blo 583288 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B2220443 : Blo 583288 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B877097 : Blo 583288 877097 := bstep (se 2 (by rfl) ⟨328911, by rfl⟩ : syracuseStep 877097 = 657823) B657823
theorem B2220959 : Blo 583288 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B6677639 : Blo 583288 6677639 := bstep (se 1 (by rfl) ⟨5008229, by rfl⟩ : syracuseStep 6677639 = 10016459) B10016459
theorem B2221415 : Blo 583288 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B878375 : Blo 583288 878375 := bstep (se 1 (by rfl) ⟨658781, by rfl⟩ : syracuseStep 878375 = 1317563) B1317563
theorem B878447 : Blo 583288 878447 := bstep (se 1 (by rfl) ⟨658835, by rfl⟩ : syracuseStep 878447 = 1317671) B1317671
theorem B878699 : Blo 583288 878699 := bstep (se 1 (by rfl) ⟨659024, by rfl⟩ : syracuseStep 878699 = 1318049) B1318049
theorem B878759 : Blo 583288 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B2222417 : Blo 583288 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B584095 : Blo 583288 584095 := bstep (se 1 (by rfl) ⟨438071, by rfl⟩ : syracuseStep 584095 = 876143) B876143
theorem B5401259 : Blo 583288 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B879311 : Blo 583288 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B879593 : Blo 583288 879593 := bstep (se 2 (by rfl) ⟨329847, by rfl⟩ : syracuseStep 879593 = 659695) B659695
theorem B2223085 : Blo 583288 2223085 := bstep (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) B833657
theorem B585023 : Blo 583288 585023 := bstep (se 1 (by rfl) ⟨438767, by rfl⟩ : syracuseStep 585023 = 877535) B877535
theorem B880127 : Blo 583288 880127 := bstep (se 1 (by rfl) ⟨660095, by rfl⟩ : syracuseStep 880127 = 1320191) B1320191
theorem B585383 : Blo 583288 585383 := bstep (se 1 (by rfl) ⟨439037, by rfl⟩ : syracuseStep 585383 = 878075) B878075
theorem B585455 : Blo 583288 585455 := bstep (se 1 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 585455 = 878183) B878183
theorem B880667 : Blo 583288 880667 := bstep (se 1 (by rfl) ⟨660500, by rfl⟩ : syracuseStep 880667 = 1321001) B1321001
theorem B109801615 : Blo 583288 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B9040033 : Blo 583288 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B3338455 : Blo 583288 3338455 := bstep (se 1 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 3338455 = 5007683) B5007683
theorem B1405279 : Blo 583288 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B2224847 : Blo 583288 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B586783 : Blo 583288 586783 := bstep (se 1 (by rfl) ⟨440087, by rfl⟩ : syracuseStep 586783 = 880175) B880175
theorem B5338223 : Blo 583288 5338223 := bstep (se 1 (by rfl) ⟨4003667, by rfl⟩ : syracuseStep 5338223 = 8007335) B8007335
theorem B2225515 : Blo 583288 2225515 := bstep (se 1 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 2225515 = 3338273) B3338273
theorem B6322283 : Blo 583288 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B7502503 : Blo 583288 7502503 := bstep (se 1 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 7502503 = 11253755) B11253755
theorem B4455161 : Blo 583288 4455161 := bstep (se 2 (by rfl) ⟨1670685, by rfl⟩ : syracuseStep 4455161 = 3341371) B3341371
theorem B3341897 : Blo 583288 3341897 := bstep (se 2 (by rfl) ⟨1253211, by rfl⟩ : syracuseStep 3341897 = 2506423) B2506423
theorem B2228431 : Blo 583288 2228431 := bstep (se 1 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 2228431 = 3342647) B3342647
theorem B8225027 : Blo 583288 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B656743 : Blo 583288 656743 := bstep (se 1 (by rfl) ⟨492557, by rfl⟩ : syracuseStep 656743 = 985115) B985115
theorem B2491883 : Blo 583288 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B1312415 : Blo 583288 1312415 := bstep (se 1 (by rfl) ⟨984311, by rfl⟩ : syracuseStep 1312415 = 1968623) B1968623
theorem B10159775 : Blo 583288 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1312649 : Blo 583288 1312649 := bstep (se 2 (by rfl) ⟨492243, by rfl⟩ : syracuseStep 1312649 = 984487) B984487
theorem B657319 : Blo 583288 657319 := bstep (se 1 (by rfl) ⟨492989, by rfl⟩ : syracuseStep 657319 = 985979) B985979
theorem B2820035 : Blo 583288 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B4983353 : Blo 583288 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B1313513 : Blo 583288 1313513 := bstep (se 2 (by rfl) ⟨492567, by rfl⟩ : syracuseStep 1313513 = 985135) B985135
theorem B987079 : Blo 583288 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B1970351 : Blo 583288 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B4002331 : Blo 583288 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B1872551 : Blo 583288 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B1315547 : Blo 583288 1315547 := bstep (se 1 (by rfl) ⟨986660, by rfl⟩ : syracuseStep 1315547 = 1973321) B1973321
theorem B1479455 : Blo 583288 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1970999 : Blo 583288 1970999 := bstep (se 1 (by rfl) ⟨1478249, by rfl⟩ : syracuseStep 1970999 = 2956499) B2956499
theorem B660415 : Blo 583288 660415 := bstep (se 1 (by rfl) ⟨495311, by rfl⟩ : syracuseStep 660415 = 990623) B990623
theorem B1315943 : Blo 583288 1315943 := bstep (se 1 (by rfl) ⟨986957, by rfl⟩ : syracuseStep 1315943 = 1973915) B1973915
theorem B7476623 : Blo 583288 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B1480295 : Blo 583288 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B1316627 : Blo 583288 1316627 := bstep (se 1 (by rfl) ⟨987470, by rfl⟩ : syracuseStep 1316627 = 1974941) B1974941
theorem B1873705 : Blo 583288 1873705 := bstep (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) B1405279
theorem B1972079 : Blo 583288 1972079 := bstep (se 1 (by rfl) ⟨1479059, by rfl⟩ : syracuseStep 1972079 = 2958119) B2958119
theorem B1316735 : Blo 583288 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B1480639 : Blo 583288 1480639 := bstep (se 1 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 1480639 = 2220959) B2220959
theorem B1480943 : Blo 583288 1480943 := bstep (se 1 (by rfl) ⟨1110707, by rfl⟩ : syracuseStep 1480943 = 2221415) B2221415
theorem B4987727 : Blo 583288 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B1481611 : Blo 583288 1481611 := bstep (se 1 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 1481611 = 2222417) B2222417
theorem B10689869 : Blo 583288 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B10166147 : Blo 583288 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B1253801 : Blo 583288 1253801 := bstep (se 2 (by rfl) ⟨470175, by rfl⟩ : syracuseStep 1253801 = 940351) B940351
theorem B1483231 : Blo 583288 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B1319399 : Blo 583288 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B1319471 : Blo 583288 1319471 := bstep (se 1 (by rfl) ⟨989603, by rfl⟩ : syracuseStep 1319471 = 1979207) B1979207
theorem B10003337 : Blo 583288 10003337 := bstep (se 2 (by rfl) ⟨3751251, by rfl⟩ : syracuseStep 10003337 = 7502503) B7502503
theorem B1319849 : Blo 583288 1319849 := bstep (se 2 (by rfl) ⟨494943, by rfl⟩ : syracuseStep 1319849 = 989887) B989887
theorem B5710985 : Blo 583288 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B1320119 : Blo 583288 1320119 := bstep (se 1 (by rfl) ⟨990089, by rfl⟩ : syracuseStep 1320119 = 1980179) B1980179
theorem B11216393 : Blo 583288 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B1320695 : Blo 583288 1320695 := bstep (se 1 (by rfl) ⟨990521, by rfl⟩ : syracuseStep 1320695 = 1981043) B1981043
theorem B1321055 : Blo 583288 1321055 := bstep (se 1 (by rfl) ⟨990791, by rfl⟩ : syracuseStep 1321055 = 1981583) B1981583
theorem B5614271 : Blo 583288 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B2960711 : Blo 583288 2960711 := bstep (se 1 (by rfl) ⟨2220533, by rfl⟩ : syracuseStep 2960711 = 4441067) B4441067
theorem B1977695 : Blo 583288 1977695 := bstep (se 1 (by rfl) ⟨1483271, by rfl⟩ : syracuseStep 1977695 = 2966543) B2966543
theorem B2665885 : Blo 583288 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B11251295 : Blo 583288 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B1126703 : Blo 583288 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B2536795 : Blo 583288 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B7485281 : Blo 583288 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B2964113 : Blo 583288 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B4439123 : Blo 583288 4439123 := bstep (se 1 (by rfl) ⟨3329342, by rfl⟩ : syracuseStep 4439123 = 6658685) B6658685
theorem B1981691 : Blo 583288 1981691 := bstep (se 1 (by rfl) ⟨1486268, by rfl⟩ : syracuseStep 1981691 = 2972537) B2972537
theorem B2703455 : Blo 583288 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B14598559 : Blo 583288 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B2967353 : Blo 583288 2967353 := bstep (se 2 (by rfl) ⟨1112757, by rfl⟩ : syracuseStep 2967353 = 2225515) B2225515
theorem B3558815 : Blo 583288 3558815 := bstep (se 1 (by rfl) ⟨2669111, by rfl⟩ : syracuseStep 3558815 = 5338223) B5338223
theorem B6016427 : Blo 583288 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B4214855 : Blo 583288 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B2970107 : Blo 583288 2970107 := bstep (se 1 (by rfl) ⟨2227580, by rfl⟩ : syracuseStep 2970107 = 4455161) B4455161
theorem B2217071 : Blo 583288 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B2971079 : Blo 583288 2971079 := bstep (se 1 (by rfl) ⟨2228309, by rfl⟩ : syracuseStep 2971079 = 4456619) B4456619
theorem B4281947 : Blo 583288 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B128243357 : Blo 583288 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B11229151 : Blo 583288 11229151 := bstep (se 1 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 11229151 = 16843727) B16843727
theorem B12671477 : Blo 583288 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B875111 : Blo 583288 875111 := bstep (se 1 (by rfl) ⟨656333, by rfl⟩ : syracuseStep 875111 = 1312667) B1312667
theorem B20339495 : Blo 583288 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B2219471 : Blo 583288 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B876215 : Blo 583288 876215 := bstep (se 1 (by rfl) ⟨657161, by rfl⟩ : syracuseStep 876215 = 1314323) B1314323
theorem B876263 : Blo 583288 876263 := bstep (se 1 (by rfl) ⟨657197, by rfl⟩ : syracuseStep 876263 = 1314395) B1314395
theorem B51175709 : Blo 583288 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B876923 : Blo 583288 876923 := bstep (se 1 (by rfl) ⟨657692, by rfl⟩ : syracuseStep 876923 = 1315385) B1315385
theorem B876959 : Blo 583288 876959 := bstep (se 1 (by rfl) ⟨657719, by rfl⟩ : syracuseStep 876959 = 1315439) B1315439
theorem B1335935 : Blo 583288 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B4285223 : Blo 583288 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B877895 : Blo 583288 877895 := bstep (se 1 (by rfl) ⟨658421, by rfl⟩ : syracuseStep 877895 = 1316843) B1316843
theorem B878063 : Blo 583288 878063 := bstep (se 1 (by rfl) ⟨658547, by rfl⟩ : syracuseStep 878063 = 1317095) B1317095
theorem B878171 : Blo 583288 878171 := bstep (se 1 (by rfl) ⟨658628, by rfl⟩ : syracuseStep 878171 = 1317257) B1317257
theorem B583495 : Blo 583288 583495 := bstep (se 1 (by rfl) ⟨437621, by rfl⟩ : syracuseStep 583495 = 875243) B875243
theorem B6022991 : Blo 583288 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B583743 : Blo 583288 583743 := bstep (se 1 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 583743 = 875615) B875615
theorem B878663 : Blo 583288 878663 := bstep (se 1 (by rfl) ⟨658997, by rfl⟩ : syracuseStep 878663 = 1317995) B1317995
theorem B583791 : Blo 583288 583791 := bstep (se 1 (by rfl) ⟨437843, by rfl⟩ : syracuseStep 583791 = 875687) B875687
theorem B21326327 : Blo 583288 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B584383 : Blo 583288 584383 := bstep (se 1 (by rfl) ⟨438287, by rfl⟩ : syracuseStep 584383 = 876575) B876575
theorem B146402153 : Blo 583288 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B12053377 : Blo 583288 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B879497 : Blo 583288 879497 := bstep (se 2 (by rfl) ⟨329811, by rfl⟩ : syracuseStep 879497 = 659623) B659623
theorem B4451273 : Blo 583288 4451273 := bstep (se 2 (by rfl) ⟨1669227, by rfl⟩ : syracuseStep 4451273 = 3338455) B3338455
theorem B584731 : Blo 583288 584731 := bstep (se 1 (by rfl) ⟨438548, by rfl⟩ : syracuseStep 584731 = 877097) B877097
theorem B2812961 : Blo 583288 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B4451759 : Blo 583288 4451759 := bstep (se 1 (by rfl) ⟨3338819, by rfl⟩ : syracuseStep 4451759 = 6677639) B6677639
theorem B585583 : Blo 583288 585583 := bstep (se 1 (by rfl) ⟨439187, by rfl⟩ : syracuseStep 585583 = 878375) B878375
theorem B25325459 : Blo 583288 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B585631 : Blo 583288 585631 := bstep (se 1 (by rfl) ⟨439223, by rfl⟩ : syracuseStep 585631 = 878447) B878447
theorem B585799 : Blo 583288 585799 := bstep (se 1 (by rfl) ⟨439349, by rfl⟩ : syracuseStep 585799 = 878699) B878699
theorem B585839 : Blo 583288 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B1405097 : Blo 583288 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B3600839 : Blo 583288 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B586207 : Blo 583288 586207 := bstep (se 1 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 586207 = 879311) B879311
theorem B586395 : Blo 583288 586395 := bstep (se 1 (by rfl) ⟨439796, by rfl⟩ : syracuseStep 586395 = 879593) B879593
theorem B5010281 : Blo 583288 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B10843129 : Blo 583288 10843129 := bstep (se 2 (by rfl) ⟨4066173, by rfl⟩ : syracuseStep 10843129 = 8132347) B8132347
theorem B586751 : Blo 583288 586751 := bstep (se 1 (by rfl) ⟨440063, by rfl⟩ : syracuseStep 586751 = 880127) B880127
theorem B587111 : Blo 583288 587111 := bstep (se 1 (by rfl) ⟨440333, by rfl⟩ : syracuseStep 587111 = 880667) B880667
theorem B1111657 : Blo 583288 1111657 := bstep (se 2 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 1111657 = 833743) B833743
theorem B2227931 : Blo 583288 2227931 := bstep (se 1 (by rfl) ⟨1670948, by rfl⟩ : syracuseStep 2227931 = 3341897) B3341897
theorem B1802303 : Blo 583288 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B19464745 : Blo 583288 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1313567 : Blo 583288 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B1248367 : Blo 583288 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B986303 : Blo 583288 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B1313999 : Blo 583288 1313999 := bstep (se 1 (by rfl) ⟨985499, by rfl⟩ : syracuseStep 1313999 = 1970999) B1970999
theorem B1478047 : Blo 583288 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B4984415 : Blo 583288 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B2854631 : Blo 583288 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B986863 : Blo 583288 986863 := bstep (se 1 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 986863 = 1480295) B1480295
theorem B85495571 : Blo 583288 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B1314719 : Blo 583288 1314719 := bstep (se 1 (by rfl) ⟨986039, by rfl⟩ : syracuseStep 1314719 = 1972079) B1972079
theorem B987295 : Blo 583288 987295 := bstep (se 1 (by rfl) ⟨740471, by rfl⟩ : syracuseStep 987295 = 1480943) B1480943
theorem B1479647 : Blo 583288 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B1316105 : Blo 583288 1316105 := bstep (se 2 (by rfl) ⟨493539, by rfl⟩ : syracuseStep 1316105 = 987079) B987079
theorem B34117139 : Blo 583288 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B890623 : Blo 583288 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B2856815 : Blo 583288 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B3807323 : Blo 583288 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B7477595 : Blo 583288 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B3382393 : Blo 583288 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B3742847 : Blo 583288 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B1875307 : Blo 583288 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B1482209 : Blo 583288 1482209 := bstep (se 2 (by rfl) ⟨555828, by rfl⟩ : syracuseStep 1482209 = 1111657) B1111657
theorem B1973807 : Blo 583288 1973807 := bstep (se 1 (by rfl) ⟨1480355, by rfl⟩ : syracuseStep 1973807 = 2960711) B2960711
theorem B1318463 : Blo 583288 1318463 := bstep (se 1 (by rfl) ⟨988847, by rfl⟩ : syracuseStep 1318463 = 1977695) B1977695
theorem B2498273 : Blo 583288 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B1974185 : Blo 583288 1974185 := bstep (se 2 (by rfl) ⟨740319, by rfl⟩ : syracuseStep 1974185 = 1480639) B1480639
theorem B16883639 : Blo 583288 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B2400559 : Blo 583288 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B1975481 : Blo 583288 1975481 := bstep (se 2 (by rfl) ⟨740805, by rfl⟩ : syracuseStep 1975481 = 1481611) B1481611
theorem B4990187 : Blo 583288 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B1976075 : Blo 583288 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B2959415 : Blo 583288 2959415 := bstep (se 1 (by rfl) ⟨2219561, by rfl⟩ : syracuseStep 2959415 = 4439123) B4439123
theorem B1321127 : Blo 583288 1321127 := bstep (se 1 (by rfl) ⟨990845, by rfl⟩ : syracuseStep 1321127 = 1981691) B1981691
theorem B1485287 : Blo 583288 1485287 := bstep (se 1 (by rfl) ⟨1113965, by rfl⟩ : syracuseStep 1485287 = 2227931) B2227931
theorem B5483351 : Blo 583288 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B1977641 : Blo 583288 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B1978235 : Blo 583288 1978235 := bstep (se 1 (by rfl) ⟨1483676, by rfl⟩ : syracuseStep 1978235 = 2967353) B2967353
theorem B1880023 : Blo 583288 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B3322235 : Blo 583288 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B2372543 : Blo 583288 2372543 := bstep (se 1 (by rfl) ⟨1779407, by rfl⟩ : syracuseStep 2372543 = 3558815) B3558815
theorem B4010951 : Blo 583288 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B1980071 : Blo 583288 1980071 := bstep (se 1 (by rfl) ⟨1485053, by rfl⟩ : syracuseStep 1980071 = 2970107) B2970107
theorem B1980719 : Blo 583288 1980719 := bstep (se 1 (by rfl) ⟨1485539, by rfl⟩ : syracuseStep 1980719 = 2971079) B2971079
theorem B16071169 : Blo 583288 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B3554513 : Blo 583288 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B3325151 : Blo 583288 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B7126579 : Blo 583288 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B835867 : Blo 583288 835867 := bstep (se 1 (by rfl) ⟨626900, by rfl⟩ : syracuseStep 835867 = 1253801) B1253801
theorem B6668891 : Blo 583288 6668891 := bstep (se 1 (by rfl) ⟨5001668, by rfl⟩ : syracuseStep 6668891 = 10003337) B10003337
theorem B4015327 : Blo 583288 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B97601435 : Blo 583288 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B2967515 : Blo 583288 2967515 := bstep (se 1 (by rfl) ⟨2225636, by rfl⟩ : syracuseStep 2967515 = 4451273) B4451273
theorem B2967839 : Blo 583288 2967839 := bstep (se 1 (by rfl) ⟨2225879, by rfl⟩ : syracuseStep 2967839 = 4451759) B4451759
theorem B936731 : Blo 583288 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B2971241 : Blo 583288 2971241 := bstep (se 2 (by rfl) ⟨1114215, by rfl⟩ : syracuseStep 2971241 = 2228431) B2228431
theorem B1661255 : Blo 583288 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B874943 : Blo 583288 874943 := bstep (se 1 (by rfl) ⟨656207, by rfl⟩ : syracuseStep 874943 = 1312415) B1312415
theorem B6773183 : Blo 583288 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B875099 : Blo 583288 875099 := bstep (se 1 (by rfl) ⟨656324, by rfl⟩ : syracuseStep 875099 = 1312649) B1312649
theorem B875657 : Blo 583288 875657 := bstep (se 2 (by rfl) ⟨328371, by rfl⟩ : syracuseStep 875657 = 656743) B656743
theorem B875675 : Blo 583288 875675 := bstep (se 1 (by rfl) ⟨656756, by rfl⟩ : syracuseStep 875675 = 1313513) B1313513
theorem B876425 : Blo 583288 876425 := bstep (se 2 (by rfl) ⟨328659, by rfl⟩ : syracuseStep 876425 = 657319) B657319
theorem B2809903 : Blo 583288 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B877031 : Blo 583288 877031 := bstep (se 1 (by rfl) ⟨657773, by rfl⟩ : syracuseStep 877031 = 1315547) B1315547
theorem B877295 : Blo 583288 877295 := bstep (se 1 (by rfl) ⟨657971, by rfl⟩ : syracuseStep 877295 = 1315943) B1315943
theorem B877751 : Blo 583288 877751 := bstep (se 1 (by rfl) ⟨658313, by rfl⟩ : syracuseStep 877751 = 1316627) B1316627
theorem B877823 : Blo 583288 877823 := bstep (se 1 (by rfl) ⟨658367, by rfl⟩ : syracuseStep 877823 = 1316735) B1316735
theorem B8447651 : Blo 583288 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B583407 : Blo 583288 583407 := bstep (se 1 (by rfl) ⟨437555, by rfl⟩ : syracuseStep 583407 = 875111) B875111
theorem B13559663 : Blo 583288 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B584143 : Blo 583288 584143 := bstep (se 1 (by rfl) ⟨438107, by rfl⟩ : syracuseStep 584143 = 876215) B876215
theorem B584175 : Blo 583288 584175 := bstep (se 1 (by rfl) ⟨438131, by rfl⟩ : syracuseStep 584175 = 876263) B876263
theorem B6777431 : Blo 583288 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B57830021 : Blo 583288 57830021 := bstep (se 4 (by rfl) ⟨5421564, by rfl⟩ : syracuseStep 57830021 = 10843129) B10843129
theorem B584615 : Blo 583288 584615 := bstep (se 1 (by rfl) ⟨438461, by rfl⟩ : syracuseStep 584615 = 876923) B876923
theorem B584639 : Blo 583288 584639 := bstep (se 1 (by rfl) ⟨438479, by rfl⟩ : syracuseStep 584639 = 876959) B876959
theorem B879599 : Blo 583288 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B879647 : Blo 583288 879647 := bstep (se 1 (by rfl) ⟨659735, by rfl⟩ : syracuseStep 879647 = 1319471) B1319471
theorem B879899 : Blo 583288 879899 := bstep (se 1 (by rfl) ⟨659924, by rfl⟩ : syracuseStep 879899 = 1319849) B1319849
theorem B5336441 : Blo 583288 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B880079 : Blo 583288 880079 := bstep (se 1 (by rfl) ⟨660059, by rfl⟩ : syracuseStep 880079 = 1320119) B1320119
theorem B585263 : Blo 583288 585263 := bstep (se 1 (by rfl) ⟨438947, by rfl⟩ : syracuseStep 585263 = 877895) B877895
theorem B585375 : Blo 583288 585375 := bstep (se 1 (by rfl) ⟨439031, by rfl⟩ : syracuseStep 585375 = 878063) B878063
theorem B585447 : Blo 583288 585447 := bstep (se 1 (by rfl) ⟨439085, by rfl⟩ : syracuseStep 585447 = 878171) B878171
theorem B880463 : Blo 583288 880463 := bstep (se 1 (by rfl) ⟨660347, by rfl⟩ : syracuseStep 880463 = 1320695) B1320695
theorem B880553 : Blo 583288 880553 := bstep (se 2 (by rfl) ⟨330207, by rfl⟩ : syracuseStep 880553 = 660415) B660415
theorem B585775 : Blo 583288 585775 := bstep (se 1 (by rfl) ⟨439331, by rfl⟩ : syracuseStep 585775 = 878663) B878663
theorem B880703 : Blo 583288 880703 := bstep (se 1 (by rfl) ⟨660527, by rfl⟩ : syracuseStep 880703 = 1321055) B1321055
theorem B14217551 : Blo 583288 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B586331 : Blo 583288 586331 := bstep (se 1 (by rfl) ⟨439748, by rfl⟩ : syracuseStep 586331 = 879497) B879497
theorem B7500863 : Blo 583288 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B14972201 : Blo 583288 14972201 := bstep (se 2 (by rfl) ⟨5614575, by rfl⟩ : syracuseStep 14972201 = 11229151) B11229151
theorem B751135 : Blo 583288 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B3340187 : Blo 583288 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B1114489 : Blo 583288 1114489 := bstep (se 2 (by rfl) ⟨417933, by rfl⟩ : syracuseStep 1114489 = 835867) B835867
theorem B25952993 : Blo 583288 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B657535 : Blo 583288 657535 := bstep (se 1 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 657535 = 986303) B986303
theorem B1903087 : Blo 583288 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B986431 : Blo 583288 986431 := bstep (se 1 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 986431 = 1479647) B1479647
theorem B22744759 : Blo 583288 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B1904543 : Blo 583288 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B4985063 : Blo 583288 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B1970729 : Blo 583288 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B2495231 : Blo 583288 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B1315817 : Blo 583288 1315817 := bstep (se 2 (by rfl) ⟨493431, by rfl⟩ : syracuseStep 1315817 = 986863) B986863
theorem B988139 : Blo 583288 988139 := bstep (se 1 (by rfl) ⟨741104, by rfl⟩ : syracuseStep 988139 = 1482209) B1482209
theorem B1315871 : Blo 583288 1315871 := bstep (se 1 (by rfl) ⟨986903, by rfl⟩ : syracuseStep 1315871 = 1973807) B1973807
theorem B1316123 : Blo 583288 1316123 := bstep (se 1 (by rfl) ⟨987092, by rfl⟩ : syracuseStep 1316123 = 1974185) B1974185
theorem B1316393 : Blo 583288 1316393 := bstep (se 2 (by rfl) ⟨493647, by rfl⟩ : syracuseStep 1316393 = 987295) B987295
theorem B1316987 : Blo 583288 1316987 := bstep (se 1 (by rfl) ⟨987740, by rfl⟩ : syracuseStep 1316987 = 1975481) B1975481
theorem B1317383 : Blo 583288 1317383 := bstep (se 1 (by rfl) ⟨988037, by rfl⟩ : syracuseStep 1317383 = 1976075) B1976075
theorem B1972943 : Blo 583288 1972943 := bstep (se 1 (by rfl) ⟨1479707, by rfl⟩ : syracuseStep 1972943 = 2959415) B2959415
theorem B990191 : Blo 583288 990191 := bstep (se 1 (by rfl) ⟨742643, by rfl⟩ : syracuseStep 990191 = 1485287) B1485287
theorem B2497949 : Blo 583288 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B1318427 : Blo 583288 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B1187497 : Blo 583288 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B1318823 : Blo 583288 1318823 := bstep (se 1 (by rfl) ⟨989117, by rfl⟩ : syracuseStep 1318823 = 1978235) B1978235
theorem B9478367 : Blo 583288 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B1581695 : Blo 583288 1581695 := bstep (se 1 (by rfl) ⟨1186271, by rfl⟩ : syracuseStep 1581695 = 2372543) B2372543
theorem B1320047 : Blo 583288 1320047 := bstep (se 1 (by rfl) ⟨990035, by rfl⟩ : syracuseStep 1320047 = 1980071) B1980071
theorem B1320479 : Blo 583288 1320479 := bstep (se 1 (by rfl) ⟨990359, by rfl⟩ : syracuseStep 1320479 = 1980719) B1980719
theorem B2500409 : Blo 583288 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B2369675 : Blo 583288 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B3746537 : Blo 583288 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B1978343 : Blo 583288 1978343 := bstep (se 1 (by rfl) ⟨1483757, by rfl⟩ : syracuseStep 1978343 = 2967515) B2967515
theorem B1978559 : Blo 583288 1978559 := bstep (se 1 (by rfl) ⟨1483919, by rfl⟩ : syracuseStep 1978559 = 2967839) B2967839
theorem B5353769 : Blo 583288 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B3322943 : Blo 583288 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B56997047 : Blo 583288 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B1980827 : Blo 583288 1980827 := bstep (se 1 (by rfl) ⟨1485620, by rfl⟩ : syracuseStep 1980827 = 2971241) B2971241
theorem B2538215 : Blo 583288 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B2506697 : Blo 583288 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B11255759 : Blo 583288 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B3326791 : Blo 583288 3326791 := bstep (se 1 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 3326791 = 4990187) B4990187
theorem B38553347 : Blo 583288 38553347 := bstep (se 1 (by rfl) ⟨28915010, by rfl⟩ : syracuseStep 38553347 = 57830021) B57830021
theorem B3655567 : Blo 583288 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B1001513 : Blo 583288 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B3557627 : Blo 583288 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B2214823 : Blo 583288 2214823 := bstep (se 1 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 2214823 = 3322235) B3322235
theorem B2673967 : Blo 583288 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B5000575 : Blo 583288 5000575 := bstep (se 1 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 5000575 = 7500863) B7500863
theorem B9981467 : Blo 583288 9981467 := bstep (se 1 (by rfl) ⟨7486100, by rfl⟩ : syracuseStep 9981467 = 14972201) B14972201
theorem B4509857 : Blo 583288 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B2216767 : Blo 583288 2216767 := bstep (se 1 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 2216767 = 3325151) B3325151
theorem B1201535 : Blo 583288 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B4445927 : Blo 583288 4445927 := bstep (se 1 (by rfl) ⟨3334445, by rfl⟩ : syracuseStep 4445927 = 6668891) B6668891
theorem B65067623 : Blo 583288 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B12802981 : Blo 583288 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B875711 : Blo 583288 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B875999 : Blo 583288 875999 := bstep (se 1 (by rfl) ⟨656999, by rfl⟩ : syracuseStep 875999 = 1313999) B1313999
theorem B876479 : Blo 583288 876479 := bstep (se 1 (by rfl) ⟨657359, by rfl⟩ : syracuseStep 876479 = 1314719) B1314719
theorem B877403 : Blo 583288 877403 := bstep (se 1 (by rfl) ⟨658052, by rfl⟩ : syracuseStep 877403 = 1316105) B1316105
theorem B1664489 : Blo 583288 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B1107503 : Blo 583288 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B583295 : Blo 583288 583295 := bstep (se 1 (by rfl) ⟨437471, by rfl⟩ : syracuseStep 583295 = 874943) B874943
theorem B4515455 : Blo 583288 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B583399 : Blo 583288 583399 := bstep (se 1 (by rfl) ⟨437549, by rfl⟩ : syracuseStep 583399 = 875099) B875099
theorem B583771 : Blo 583288 583771 := bstep (se 1 (by rfl) ⟨437828, by rfl⟩ : syracuseStep 583771 = 875657) B875657
theorem B583783 : Blo 583288 583783 := bstep (se 1 (by rfl) ⟨437837, by rfl⟩ : syracuseStep 583783 = 875675) B875675
theorem B878975 : Blo 583288 878975 := bstep (se 1 (by rfl) ⟨659231, by rfl⟩ : syracuseStep 878975 = 1318463) B1318463
theorem B1665515 : Blo 583288 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B584283 : Blo 583288 584283 := bstep (se 1 (by rfl) ⟨438212, by rfl⟩ : syracuseStep 584283 = 876425) B876425
theorem B584687 : Blo 583288 584687 := bstep (se 1 (by rfl) ⟨438515, by rfl⟩ : syracuseStep 584687 = 877031) B877031
theorem B584863 : Blo 583288 584863 := bstep (se 1 (by rfl) ⟨438647, by rfl⟩ : syracuseStep 584863 = 877295) B877295
theorem B585167 : Blo 583288 585167 := bstep (se 1 (by rfl) ⟨438875, by rfl⟩ : syracuseStep 585167 = 877751) B877751
theorem B585215 : Blo 583288 585215 := bstep (se 1 (by rfl) ⟨438911, by rfl⟩ : syracuseStep 585215 = 877823) B877823
theorem B5631767 : Blo 583288 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B9039775 : Blo 583288 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B880751 : Blo 583288 880751 := bstep (se 1 (by rfl) ⟨660563, by rfl⟩ : syracuseStep 880751 = 1321127) B1321127
theorem B4518287 : Blo 583288 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B586399 : Blo 583288 586399 := bstep (se 1 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 586399 = 879599) B879599
theorem B586431 : Blo 583288 586431 := bstep (se 1 (by rfl) ⟨439823, by rfl⟩ : syracuseStep 586431 = 879647) B879647
theorem B586599 : Blo 583288 586599 := bstep (se 1 (by rfl) ⟨439949, by rfl⟩ : syracuseStep 586599 = 879899) B879899
theorem B586719 : Blo 583288 586719 := bstep (se 1 (by rfl) ⟨440039, by rfl⟩ : syracuseStep 586719 = 880079) B880079
theorem B586975 : Blo 583288 586975 := bstep (se 1 (by rfl) ⟨440231, by rfl⟩ : syracuseStep 586975 = 880463) B880463
theorem B587035 : Blo 583288 587035 := bstep (se 1 (by rfl) ⟨440276, by rfl⟩ : syracuseStep 587035 = 880553) B880553
theorem B587135 : Blo 583288 587135 := bstep (se 1 (by rfl) ⟨440351, by rfl⟩ : syracuseStep 587135 = 880703) B880703
theorem B21428225 : Blo 583288 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B2226791 : Blo 583288 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B9502105 : Blo 583288 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B17301995 : Blo 583288 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B6654311 : Blo 583288 6654311 := bstep (se 1 (by rfl) ⟨4990733, by rfl⟩ : syracuseStep 6654311 = 9981467) B9981467
theorem B1313819 : Blo 583288 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B658759 : Blo 583288 658759 := bstep (se 1 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 658759 = 988139) B988139
theorem B2953097 : Blo 583288 2953097 := bstep (se 2 (by rfl) ⟨1107411, by rfl⟩ : syracuseStep 2953097 = 2214823) B2214823
theorem B12816373 : Blo 583288 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B1315241 : Blo 583288 1315241 := bstep (se 2 (by rfl) ⟨493215, by rfl⟩ : syracuseStep 1315241 = 986431) B986431
theorem B1315295 : Blo 583288 1315295 := bstep (se 1 (by rfl) ⟨986471, by rfl⟩ : syracuseStep 1315295 = 1972943) B1972943
theorem B660127 : Blo 583288 660127 := bstep (se 1 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 660127 = 990191) B990191
theorem B1054463 : Blo 583288 1054463 := bstep (se 1 (by rfl) ⟨790847, by rfl⟩ : syracuseStep 1054463 = 1581695) B1581695
theorem B2955689 : Blo 583288 2955689 := bstep (se 2 (by rfl) ⟨1108383, by rfl⟩ : syracuseStep 2955689 = 2216767) B2216767
theorem B2497691 : Blo 583288 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B1318895 : Blo 583288 1318895 := bstep (se 1 (by rfl) ⟨989171, by rfl⟩ : syracuseStep 1318895 = 1978343) B1978343
theorem B1319039 : Blo 583288 1319039 := bstep (se 1 (by rfl) ⟨989279, by rfl⟩ : syracuseStep 1319039 = 1978559) B1978559
theorem B1320551 : Blo 583288 1320551 := bstep (se 1 (by rfl) ⟨990413, by rfl⟩ : syracuseStep 1320551 = 1980827) B1980827
theorem B1484527 : Blo 583288 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B1583329 : Blo 583288 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B1485985 : Blo 583288 1485985 := bstep (se 2 (by rfl) ⟨557244, by rfl⟩ : syracuseStep 1485985 = 1114489) B1114489
theorem B4435721 : Blo 583288 4435721 := bstep (se 2 (by rfl) ⟨1663395, by rfl⟩ : syracuseStep 4435721 = 3326791) B3326791
theorem B667675 : Blo 583288 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B2371751 : Blo 583288 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B3323375 : Blo 583288 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B2963951 : Blo 583288 2963951 := bstep (se 1 (by rfl) ⟨2222963, by rfl⟩ : syracuseStep 2963951 = 4445927) B4445927
theorem B4438637 : Blo 583288 4438637 := bstep (se 3 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 4438637 = 1664489) B1664489
theorem B6667433 : Blo 583288 6667433 := bstep (se 2 (by rfl) ⟨2500287, by rfl⟩ : syracuseStep 6667433 = 5000575) B5000575
theorem B102808925 : Blo 583288 102808925 := bstep (se 3 (by rfl) ⟨19276673, by rfl⟩ : syracuseStep 102808925 = 38553347) B38553347
theorem B30326345 : Blo 583288 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B738335 : Blo 583288 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B3754511 : Blo 583288 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B2215295 : Blo 583288 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B37998031 : Blo 583288 37998031 := bstep (se 1 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 37998031 = 56997047) B56997047
theorem B1692143 : Blo 583288 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B12669473 : Blo 583288 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B4874089 : Blo 583288 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B10149797 : Blo 583288 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B1269695 : Blo 583288 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B3006571 : Blo 583288 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B876713 : Blo 583288 876713 := bstep (se 2 (by rfl) ⟨328767, by rfl⟩ : syracuseStep 876713 = 657535) B657535
theorem B1663487 : Blo 583288 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B877211 : Blo 583288 877211 := bstep (se 1 (by rfl) ⟨657908, by rfl⟩ : syracuseStep 877211 = 1315817) B1315817
theorem B877247 : Blo 583288 877247 := bstep (se 1 (by rfl) ⟨657935, by rfl⟩ : syracuseStep 877247 = 1315871) B1315871
theorem B877415 : Blo 583288 877415 := bstep (se 1 (by rfl) ⟨658061, by rfl⟩ : syracuseStep 877415 = 1316123) B1316123
theorem B877595 : Blo 583288 877595 := bstep (se 1 (by rfl) ⟨658196, by rfl⟩ : syracuseStep 877595 = 1316393) B1316393
theorem B877991 : Blo 583288 877991 := bstep (se 1 (by rfl) ⟨658493, by rfl⟩ : syracuseStep 877991 = 1316987) B1316987
theorem B878255 : Blo 583288 878255 := bstep (se 1 (by rfl) ⟨658691, by rfl⟩ : syracuseStep 878255 = 1317383) B1317383
theorem B3565289 : Blo 583288 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B43378415 : Blo 583288 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B583807 : Blo 583288 583807 := bstep (se 1 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 583807 = 875711) B875711
theorem B1665299 : Blo 583288 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B583999 : Blo 583288 583999 := bstep (se 1 (by rfl) ⟨437999, by rfl⟩ : syracuseStep 583999 = 875999) B875999
theorem B878951 : Blo 583288 878951 := bstep (se 1 (by rfl) ⟨659213, by rfl⟩ : syracuseStep 878951 = 1318427) B1318427
theorem B12053033 : Blo 583288 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B879215 : Blo 583288 879215 := bstep (se 1 (by rfl) ⟨659411, by rfl⟩ : syracuseStep 879215 = 1318823) B1318823
theorem B584319 : Blo 583288 584319 := bstep (se 1 (by rfl) ⟨438239, by rfl⟩ : syracuseStep 584319 = 876479) B876479
theorem B6318911 : Blo 583288 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B6319133 : Blo 583288 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B584935 : Blo 583288 584935 := bstep (se 1 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 584935 = 877403) B877403
theorem B880031 : Blo 583288 880031 := bstep (se 1 (by rfl) ⟨660023, by rfl⟩ : syracuseStep 880031 = 1320047) B1320047
theorem B880319 : Blo 583288 880319 := bstep (se 1 (by rfl) ⟨660239, by rfl⟩ : syracuseStep 880319 = 1320479) B1320479
theorem B3010303 : Blo 583288 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B1666939 : Blo 583288 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B585983 : Blo 583288 585983 := bstep (se 1 (by rfl) ⟨439487, by rfl⟩ : syracuseStep 585983 = 878975) B878975
theorem B1110343 : Blo 583288 1110343 := bstep (se 1 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 1110343 = 1665515) B1665515
theorem B587167 : Blo 583288 587167 := bstep (se 1 (by rfl) ⟨440375, by rfl⟩ : syracuseStep 587167 = 880751) B880751
theorem B3569179 : Blo 583288 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B3012191 : Blo 583288 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B17070641 : Blo 583288 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B14285483 : Blo 583288 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B1671131 : Blo 583288 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B7503839 : Blo 583288 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B11534663 : Blo 583288 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B1476863 : Blo 583288 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B1968731 : Blo 583288 1968731 := bstep (se 1 (by rfl) ⟨1476548, by rfl⟩ : syracuseStep 1968731 = 2953097) B2953097
theorem B1968893 : Blo 583288 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B1970459 : Blo 583288 1970459 := bstep (se 1 (by rfl) ⟨1477844, by rfl⟩ : syracuseStep 1970459 = 2955689) B2955689
theorem B50664041 : Blo 583288 50664041 := bstep (se 2 (by rfl) ⟨18999015, by rfl⟩ : syracuseStep 50664041 = 37998031) B37998031
theorem B890233 : Blo 583288 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B1480457 : Blo 583288 1480457 := bstep (se 2 (by rfl) ⟨555171, by rfl⟩ : syracuseStep 1480457 = 1110343) B1110343
theorem B8035355 : Blo 583288 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B4758905 : Blo 583288 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B2957147 : Blo 583288 2957147 := bstep (se 1 (by rfl) ⟨2217860, by rfl⟩ : syracuseStep 2957147 = 4435721) B4435721
theorem B11247605 : Blo 583288 11247605 := bstep (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) B1054463
theorem B1581167 : Blo 583288 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B1975967 : Blo 583288 1975967 := bstep (se 1 (by rfl) ⟨1481975, by rfl⟩ : syracuseStep 1975967 = 2963951) B2963951
theorem B11380427 : Blo 583288 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B2959091 : Blo 583288 2959091 := bstep (se 1 (by rfl) ⟨2219318, by rfl⟩ : syracuseStep 2959091 = 4438637) B4438637
theorem B6498785 : Blo 583288 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B4008761 : Blo 583288 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B4436207 : Blo 583288 4436207 := bstep (se 1 (by rfl) ⟨3327155, by rfl⟩ : syracuseStep 4436207 = 6654311) B6654311
theorem B2503007 : Blo 583288 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B1979369 : Blo 583288 1979369 := bstep (se 2 (by rfl) ⟨742263, by rfl⟩ : syracuseStep 1979369 = 1484527) B1484527
theorem B2111105 : Blo 583288 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1128095 : Blo 583288 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1981313 : Blo 583288 1981313 := bstep (se 2 (by rfl) ⟨742992, by rfl⟩ : syracuseStep 1981313 = 1485985) B1485985
theorem B17088497 : Blo 583288 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B32130037 : Blo 583288 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B2376859 : Blo 583288 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B28918943 : Blo 583288 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B4212607 : Blo 583288 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B4212755 : Blo 583288 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B2215583 : Blo 583288 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B9523655 : Blo 583288 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B4444955 : Blo 583288 4444955 := bstep (se 1 (by rfl) ⟨3333716, by rfl⟩ : syracuseStep 4444955 = 6667433) B6667433
theorem B68539283 : Blo 583288 68539283 := bstep (se 1 (by rfl) ⟨51404462, by rfl⟩ : syracuseStep 68539283 = 102808925) B102808925
theorem B5002559 : Blo 583288 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B875879 : Blo 583288 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B876827 : Blo 583288 876827 := bstep (se 1 (by rfl) ⟨657620, by rfl⟩ : syracuseStep 876827 = 1315241) B1315241
theorem B876863 : Blo 583288 876863 := bstep (se 1 (by rfl) ⟨657647, by rfl⟩ : syracuseStep 876863 = 1315295) B1315295
theorem B8446315 : Blo 583288 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B878345 : Blo 583288 878345 := bstep (se 2 (by rfl) ⟨329379, by rfl⟩ : syracuseStep 878345 = 658759) B658759
theorem B1665127 : Blo 583288 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B2222585 : Blo 583288 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B846463 : Blo 583288 846463 := bstep (se 1 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 846463 = 1269695) B1269695
theorem B879263 : Blo 583288 879263 := bstep (se 1 (by rfl) ⟨659447, by rfl⟩ : syracuseStep 879263 = 1318895) B1318895
theorem B879359 : Blo 583288 879359 := bstep (se 1 (by rfl) ⟨659519, by rfl⟩ : syracuseStep 879359 = 1319039) B1319039
theorem B584475 : Blo 583288 584475 := bstep (se 1 (by rfl) ⟨438356, by rfl⟩ : syracuseStep 584475 = 876713) B876713
theorem B1108991 : Blo 583288 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B584807 : Blo 583288 584807 := bstep (se 1 (by rfl) ⟨438605, by rfl⟩ : syracuseStep 584807 = 877211) B877211
theorem B584831 : Blo 583288 584831 := bstep (se 1 (by rfl) ⟨438623, by rfl⟩ : syracuseStep 584831 = 877247) B877247
theorem B584943 : Blo 583288 584943 := bstep (se 1 (by rfl) ⟨438707, by rfl⟩ : syracuseStep 584943 = 877415) B877415
theorem B585063 : Blo 583288 585063 := bstep (se 1 (by rfl) ⟨438797, by rfl⟩ : syracuseStep 585063 = 877595) B877595
theorem B880169 : Blo 583288 880169 := bstep (se 2 (by rfl) ⟨330063, by rfl⟩ : syracuseStep 880169 = 660127) B660127
theorem B585327 : Blo 583288 585327 := bstep (se 1 (by rfl) ⟨438995, by rfl⟩ : syracuseStep 585327 = 877991) B877991
theorem B880367 : Blo 583288 880367 := bstep (se 1 (by rfl) ⟨660275, by rfl⟩ : syracuseStep 880367 = 1320551) B1320551
theorem B585503 : Blo 583288 585503 := bstep (se 1 (by rfl) ⟨439127, by rfl⟩ : syracuseStep 585503 = 878255) B878255
theorem B1110199 : Blo 583288 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B585967 : Blo 583288 585967 := bstep (se 1 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 585967 = 878951) B878951
theorem B586143 : Blo 583288 586143 := bstep (se 1 (by rfl) ⟨439607, by rfl⟩ : syracuseStep 586143 = 879215) B879215
theorem B586687 : Blo 583288 586687 := bstep (se 1 (by rfl) ⟨440015, by rfl⟩ : syracuseStep 586687 = 880031) B880031
theorem B586879 : Blo 583288 586879 := bstep (se 1 (by rfl) ⟨440159, by rfl⟩ : syracuseStep 586879 = 880319) B880319
theorem B16054949 : Blo 583288 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B20217563 : Blo 583288 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B27066125 : Blo 583288 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B1114087 : Blo 583288 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B984575 : Blo 583288 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B1312487 : Blo 583288 1312487 := bstep (se 1 (by rfl) ⟨984365, by rfl⟩ : syracuseStep 1312487 = 1968731) B1968731
theorem B1312595 : Blo 583288 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1477055 : Blo 583288 1477055 := bstep (se 1 (by rfl) ⟨1107791, by rfl⟩ : syracuseStep 1477055 = 2215583) B2215583
theorem B1313639 : Blo 583288 1313639 := bstep (se 1 (by rfl) ⟨985229, by rfl⟩ : syracuseStep 1313639 = 1970459) B1970459
theorem B986971 : Blo 583288 986971 := bstep (se 1 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 986971 = 1480457) B1480457
theorem B1971431 : Blo 583288 1971431 := bstep (se 1 (by rfl) ⟨1478573, by rfl⟩ : syracuseStep 1971431 = 2957147) B2957147
theorem B1480265 : Blo 583288 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B1317311 : Blo 583288 1317311 := bstep (se 1 (by rfl) ⟨987983, by rfl⟩ : syracuseStep 1317311 = 1975967) B1975967
theorem B1972727 : Blo 583288 1972727 := bstep (se 1 (by rfl) ⟨1479545, by rfl⟩ : syracuseStep 1972727 = 2959091) B2959091
theorem B4332523 : Blo 583288 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B1481723 : Blo 583288 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B2957309 : Blo 583288 2957309 := bstep (se 3 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 2957309 = 1108991) B1108991
theorem B2957471 : Blo 583288 2957471 := bstep (se 1 (by rfl) ⟨2218103, by rfl⟩ : syracuseStep 2957471 = 4436207) B4436207
theorem B1319579 : Blo 583288 1319579 := bstep (se 1 (by rfl) ⟨989684, by rfl⟩ : syracuseStep 1319579 = 1979369) B1979369
theorem B1320875 : Blo 583288 1320875 := bstep (se 1 (by rfl) ⟨990656, by rfl⟩ : syracuseStep 1320875 = 1981313) B1981313
theorem B13478375 : Blo 583288 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B1485449 : Blo 583288 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B19279295 : Blo 583288 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B42840049 : Blo 583288 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B5616809 : Blo 583288 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B2963303 : Blo 583288 2963303 := bstep (se 1 (by rfl) ⟨2222477, by rfl⟩ : syracuseStep 2963303 = 4444955) B4444955
theorem B45692855 : Blo 583288 45692855 := bstep (se 1 (by rfl) ⟨34269641, by rfl⟩ : syracuseStep 45692855 = 68539283) B68539283
theorem B1128617 : Blo 583288 1128617 := bstep (se 2 (by rfl) ⟨423231, by rfl⟩ : syracuseStep 1128617 = 846463) B846463
theorem B5356903 : Blo 583288 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B7586951 : Blo 583288 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B2672507 : Blo 583288 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B10703299 : Blo 583288 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B18044083 : Blo 583288 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B11392331 : Blo 583288 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B7689775 : Blo 583288 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B4216445 : Blo 583288 4216445 := bstep (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) B1581167
theorem B11261753 : Blo 583288 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B2808503 : Blo 583288 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B3169145 : Blo 583288 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B2220169 : Blo 583288 2220169 := bstep (se 2 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 2220169 = 1665127) B1665127
theorem B6349103 : Blo 583288 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B33776027 : Blo 583288 33776027 := bstep (se 1 (by rfl) ⟨25332020, by rfl⟩ : syracuseStep 33776027 = 50664041) B50664041
theorem B3335039 : Blo 583288 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B583919 : Blo 583288 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B3172603 : Blo 583288 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B7498403 : Blo 583288 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B584551 : Blo 583288 584551 := bstep (se 1 (by rfl) ⟨438413, by rfl⟩ : syracuseStep 584551 = 876827) B876827
theorem B584575 : Blo 583288 584575 := bstep (se 1 (by rfl) ⟨438431, by rfl⟩ : syracuseStep 584575 = 876863) B876863
theorem B585563 : Blo 583288 585563 := bstep (se 1 (by rfl) ⟨439172, by rfl⟩ : syracuseStep 585563 = 878345) B878345
theorem B586175 : Blo 583288 586175 := bstep (se 1 (by rfl) ⟨439631, by rfl⟩ : syracuseStep 586175 = 879263) B879263
theorem B586239 : Blo 583288 586239 := bstep (se 1 (by rfl) ⟨439679, by rfl⟩ : syracuseStep 586239 = 879359) B879359
theorem B4747909 : Blo 583288 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B586779 : Blo 583288 586779 := bstep (se 1 (by rfl) ⟨440084, by rfl⟩ : syracuseStep 586779 = 880169) B880169
theorem B586911 : Blo 583288 586911 := bstep (se 1 (by rfl) ⟨440183, by rfl⟩ : syracuseStep 586911 = 880367) B880367
theorem B1668671 : Blo 583288 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B1407403 : Blo 583288 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B752063 : Blo 583288 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B656383 : Blo 583288 656383 := bstep (se 1 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 656383 = 984575) B984575
theorem B984703 : Blo 583288 984703 := bstep (se 1 (by rfl) ⟨738527, by rfl⟩ : syracuseStep 984703 = 1477055) B1477055
theorem B4230137 : Blo 583288 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B1314287 : Blo 583288 1314287 := bstep (se 1 (by rfl) ⟨985715, by rfl⟩ : syracuseStep 1314287 = 1971431) B1971431
theorem B30379549 : Blo 583288 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B986843 : Blo 583288 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B7507835 : Blo 583288 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B1315151 : Blo 583288 1315151 := bstep (se 1 (by rfl) ⟨986363, by rfl⟩ : syracuseStep 1315151 = 1972727) B1972727
theorem B1872335 : Blo 583288 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B987815 : Blo 583288 987815 := bstep (se 1 (by rfl) ⟨740861, by rfl⟩ : syracuseStep 987815 = 1481723) B1481723
theorem B1315961 : Blo 583288 1315961 := bstep (se 2 (by rfl) ⟨493485, by rfl⟩ : syracuseStep 1315961 = 986971) B986971
theorem B57120065 : Blo 583288 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B1971539 : Blo 583288 1971539 := bstep (se 1 (by rfl) ⟨1478654, by rfl⟩ : syracuseStep 1971539 = 2957309) B2957309
theorem B1971647 : Blo 583288 1971647 := bstep (se 1 (by rfl) ⟨1478735, by rfl⟩ : syracuseStep 1971647 = 2957471) B2957471
theorem B4232735 : Blo 583288 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B22517351 : Blo 583288 22517351 := bstep (se 1 (by rfl) ⟨16888013, by rfl⟩ : syracuseStep 22517351 = 33776027) B33776027
theorem B6330545 : Blo 583288 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B2005501 : Blo 583288 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B24058777 : Blo 583288 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B8985583 : Blo 583288 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B990299 : Blo 583288 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B12852863 : Blo 583288 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B1876537 : Blo 583288 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B3744539 : Blo 583288 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B1975535 : Blo 583288 1975535 := bstep (se 1 (by rfl) ⟨1481651, by rfl⟩ : syracuseStep 1975535 = 2963303) B2963303
theorem B5776697 : Blo 583288 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B2960225 : Blo 583288 2960225 := bstep (se 2 (by rfl) ⟨1110084, by rfl⟩ : syracuseStep 2960225 = 2220169) B2220169
theorem B1781671 : Blo 583288 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B12038581 : Blo 583288 12038581 := bstep (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) B1128617
theorem B20231869 : Blo 583288 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B2112763 : Blo 583288 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B14271065 : Blo 583288 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B4998935 : Blo 583288 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B30461903 : Blo 583288 30461903 := bstep (se 1 (by rfl) ⟨22846427, by rfl⟩ : syracuseStep 30461903 = 45692855) B45692855
theorem B874991 : Blo 583288 874991 := bstep (se 1 (by rfl) ⟨656243, by rfl⟩ : syracuseStep 874991 = 1312487) B1312487
theorem B875063 : Blo 583288 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B875759 : Blo 583288 875759 := bstep (se 1 (by rfl) ⟨656819, by rfl⟩ : syracuseStep 875759 = 1313639) B1313639
theorem B2810963 : Blo 583288 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B878207 : Blo 583288 878207 := bstep (se 1 (by rfl) ⟨658655, by rfl⟩ : syracuseStep 878207 = 1317311) B1317311
theorem B879719 : Blo 583288 879719 := bstep (se 1 (by rfl) ⟨659789, by rfl⟩ : syracuseStep 879719 = 1319579) B1319579
theorem B2223359 : Blo 583288 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B880583 : Blo 583288 880583 := bstep (se 1 (by rfl) ⟨660437, by rfl⟩ : syracuseStep 880583 = 1320875) B1320875
theorem B10253033 : Blo 583288 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1112447 : Blo 583288 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B7142537 : Blo 583288 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B2820091 : Blo 583288 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B1312937 : Blo 583288 1312937 := bstep (se 2 (by rfl) ⟨492351, by rfl⟩ : syracuseStep 1312937 = 984703) B984703
theorem B657895 : Blo 583288 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B1248223 : Blo 583288 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B658543 : Blo 583288 658543 := bstep (se 1 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 658543 = 987815) B987815
theorem B15404525 : Blo 583288 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B38080043 : Blo 583288 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B1314359 : Blo 583288 1314359 := bstep (se 1 (by rfl) ⟨985769, by rfl⟩ : syracuseStep 1314359 = 1971539) B1971539
theorem B1314431 : Blo 583288 1314431 := bstep (se 1 (by rfl) ⟨985823, by rfl⟩ : syracuseStep 1314431 = 1971647) B1971647
theorem B2821823 : Blo 583288 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B15011567 : Blo 583288 15011567 := bstep (se 1 (by rfl) ⟨11258675, by rfl⟩ : syracuseStep 15011567 = 22517351) B22517351
theorem B40506065 : Blo 583288 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B660199 : Blo 583288 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B2496359 : Blo 583288 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B1873975 : Blo 583288 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B1317023 : Blo 583288 1317023 := bstep (se 1 (by rfl) ⟨987767, by rfl⟩ : syracuseStep 1317023 = 1975535) B1975535
theorem B1973483 : Blo 583288 1973483 := bstep (se 1 (by rfl) ⟨1480112, by rfl⟩ : syracuseStep 1973483 = 2960225) B2960225
theorem B1482239 : Blo 583288 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B26975825 : Blo 583288 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B19046765 : Blo 583288 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B9514043 : Blo 583288 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B2502049 : Blo 583288 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B8568575 : Blo 583288 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B2375561 : Blo 583288 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B47923109 : Blo 583288 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B6835355 : Blo 583288 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B2674001 : Blo 583288 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B741631 : Blo 583288 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B3332623 : Blo 583288 3332623 := bstep (se 1 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 3332623 = 4998935) B4998935
theorem B875177 : Blo 583288 875177 := bstep (se 2 (by rfl) ⟨328191, by rfl⟩ : syracuseStep 875177 = 656383) B656383
theorem B876191 : Blo 583288 876191 := bstep (se 1 (by rfl) ⟨657143, by rfl⟩ : syracuseStep 876191 = 1314287) B1314287
theorem B5005223 : Blo 583288 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B20307935 : Blo 583288 20307935 := bstep (se 1 (by rfl) ⟨15230951, by rfl⟩ : syracuseStep 20307935 = 30461903) B30461903
theorem B876767 : Blo 583288 876767 := bstep (se 1 (by rfl) ⟨657575, by rfl⟩ : syracuseStep 876767 = 1315151) B1315151
theorem B877307 : Blo 583288 877307 := bstep (se 1 (by rfl) ⟨657980, by rfl⟩ : syracuseStep 877307 = 1315961) B1315961
theorem B4220363 : Blo 583288 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B583327 : Blo 583288 583327 := bstep (se 1 (by rfl) ⟨437495, by rfl⟩ : syracuseStep 583327 = 874991) B874991
theorem B583375 : Blo 583288 583375 := bstep (se 1 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 583375 = 875063) B875063
theorem B583839 : Blo 583288 583839 := bstep (se 1 (by rfl) ⟨437879, by rfl⟩ : syracuseStep 583839 = 875759) B875759
theorem B16051441 : Blo 583288 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B585471 : Blo 583288 585471 := bstep (se 1 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 585471 = 878207) B878207
theorem B586479 : Blo 583288 586479 := bstep (se 1 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 586479 = 879719) B879719
theorem B587055 : Blo 583288 587055 := bstep (se 1 (by rfl) ⟨440291, by rfl⟩ : syracuseStep 587055 = 880583) B880583
theorem B32078369 : Blo 583288 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B2817017 : Blo 583288 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B4556903 : Blo 583288 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B27004043 : Blo 583288 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B21401921 : Blo 583288 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B1315655 : Blo 583288 1315655 := bstep (se 1 (by rfl) ⟨986741, by rfl⟩ : syracuseStep 1315655 = 1973483) B1973483
theorem B988159 : Blo 583288 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B13538623 : Blo 583288 13538623 := bstep (se 1 (by rfl) ⟨10153967, by rfl⟩ : syracuseStep 13538623 = 20307935) B20307935
theorem B988841 : Blo 583288 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B2498633 : Blo 583288 2498633 := bstep (se 2 (by rfl) ⟨936987, by rfl⟩ : syracuseStep 2498633 = 1873975) B1873975
theorem B1878011 : Blo 583288 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B5712383 : Blo 583288 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B1583707 : Blo 583288 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B1782667 : Blo 583288 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B10269683 : Blo 583288 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B1881215 : Blo 583288 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B10007711 : Blo 583288 10007711 := bstep (se 1 (by rfl) ⟨7505783, by rfl⟩ : syracuseStep 10007711 = 15011567) B15011567
theorem B11254301 : Blo 583288 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B12697843 : Blo 583288 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B6342695 : Blo 583288 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B4443497 : Blo 583288 4443497 := bstep (se 2 (by rfl) ⟨1666311, by rfl⟩ : syracuseStep 4443497 = 3332623) B3332623
theorem B21385579 : Blo 583288 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B875291 : Blo 583288 875291 := bstep (se 1 (by rfl) ⟨656468, by rfl⟩ : syracuseStep 875291 = 1312937) B1312937
theorem B25386695 : Blo 583288 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B876239 : Blo 583288 876239 := bstep (se 1 (by rfl) ⟨657179, by rfl⟩ : syracuseStep 876239 = 1314359) B1314359
theorem B876287 : Blo 583288 876287 := bstep (se 1 (by rfl) ⟨657215, by rfl⟩ : syracuseStep 876287 = 1314431) B1314431
theorem B3760121 : Blo 583288 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B877193 : Blo 583288 877193 := bstep (se 2 (by rfl) ⟨328947, by rfl⟩ : syracuseStep 877193 = 657895) B657895
theorem B1664239 : Blo 583288 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B1664297 : Blo 583288 1664297 := bstep (se 2 (by rfl) ⟨624111, by rfl⟩ : syracuseStep 1664297 = 1248223) B1248223
theorem B878015 : Blo 583288 878015 := bstep (se 1 (by rfl) ⟨658511, by rfl⟩ : syracuseStep 878015 = 1317023) B1317023
theorem B878057 : Blo 583288 878057 := bstep (se 2 (by rfl) ⟨329271, by rfl⟩ : syracuseStep 878057 = 658543) B658543
theorem B583451 : Blo 583288 583451 := bstep (se 1 (by rfl) ⟨437588, by rfl⟩ : syracuseStep 583451 = 875177) B875177
theorem B3336065 : Blo 583288 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B17983883 : Blo 583288 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B584127 : Blo 583288 584127 := bstep (se 1 (by rfl) ⟨438095, by rfl⟩ : syracuseStep 584127 = 876191) B876191
theorem B3336815 : Blo 583288 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B584511 : Blo 583288 584511 := bstep (se 1 (by rfl) ⟨438383, by rfl⟩ : syracuseStep 584511 = 876767) B876767
theorem B584871 : Blo 583288 584871 := bstep (se 1 (by rfl) ⟨438653, by rfl⟩ : syracuseStep 584871 = 877307) B877307
theorem B880265 : Blo 583288 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B31948739 : Blo 583288 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B4228463 : Blo 583288 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B659227 : Blo 583288 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B9507557 : Blo 583288 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B28514105 : Blo 583288 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B1252007 : Blo 583288 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B1317545 : Blo 583288 1317545 := bstep (se 2 (by rfl) ⟨494079, by rfl⟩ : syracuseStep 1317545 = 988159) B988159
theorem B3808255 : Blo 583288 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B1254143 : Blo 583288 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B48606965 : Blo 583288 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B2962331 : Blo 583288 2962331 := bstep (se 1 (by rfl) ⟨2221748, by rfl⟩ : syracuseStep 2962331 = 4443497) B4443497
theorem B14267947 : Blo 583288 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B2111609 : Blo 583288 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B16924463 : Blo 583288 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B2506747 : Blo 583288 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B72010781 : Blo 583288 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B6671807 : Blo 583288 6671807 := bstep (se 1 (by rfl) ⟨5003855, by rfl⟩ : syracuseStep 6671807 = 10007711) B10007711
theorem B16930457 : Blo 583288 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B2218985 : Blo 583288 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B877103 : Blo 583288 877103 := bstep (se 1 (by rfl) ⟨657827, by rfl⟩ : syracuseStep 877103 = 1315655) B1315655
theorem B583527 : Blo 583288 583527 := bstep (se 1 (by rfl) ⟨437645, by rfl⟩ : syracuseStep 583527 = 875291) B875291
theorem B584159 : Blo 583288 584159 := bstep (se 1 (by rfl) ⟨438119, by rfl⟩ : syracuseStep 584159 = 876239) B876239
theorem B584191 : Blo 583288 584191 := bstep (se 1 (by rfl) ⟨438143, by rfl⟩ : syracuseStep 584191 = 876287) B876287
theorem B1665755 : Blo 583288 1665755 := bstep (se 1 (by rfl) ⟨1249316, by rfl⟩ : syracuseStep 1665755 = 2498633) B2498633
theorem B584795 : Blo 583288 584795 := bstep (se 1 (by rfl) ⟨438596, by rfl⟩ : syracuseStep 584795 = 877193) B877193
theorem B1109531 : Blo 583288 1109531 := bstep (se 1 (by rfl) ⟨832148, by rfl⟩ : syracuseStep 1109531 = 1664297) B1664297
theorem B585343 : Blo 583288 585343 := bstep (se 1 (by rfl) ⟨439007, by rfl⟩ : syracuseStep 585343 = 878015) B878015
theorem B585371 : Blo 583288 585371 := bstep (se 1 (by rfl) ⟨439028, by rfl⟩ : syracuseStep 585371 = 878057) B878057
theorem B2224043 : Blo 583288 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B11989255 : Blo 583288 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B2224543 : Blo 583288 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B18051497 : Blo 583288 18051497 := bstep (se 2 (by rfl) ⟨6769311, by rfl⟩ : syracuseStep 18051497 = 13538623) B13538623
theorem B586843 : Blo 583288 586843 := bstep (se 1 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 586843 = 880265) B880265
theorem B6846455 : Blo 583288 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B7502867 : Blo 583288 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B21299159 : Blo 583288 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B2818975 : Blo 583288 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B48007187 : Blo 583288 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B19009403 : Blo 583288 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B1479323 : Blo 583288 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B18257213 : Blo 583288 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B1482695 : Blo 583288 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B12034331 : Blo 583288 12034331 := bstep (se 1 (by rfl) ⟨9025748, by rfl⟩ : syracuseStep 12034331 = 18051497) B18051497
theorem B1974887 : Blo 583288 1974887 := bstep (se 1 (by rfl) ⟨1481165, by rfl⟩ : syracuseStep 1974887 = 2962331) B2962331
theorem B11282975 : Blo 583288 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B56797757 : Blo 583288 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B6338371 : Blo 583288 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B11286971 : Blo 583288 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B834671 : Blo 583288 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B836095 : Blo 583288 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B2966057 : Blo 583288 2966057 := bstep (se 2 (by rfl) ⟨1112271, by rfl⟩ : syracuseStep 2966057 = 2224543) B2224543
theorem B19023929 : Blo 583288 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B739687 : Blo 583288 739687 := bstep (se 1 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 739687 = 1109531) B1109531
theorem B5001911 : Blo 583288 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B4447871 : Blo 583288 4447871 := bstep (se 1 (by rfl) ⟨3335903, by rfl⟩ : syracuseStep 4447871 = 6671807) B6671807
theorem B878363 : Blo 583288 878363 := bstep (se 1 (by rfl) ⟨658772, by rfl⟩ : syracuseStep 878363 = 1317545) B1317545
theorem B878969 : Blo 583288 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B5630957 : Blo 583288 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B15985673 : Blo 583288 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B584735 : Blo 583288 584735 := bstep (se 1 (by rfl) ⟨438551, by rfl⟩ : syracuseStep 584735 = 877103) B877103
theorem B1110503 : Blo 583288 1110503 := bstep (se 1 (by rfl) ⟨832877, by rfl⟩ : syracuseStep 1110503 = 1665755) B1665755
theorem B32404643 : Blo 583288 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B5077673 : Blo 583288 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B3342329 : Blo 583288 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B1114793 : Blo 583288 1114793 := bstep (se 2 (by rfl) ⟨418047, by rfl⟩ : syracuseStep 1114793 = 836095) B836095
theorem B12682619 : Blo 583288 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B986215 : Blo 583288 986215 := bstep (se 1 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 986215 = 1479323) B1479323
theorem B986249 : Blo 583288 986249 := bstep (se 2 (by rfl) ⟨369843, by rfl⟩ : syracuseStep 986249 = 739687) B739687
theorem B988463 : Blo 583288 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B1316591 : Blo 583288 1316591 := bstep (se 1 (by rfl) ⟨987443, by rfl⟩ : syracuseStep 1316591 = 1974887) B1974887
theorem B10657115 : Blo 583288 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B21603095 : Blo 583288 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B3385115 : Blo 583288 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B1977371 : Blo 583288 1977371 := bstep (se 1 (by rfl) ⟨1483028, by rfl⟩ : syracuseStep 1977371 = 2966057) B2966057
theorem B12171475 : Blo 583288 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B2965247 : Blo 583288 2965247 := bstep (se 1 (by rfl) ⟨2223935, by rfl⟩ : syracuseStep 2965247 = 4447871) B4447871
theorem B7521983 : Blo 583288 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B37865171 : Blo 583288 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B3753971 : Blo 583288 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B740335 : Blo 583288 740335 := bstep (se 1 (by rfl) ⟨555251, by rfl⟩ : syracuseStep 740335 = 1110503) B1110503
theorem B7524647 : Blo 583288 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B3758633 : Blo 583288 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B32004791 : Blo 583288 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B12672935 : Blo 583288 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B3334607 : Blo 583288 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B8022887 : Blo 583288 8022887 := bstep (se 1 (by rfl) ⟨6017165, by rfl⟩ : syracuseStep 8022887 = 12034331) B12034331
theorem B585575 : Blo 583288 585575 := bstep (se 1 (by rfl) ⟨439181, by rfl⟩ : syracuseStep 585575 = 878363) B878363
theorem B585979 : Blo 583288 585979 := bstep (se 1 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 585979 = 878969) B878969
theorem B8451161 : Blo 583288 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B2225789 : Blo 583288 2225789 := bstep (se 3 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 2225789 = 834671) B834671
theorem B2228219 : Blo 583288 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B8455079 : Blo 583288 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B64914533 : Blo 583288 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B5014655 : Blo 583288 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B657499 : Blo 583288 657499 := bstep (se 1 (by rfl) ⟨493124, by rfl⟩ : syracuseStep 657499 = 986249) B986249
theorem B5016431 : Blo 583288 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B658975 : Blo 583288 658975 := bstep (se 1 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 658975 = 988463) B988463
theorem B987113 : Blo 583288 987113 := bstep (se 2 (by rfl) ⟨370167, by rfl⟩ : syracuseStep 987113 = 740335) B740335
theorem B1314953 : Blo 583288 1314953 := bstep (se 2 (by rfl) ⟨493107, by rfl⟩ : syracuseStep 1314953 = 986215) B986215
theorem B21336527 : Blo 583288 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B5348591 : Blo 583288 5348591 := bstep (se 1 (by rfl) ⟨4011443, by rfl⟩ : syracuseStep 5348591 = 8022887) B8022887
theorem B1318247 : Blo 583288 1318247 := bstep (se 1 (by rfl) ⟨988685, by rfl⟩ : syracuseStep 1318247 = 1977371) B1977371
theorem B1483859 : Blo 583288 1483859 := bstep (se 1 (by rfl) ⟨1112894, by rfl⟩ : syracuseStep 1483859 = 2225789) B2225789
theorem B1976831 : Blo 583288 1976831 := bstep (se 1 (by rfl) ⟨1482623, by rfl⟩ : syracuseStep 1976831 = 2965247) B2965247
theorem B1485479 : Blo 583288 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B25243447 : Blo 583288 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B2502647 : Blo 583288 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B2505755 : Blo 583288 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B14402063 : Blo 583288 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B743195 : Blo 583288 743195 := bstep (se 1 (by rfl) ⟨557396, by rfl⟩ : syracuseStep 743195 = 1114793) B1114793
theorem B877727 : Blo 583288 877727 := bstep (se 1 (by rfl) ⟨658295, by rfl⟩ : syracuseStep 877727 = 1316591) B1316591
theorem B7104743 : Blo 583288 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B8448623 : Blo 583288 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B2223071 : Blo 583288 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B2256743 : Blo 583288 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B5634107 : Blo 583288 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B9601375 : Blo 583288 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B5636719 : Blo 583288 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B3343103 : Blo 583288 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B3344287 : Blo 583288 3344287 := bstep (se 1 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 3344287 = 5016431) B5016431
theorem B658075 : Blo 583288 658075 := bstep (se 1 (by rfl) ⟨493556, by rfl⟩ : syracuseStep 658075 = 987113) B987113
theorem B14224351 : Blo 583288 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B33657929 : Blo 583288 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B989239 : Blo 583288 989239 := bstep (se 1 (by rfl) ⟨741929, by rfl⟩ : syracuseStep 989239 = 1483859) B1483859
theorem B1317887 : Blo 583288 1317887 := bstep (se 1 (by rfl) ⟨988415, by rfl⟩ : syracuseStep 1317887 = 1976831) B1976831
theorem B990319 : Blo 583288 990319 := bstep (se 1 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 990319 = 1485479) B1485479
theorem B1482047 : Blo 583288 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B1981853 : Blo 583288 1981853 := bstep (se 3 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 1981853 = 743195) B743195
theorem B4736495 : Blo 583288 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B3756071 : Blo 583288 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B43276355 : Blo 583288 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B876635 : Blo 583288 876635 := bstep (se 1 (by rfl) ⟨657476, by rfl⟩ : syracuseStep 876635 = 1314953) B1314953
theorem B876665 : Blo 583288 876665 := bstep (se 2 (by rfl) ⟨328749, by rfl⟩ : syracuseStep 876665 = 657499) B657499
theorem B878633 : Blo 583288 878633 := bstep (se 2 (by rfl) ⟨329487, by rfl⟩ : syracuseStep 878633 = 658975) B658975
theorem B3565727 : Blo 583288 3565727 := bstep (se 1 (by rfl) ⟨2674295, by rfl⟩ : syracuseStep 3565727 = 5348591) B5348591
theorem B878831 : Blo 583288 878831 := bstep (se 1 (by rfl) ⟨659123, by rfl⟩ : syracuseStep 878831 = 1318247) B1318247
theorem B585151 : Blo 583288 585151 := bstep (se 1 (by rfl) ⟨438863, by rfl⟩ : syracuseStep 585151 = 877727) B877727
theorem B5632415 : Blo 583288 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B1504495 : Blo 583288 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B1668431 : Blo 583288 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B6682013 : Blo 583288 6682013 := bstep (se 3 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 6682013 = 2505755) B2505755
theorem B2228735 : Blo 583288 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B4459049 : Blo 583288 4459049 := bstep (se 2 (by rfl) ⟨1672143, by rfl⟩ : syracuseStep 4459049 = 3344287) B3344287
theorem B988031 : Blo 583288 988031 := bstep (se 1 (by rfl) ⟨741023, by rfl⟩ : syracuseStep 988031 = 1482047) B1482047
theorem B2005993 : Blo 583288 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B1318985 : Blo 583288 1318985 := bstep (se 2 (by rfl) ⟨494619, by rfl⟩ : syracuseStep 1318985 = 989239) B989239
theorem B1320425 : Blo 583288 1320425 := bstep (se 2 (by rfl) ⟨495159, by rfl⟩ : syracuseStep 1320425 = 990319) B990319
theorem B1321235 : Blo 583288 1321235 := bstep (se 1 (by rfl) ⟨990926, by rfl⟩ : syracuseStep 1321235 = 1981853) B1981853
theorem B7515625 : Blo 583288 7515625 := bstep (se 2 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 7515625 = 5636719) B5636719
theorem B3157663 : Blo 583288 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B2504047 : Blo 583288 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B28850903 : Blo 583288 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B2377151 : Blo 583288 2377151 := bstep (se 1 (by rfl) ⟨1782863, by rfl⟩ : syracuseStep 2377151 = 3565727) B3565727
theorem B3754943 : Blo 583288 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B12801833 : Blo 583288 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B22438619 : Blo 583288 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B877433 : Blo 583288 877433 := bstep (se 2 (by rfl) ⟨329037, by rfl⟩ : syracuseStep 877433 = 658075) B658075
theorem B18965801 : Blo 583288 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B878591 : Blo 583288 878591 := bstep (se 1 (by rfl) ⟨658943, by rfl⟩ : syracuseStep 878591 = 1317887) B1317887
theorem B584423 : Blo 583288 584423 := bstep (se 1 (by rfl) ⟨438317, by rfl⟩ : syracuseStep 584423 = 876635) B876635
theorem B584443 : Blo 583288 584443 := bstep (se 1 (by rfl) ⟨438332, by rfl⟩ : syracuseStep 584443 = 876665) B876665
theorem B585755 : Blo 583288 585755 := bstep (se 1 (by rfl) ⟨439316, by rfl⟩ : syracuseStep 585755 = 878633) B878633
theorem B585887 : Blo 583288 585887 := bstep (se 1 (by rfl) ⟨439415, by rfl⟩ : syracuseStep 585887 = 878831) B878831
theorem B1112287 : Blo 583288 1112287 := bstep (se 1 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 1112287 = 1668431) B1668431
theorem B4454675 : Blo 583288 4454675 := bstep (se 1 (by rfl) ⟨3341006, by rfl⟩ : syracuseStep 4454675 = 6682013) B6682013
theorem B658687 : Blo 583288 658687 := bstep (se 1 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 658687 = 988031) B988031
theorem B1483049 : Blo 583288 1483049 := bstep (se 2 (by rfl) ⟨556143, by rfl⟩ : syracuseStep 1483049 = 1112287) B1112287
theorem B1485823 : Blo 583288 1485823 := bstep (se 1 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 1485823 = 2228735) B2228735
theorem B1584767 : Blo 583288 1584767 := bstep (se 1 (by rfl) ⟨1188575, by rfl⟩ : syracuseStep 1584767 = 2377151) B2377151
theorem B2503295 : Blo 583288 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B8534555 : Blo 583288 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B4210217 : Blo 583288 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B14959079 : Blo 583288 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B2674657 : Blo 583288 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B2969783 : Blo 583288 2969783 := bstep (se 1 (by rfl) ⟨2227337, by rfl⟩ : syracuseStep 2969783 = 4454675) B4454675
theorem B2972699 : Blo 583288 2972699 := bstep (se 1 (by rfl) ⟨2229524, by rfl⟩ : syracuseStep 2972699 = 4459049) B4459049
theorem B10020833 : Blo 583288 10020833 := bstep (se 2 (by rfl) ⟨3757812, by rfl⟩ : syracuseStep 10020833 = 7515625) B7515625
theorem B879323 : Blo 583288 879323 := bstep (se 1 (by rfl) ⟨659492, by rfl⟩ : syracuseStep 879323 = 1318985) B1318985
theorem B584955 : Blo 583288 584955 := bstep (se 1 (by rfl) ⟨438716, by rfl⟩ : syracuseStep 584955 = 877433) B877433
theorem B12643867 : Blo 583288 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B880283 : Blo 583288 880283 := bstep (se 1 (by rfl) ⟨660212, by rfl⟩ : syracuseStep 880283 = 1320425) B1320425
theorem B585727 : Blo 583288 585727 := bstep (se 1 (by rfl) ⟨439295, by rfl⟩ : syracuseStep 585727 = 878591) B878591
theorem B880823 : Blo 583288 880823 := bstep (se 1 (by rfl) ⟨660617, by rfl⟩ : syracuseStep 880823 = 1321235) B1321235
theorem B3338729 : Blo 583288 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B19233935 : Blo 583288 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B988699 : Blo 583288 988699 := bstep (se 1 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 988699 = 1483049) B1483049
theorem B1056511 : Blo 583288 1056511 := bstep (se 1 (by rfl) ⟨792383, by rfl⟩ : syracuseStep 1056511 = 1584767) B1584767
theorem B12822623 : Blo 583288 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B9972719 : Blo 583288 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B1979855 : Blo 583288 1979855 := bstep (se 1 (by rfl) ⟨1484891, by rfl⟩ : syracuseStep 1979855 = 2969783) B2969783
theorem B1981097 : Blo 583288 1981097 := bstep (se 2 (by rfl) ⟨742911, by rfl⟩ : syracuseStep 1981097 = 1485823) B1485823
theorem B1981799 : Blo 583288 1981799 := bstep (se 1 (by rfl) ⟨1486349, by rfl⟩ : syracuseStep 1981799 = 2972699) B2972699
theorem B16858489 : Blo 583288 16858489 := bstep (se 2 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 16858489 = 12643867) B12643867
theorem B5689703 : Blo 583288 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B2806811 : Blo 583288 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B878249 : Blo 583288 878249 := bstep (se 2 (by rfl) ⟨329343, by rfl⟩ : syracuseStep 878249 = 658687) B658687
theorem B3566209 : Blo 583288 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B6680555 : Blo 583288 6680555 := bstep (se 1 (by rfl) ⟨5010416, by rfl⟩ : syracuseStep 6680555 = 10020833) B10020833
theorem B586215 : Blo 583288 586215 := bstep (se 1 (by rfl) ⟨439661, by rfl⟩ : syracuseStep 586215 = 879323) B879323
theorem B586855 : Blo 583288 586855 := bstep (se 1 (by rfl) ⟨440141, by rfl⟩ : syracuseStep 586855 = 880283) B880283
theorem B587215 : Blo 583288 587215 := bstep (se 1 (by rfl) ⟨440411, by rfl⟩ : syracuseStep 587215 = 880823) B880823
theorem B2225819 : Blo 583288 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B1668863 : Blo 583288 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B15172541 : Blo 583288 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B1871207 : Blo 583288 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B4754945 : Blo 583288 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B1318265 : Blo 583288 1318265 := bstep (se 2 (by rfl) ⟨494349, by rfl⟩ : syracuseStep 1318265 = 988699) B988699
theorem B1319903 : Blo 583288 1319903 := bstep (se 1 (by rfl) ⟨989927, by rfl⟩ : syracuseStep 1319903 = 1979855) B1979855
theorem B1483879 : Blo 583288 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B1320731 : Blo 583288 1320731 := bstep (se 1 (by rfl) ⟨990548, by rfl⟩ : syracuseStep 1320731 = 1981097) B1981097
theorem B1321199 : Blo 583288 1321199 := bstep (se 1 (by rfl) ⟨990899, by rfl⟩ : syracuseStep 1321199 = 1981799) B1981799
theorem B4450301 : Blo 583288 4450301 := bstep (se 3 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 4450301 = 1668863) B1668863
theorem B585499 : Blo 583288 585499 := bstep (se 1 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 585499 = 878249) B878249
theorem B8548415 : Blo 583288 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B6648479 : Blo 583288 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B4453703 : Blo 583288 4453703 := bstep (se 1 (by rfl) ⟨3340277, by rfl⟩ : syracuseStep 4453703 = 6680555) B6680555
theorem B22477985 : Blo 583288 22477985 := bstep (se 2 (by rfl) ⟨8429244, by rfl⟩ : syracuseStep 22477985 = 16858489) B16858489
theorem B1408681 : Blo 583288 1408681 := bstep (se 2 (by rfl) ⟨528255, by rfl⟩ : syracuseStep 1408681 = 1056511) B1056511
theorem B1247471 : Blo 583288 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B4432319 : Blo 583288 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B14985323 : Blo 583288 14985323 := bstep (se 1 (by rfl) ⟨11238992, by rfl⟩ : syracuseStep 14985323 = 22477985) B22477985
theorem B1878241 : Blo 583288 1878241 := bstep (se 2 (by rfl) ⟨704340, by rfl⟩ : syracuseStep 1878241 = 1408681) B1408681
theorem B1978505 : Blo 583288 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B2966867 : Blo 583288 2966867 := bstep (se 1 (by rfl) ⟨2225150, by rfl⟩ : syracuseStep 2966867 = 4450301) B4450301
theorem B2969135 : Blo 583288 2969135 := bstep (se 1 (by rfl) ⟨2226851, by rfl⟩ : syracuseStep 2969135 = 4453703) B4453703
theorem B10115027 : Blo 583288 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B3169963 : Blo 583288 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B878843 : Blo 583288 878843 := bstep (se 1 (by rfl) ⟨659132, by rfl⟩ : syracuseStep 878843 = 1318265) B1318265
theorem B879935 : Blo 583288 879935 := bstep (se 1 (by rfl) ⟨659951, by rfl⟩ : syracuseStep 879935 = 1319903) B1319903
theorem B880487 : Blo 583288 880487 := bstep (se 1 (by rfl) ⟨660365, by rfl⟩ : syracuseStep 880487 = 1320731) B1320731
theorem B880799 : Blo 583288 880799 := bstep (se 1 (by rfl) ⟨660599, by rfl⟩ : syracuseStep 880799 = 1321199) B1321199
theorem B5698943 : Blo 583288 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B2954879 : Blo 583288 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B1319003 : Blo 583288 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B1977911 : Blo 583288 1977911 := bstep (se 1 (by rfl) ⟨1483433, by rfl⟩ : syracuseStep 1977911 = 2966867) B2966867
theorem B831647 : Blo 583288 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B1979423 : Blo 583288 1979423 := bstep (se 1 (by rfl) ⟨1484567, by rfl⟩ : syracuseStep 1979423 = 2969135) B2969135
theorem B2504321 : Blo 583288 2504321 := bstep (se 2 (by rfl) ⟨939120, by rfl⟩ : syracuseStep 2504321 = 1878241) B1878241
theorem B6743351 : Blo 583288 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B9990215 : Blo 583288 9990215 := bstep (se 1 (by rfl) ⟨7492661, by rfl⟩ : syracuseStep 9990215 = 14985323) B14985323
theorem B585895 : Blo 583288 585895 := bstep (se 1 (by rfl) ⟨439421, by rfl⟩ : syracuseStep 585895 = 878843) B878843
theorem B586623 : Blo 583288 586623 := bstep (se 1 (by rfl) ⟨439967, by rfl⟩ : syracuseStep 586623 = 879935) B879935
theorem B586991 : Blo 583288 586991 := bstep (se 1 (by rfl) ⟨440243, by rfl⟩ : syracuseStep 586991 = 880487) B880487
theorem B587199 : Blo 583288 587199 := bstep (se 1 (by rfl) ⟨440399, by rfl⟩ : syracuseStep 587199 = 880799) B880799
theorem B3799295 : Blo 583288 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B4226617 : Blo 583288 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B1969919 : Blo 583288 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B4495567 : Blo 583288 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B1318607 : Blo 583288 1318607 := bstep (se 1 (by rfl) ⟨988955, by rfl⟩ : syracuseStep 1318607 = 1977911) B1977911
theorem B6660143 : Blo 583288 6660143 := bstep (se 1 (by rfl) ⟨4995107, by rfl⟩ : syracuseStep 6660143 = 9990215) B9990215
theorem B1319615 : Blo 583288 1319615 := bstep (se 1 (by rfl) ⟨989711, by rfl⟩ : syracuseStep 1319615 = 1979423) B1979423
theorem B2532863 : Blo 583288 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B2217725 : Blo 583288 2217725 := bstep (se 3 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 2217725 = 831647) B831647
theorem B879335 : Blo 583288 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B1669547 : Blo 583288 1669547 := bstep (se 1 (by rfl) ⟨1252160, by rfl⟩ : syracuseStep 1669547 = 2504321) B2504321
theorem B5635489 : Blo 583288 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B1313279 : Blo 583288 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B1478483 : Blo 583288 1478483 := bstep (se 1 (by rfl) ⟨1108862, by rfl⟩ : syracuseStep 1478483 = 2217725) B2217725
theorem B7513985 : Blo 583288 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B4440095 : Blo 583288 4440095 := bstep (se 1 (by rfl) ⟨3330071, by rfl⟩ : syracuseStep 4440095 = 6660143) B6660143
theorem B1688575 : Blo 583288 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B879071 : Blo 583288 879071 := bstep (se 1 (by rfl) ⟨659303, by rfl⟩ : syracuseStep 879071 = 1318607) B1318607
theorem B879743 : Blo 583288 879743 := bstep (se 1 (by rfl) ⟨659807, by rfl⟩ : syracuseStep 879743 = 1319615) B1319615
theorem B586223 : Blo 583288 586223 := bstep (se 1 (by rfl) ⟨439667, by rfl⟩ : syracuseStep 586223 = 879335) B879335
theorem B5994089 : Blo 583288 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B1113031 : Blo 583288 1113031 := bstep (se 1 (by rfl) ⟨834773, by rfl⟩ : syracuseStep 1113031 = 1669547) B1669547
theorem B985655 : Blo 583288 985655 := bstep (se 1 (by rfl) ⟨739241, by rfl⟩ : syracuseStep 985655 = 1478483) B1478483
theorem B1484041 : Blo 583288 1484041 := bstep (se 2 (by rfl) ⟨556515, by rfl⟩ : syracuseStep 1484041 = 1113031) B1113031
theorem B2960063 : Blo 583288 2960063 := bstep (se 1 (by rfl) ⟨2220047, by rfl⟩ : syracuseStep 2960063 = 4440095) B4440095
theorem B2251433 : Blo 583288 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B875519 : Blo 583288 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B5009323 : Blo 583288 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B586047 : Blo 583288 586047 := bstep (se 1 (by rfl) ⟨439535, by rfl⟩ : syracuseStep 586047 = 879071) B879071
theorem B586495 : Blo 583288 586495 := bstep (se 1 (by rfl) ⟨439871, by rfl⟩ : syracuseStep 586495 = 879743) B879743
theorem B3996059 : Blo 583288 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B657103 : Blo 583288 657103 := bstep (se 1 (by rfl) ⟨492827, by rfl⟩ : syracuseStep 657103 = 985655) B985655
theorem B10656157 : Blo 583288 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B6003821 : Blo 583288 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B1973375 : Blo 583288 1973375 := bstep (se 1 (by rfl) ⟨1480031, by rfl⟩ : syracuseStep 1973375 = 2960063) B2960063
theorem B1978721 : Blo 583288 1978721 := bstep (se 2 (by rfl) ⟨742020, by rfl⟩ : syracuseStep 1978721 = 1484041) B1484041
theorem B583679 : Blo 583288 583679 := bstep (se 1 (by rfl) ⟨437759, by rfl⟩ : syracuseStep 583679 = 875519) B875519
theorem B6679097 : Blo 583288 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B4002547 : Blo 583288 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B1315583 : Blo 583288 1315583 := bstep (se 1 (by rfl) ⟨986687, by rfl⟩ : syracuseStep 1315583 = 1973375) B1973375
theorem B1319147 : Blo 583288 1319147 := bstep (se 1 (by rfl) ⟨989360, by rfl⟩ : syracuseStep 1319147 = 1978721) B1978721
theorem B14208209 : Blo 583288 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B876137 : Blo 583288 876137 := bstep (se 2 (by rfl) ⟨328551, by rfl⟩ : syracuseStep 876137 = 657103) B657103
theorem B4452731 : Blo 583288 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B9472139 : Blo 583288 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B2968487 : Blo 583288 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B877055 : Blo 583288 877055 := bstep (se 1 (by rfl) ⟨657791, by rfl⟩ : syracuseStep 877055 = 1315583) B1315583
theorem B584091 : Blo 583288 584091 := bstep (se 1 (by rfl) ⟨438068, by rfl⟩ : syracuseStep 584091 = 876137) B876137
theorem B879431 : Blo 583288 879431 := bstep (se 1 (by rfl) ⟨659573, by rfl⟩ : syracuseStep 879431 = 1319147) B1319147
theorem B5336729 : Blo 583288 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B1978991 : Blo 583288 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B3557819 : Blo 583288 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B6314759 : Blo 583288 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B584703 : Blo 583288 584703 := bstep (se 1 (by rfl) ⟨438527, by rfl⟩ : syracuseStep 584703 = 877055) B877055
theorem B586287 : Blo 583288 586287 := bstep (se 1 (by rfl) ⟨439715, by rfl⟩ : syracuseStep 586287 = 879431) B879431
theorem B1319327 : Blo 583288 1319327 := bstep (se 1 (by rfl) ⟨989495, by rfl⟩ : syracuseStep 1319327 = 1978991) B1978991
theorem B2371879 : Blo 583288 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B4209839 : Blo 583288 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B3162505 : Blo 583288 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B2806559 : Blo 583288 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B879551 : Blo 583288 879551 := bstep (se 1 (by rfl) ⟨659663, by rfl⟩ : syracuseStep 879551 = 1319327) B1319327
theorem B1871039 : Blo 583288 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B4216673 : Blo 583288 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B586367 : Blo 583288 586367 := bstep (se 1 (by rfl) ⟨439775, by rfl⟩ : syracuseStep 586367 = 879551) B879551
theorem B4989437 : Blo 583288 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B2811115 : Blo 583288 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B3748153 : Blo 583288 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B3326291 : Blo 583288 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B4997537 : Blo 583288 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B2217527 : Blo 583288 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B1478351 : Blo 583288 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B3331691 : Blo 583288 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B985567 : Blo 583288 985567 := bstep (se 1 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 985567 = 1478351) B1478351
theorem B2221127 : Blo 583288 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B1314089 : Blo 583288 1314089 := bstep (se 2 (by rfl) ⟨492783, by rfl⟩ : syracuseStep 1314089 = 985567) B985567
theorem B1480751 : Blo 583288 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B987167 : Blo 583288 987167 := bstep (se 1 (by rfl) ⟨740375, by rfl⟩ : syracuseStep 987167 = 1480751) B1480751
theorem B876059 : Blo 583288 876059 := bstep (se 1 (by rfl) ⟨657044, by rfl⟩ : syracuseStep 876059 = 1314089) B1314089
theorem B658111 : Blo 583288 658111 := bstep (se 1 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 658111 = 987167) B987167
theorem B584039 : Blo 583288 584039 := bstep (se 1 (by rfl) ⟨438029, by rfl⟩ : syracuseStep 584039 = 876059) B876059
theorem B877481 : Blo 583288 877481 := bstep (se 2 (by rfl) ⟨329055, by rfl⟩ : syracuseStep 877481 = 658111) B658111
theorem B584987 : Blo 583288 584987 := bstep (se 1 (by rfl) ⟨438740, by rfl⟩ : syracuseStep 584987 = 877481) B877481

theorem C0 (j : ℕ) (h1 : 145822 ≤ j) (h2 : j ≤ 146521) : Blo 583288 (4 * j + 3) := by
  interval_cases j
  · exact B583291
  · exact B583295
  · exact B583299
  · exact B583303
  · exact B583307
  · exact B583311
  · exact B583315
  · exact B583319
  · exact B583323
  · exact B583327
  · exact B583331
  · exact B583335
  · exact B583339
  · exact B583343
  · exact B583347
  · exact B583351
  · exact B583355
  · exact B583359
  · exact B583363
  · exact B583367
  · exact B583371
  · exact B583375
  · exact B583379
  · exact B583383
  · exact B583387
  · exact B583391
  · exact B583395
  · exact B583399
  · exact B583403
  · exact B583407
  · exact B583411
  · exact B583415
  · exact B583419
  · exact B583423
  · exact B583427
  · exact B583431
  · exact B583435
  · exact B583439
  · exact B583443
  · exact B583447
  · exact B583451
  · exact B583455
  · exact B583459
  · exact B583463
  · exact B583467
  · exact B583471
  · exact B583475
  · exact B583479
  · exact B583483
  · exact B583487
  · exact B583491
  · exact B583495
  · exact B583499
  · exact B583503
  · exact B583507
  · exact B583511
  · exact B583515
  · exact B583519
  · exact B583523
  · exact B583527
  · exact B583531
  · exact B583535
  · exact B583539
  · exact B583543
  · exact B583547
  · exact B583551
  · exact B583555
  · exact B583559
  · exact B583563
  · exact B583567
  · exact B583571
  · exact B583575
  · exact B583579
  · exact B583583
  · exact B583587
  · exact B583591
  · exact B583595
  · exact B583599
  · exact B583603
  · exact B583607
  · exact B583611
  · exact B583615
  · exact B583619
  · exact B583623
  · exact B583627
  · exact B583631
  · exact B583635
  · exact B583639
  · exact B583643
  · exact B583647
  · exact B583651
  · exact B583655
  · exact B583659
  · exact B583663
  · exact B583667
  · exact B583671
  · exact B583675
  · exact B583679
  · exact B583683
  · exact B583687
  · exact B583691
  · exact B583695
  · exact B583699
  · exact B583703
  · exact B583707
  · exact B583711
  · exact B583715
  · exact B583719
  · exact B583723
  · exact B583727
  · exact B583731
  · exact B583735
  · exact B583739
  · exact B583743
  · exact B583747
  · exact B583751
  · exact B583755
  · exact B583759
  · exact B583763
  · exact B583767
  · exact B583771
  · exact B583775
  · exact B583779
  · exact B583783
  · exact B583787
  · exact B583791
  · exact B583795
  · exact B583799
  · exact B583803
  · exact B583807
  · exact B583811
  · exact B583815
  · exact B583819
  · exact B583823
  · exact B583827
  · exact B583831
  · exact B583835
  · exact B583839
  · exact B583843
  · exact B583847
  · exact B583851
  · exact B583855
  · exact B583859
  · exact B583863
  · exact B583867
  · exact B583871
  · exact B583875
  · exact B583879
  · exact B583883
  · exact B583887
  · exact B583891
  · exact B583895
  · exact B583899
  · exact B583903
  · exact B583907
  · exact B583911
  · exact B583915
  · exact B583919
  · exact B583923
  · exact B583927
  · exact B583931
  · exact B583935
  · exact B583939
  · exact B583943
  · exact B583947
  · exact B583951
  · exact B583955
  · exact B583959
  · exact B583963
  · exact B583967
  · exact B583971
  · exact B583975
  · exact B583979
  · exact B583983
  · exact B583987
  · exact B583991
  · exact B583995
  · exact B583999
  · exact B584003
  · exact B584007
  · exact B584011
  · exact B584015
  · exact B584019
  · exact B584023
  · exact B584027
  · exact B584031
  · exact B584035
  · exact B584039
  · exact B584043
  · exact B584047
  · exact B584051
  · exact B584055
  · exact B584059
  · exact B584063
  · exact B584067
  · exact B584071
  · exact B584075
  · exact B584079
  · exact B584083
  · exact B584087
  · exact B584091
  · exact B584095
  · exact B584099
  · exact B584103
  · exact B584107
  · exact B584111
  · exact B584115
  · exact B584119
  · exact B584123
  · exact B584127
  · exact B584131
  · exact B584135
  · exact B584139
  · exact B584143
  · exact B584147
  · exact B584151
  · exact B584155
  · exact B584159
  · exact B584163
  · exact B584167
  · exact B584171
  · exact B584175
  · exact B584179
  · exact B584183
  · exact B584187
  · exact B584191
  · exact B584195
  · exact B584199
  · exact B584203
  · exact B584207
  · exact B584211
  · exact B584215
  · exact B584219
  · exact B584223
  · exact B584227
  · exact B584231
  · exact B584235
  · exact B584239
  · exact B584243
  · exact B584247
  · exact B584251
  · exact B584255
  · exact B584259
  · exact B584263
  · exact B584267
  · exact B584271
  · exact B584275
  · exact B584279
  · exact B584283
  · exact B584287
  · exact B584291
  · exact B584295
  · exact B584299
  · exact B584303
  · exact B584307
  · exact B584311
  · exact B584315
  · exact B584319
  · exact B584323
  · exact B584327
  · exact B584331
  · exact B584335
  · exact B584339
  · exact B584343
  · exact B584347
  · exact B584351
  · exact B584355
  · exact B584359
  · exact B584363
  · exact B584367
  · exact B584371
  · exact B584375
  · exact B584379
  · exact B584383
  · exact B584387
  · exact B584391
  · exact B584395
  · exact B584399
  · exact B584403
  · exact B584407
  · exact B584411
  · exact B584415
  · exact B584419
  · exact B584423
  · exact B584427
  · exact B584431
  · exact B584435
  · exact B584439
  · exact B584443
  · exact B584447
  · exact B584451
  · exact B584455
  · exact B584459
  · exact B584463
  · exact B584467
  · exact B584471
  · exact B584475
  · exact B584479
  · exact B584483
  · exact B584487
  · exact B584491
  · exact B584495
  · exact B584499
  · exact B584503
  · exact B584507
  · exact B584511
  · exact B584515
  · exact B584519
  · exact B584523
  · exact B584527
  · exact B584531
  · exact B584535
  · exact B584539
  · exact B584543
  · exact B584547
  · exact B584551
  · exact B584555
  · exact B584559
  · exact B584563
  · exact B584567
  · exact B584571
  · exact B584575
  · exact B584579
  · exact B584583
  · exact B584587
  · exact B584591
  · exact B584595
  · exact B584599
  · exact B584603
  · exact B584607
  · exact B584611
  · exact B584615
  · exact B584619
  · exact B584623
  · exact B584627
  · exact B584631
  · exact B584635
  · exact B584639
  · exact B584643
  · exact B584647
  · exact B584651
  · exact B584655
  · exact B584659
  · exact B584663
  · exact B584667
  · exact B584671
  · exact B584675
  · exact B584679
  · exact B584683
  · exact B584687
  · exact B584691
  · exact B584695
  · exact B584699
  · exact B584703
  · exact B584707
  · exact B584711
  · exact B584715
  · exact B584719
  · exact B584723
  · exact B584727
  · exact B584731
  · exact B584735
  · exact B584739
  · exact B584743
  · exact B584747
  · exact B584751
  · exact B584755
  · exact B584759
  · exact B584763
  · exact B584767
  · exact B584771
  · exact B584775
  · exact B584779
  · exact B584783
  · exact B584787
  · exact B584791
  · exact B584795
  · exact B584799
  · exact B584803
  · exact B584807
  · exact B584811
  · exact B584815
  · exact B584819
  · exact B584823
  · exact B584827
  · exact B584831
  · exact B584835
  · exact B584839
  · exact B584843
  · exact B584847
  · exact B584851
  · exact B584855
  · exact B584859
  · exact B584863
  · exact B584867
  · exact B584871
  · exact B584875
  · exact B584879
  · exact B584883
  · exact B584887
  · exact B584891
  · exact B584895
  · exact B584899
  · exact B584903
  · exact B584907
  · exact B584911
  · exact B584915
  · exact B584919
  · exact B584923
  · exact B584927
  · exact B584931
  · exact B584935
  · exact B584939
  · exact B584943
  · exact B584947
  · exact B584951
  · exact B584955
  · exact B584959
  · exact B584963
  · exact B584967
  · exact B584971
  · exact B584975
  · exact B584979
  · exact B584983
  · exact B584987
  · exact B584991
  · exact B584995
  · exact B584999
  · exact B585003
  · exact B585007
  · exact B585011
  · exact B585015
  · exact B585019
  · exact B585023
  · exact B585027
  · exact B585031
  · exact B585035
  · exact B585039
  · exact B585043
  · exact B585047
  · exact B585051
  · exact B585055
  · exact B585059
  · exact B585063
  · exact B585067
  · exact B585071
  · exact B585075
  · exact B585079
  · exact B585083
  · exact B585087
  · exact B585091
  · exact B585095
  · exact B585099
  · exact B585103
  · exact B585107
  · exact B585111
  · exact B585115
  · exact B585119
  · exact B585123
  · exact B585127
  · exact B585131
  · exact B585135
  · exact B585139
  · exact B585143
  · exact B585147
  · exact B585151
  · exact B585155
  · exact B585159
  · exact B585163
  · exact B585167
  · exact B585171
  · exact B585175
  · exact B585179
  · exact B585183
  · exact B585187
  · exact B585191
  · exact B585195
  · exact B585199
  · exact B585203
  · exact B585207
  · exact B585211
  · exact B585215
  · exact B585219
  · exact B585223
  · exact B585227
  · exact B585231
  · exact B585235
  · exact B585239
  · exact B585243
  · exact B585247
  · exact B585251
  · exact B585255
  · exact B585259
  · exact B585263
  · exact B585267
  · exact B585271
  · exact B585275
  · exact B585279
  · exact B585283
  · exact B585287
  · exact B585291
  · exact B585295
  · exact B585299
  · exact B585303
  · exact B585307
  · exact B585311
  · exact B585315
  · exact B585319
  · exact B585323
  · exact B585327
  · exact B585331
  · exact B585335
  · exact B585339
  · exact B585343
  · exact B585347
  · exact B585351
  · exact B585355
  · exact B585359
  · exact B585363
  · exact B585367
  · exact B585371
  · exact B585375
  · exact B585379
  · exact B585383
  · exact B585387
  · exact B585391
  · exact B585395
  · exact B585399
  · exact B585403
  · exact B585407
  · exact B585411
  · exact B585415
  · exact B585419
  · exact B585423
  · exact B585427
  · exact B585431
  · exact B585435
  · exact B585439
  · exact B585443
  · exact B585447
  · exact B585451
  · exact B585455
  · exact B585459
  · exact B585463
  · exact B585467
  · exact B585471
  · exact B585475
  · exact B585479
  · exact B585483
  · exact B585487
  · exact B585491
  · exact B585495
  · exact B585499
  · exact B585503
  · exact B585507
  · exact B585511
  · exact B585515
  · exact B585519
  · exact B585523
  · exact B585527
  · exact B585531
  · exact B585535
  · exact B585539
  · exact B585543
  · exact B585547
  · exact B585551
  · exact B585555
  · exact B585559
  · exact B585563
  · exact B585567
  · exact B585571
  · exact B585575
  · exact B585579
  · exact B585583
  · exact B585587
  · exact B585591
  · exact B585595
  · exact B585599
  · exact B585603
  · exact B585607
  · exact B585611
  · exact B585615
  · exact B585619
  · exact B585623
  · exact B585627
  · exact B585631
  · exact B585635
  · exact B585639
  · exact B585643
  · exact B585647
  · exact B585651
  · exact B585655
  · exact B585659
  · exact B585663
  · exact B585667
  · exact B585671
  · exact B585675
  · exact B585679
  · exact B585683
  · exact B585687
  · exact B585691
  · exact B585695
  · exact B585699
  · exact B585703
  · exact B585707
  · exact B585711
  · exact B585715
  · exact B585719
  · exact B585723
  · exact B585727
  · exact B585731
  · exact B585735
  · exact B585739
  · exact B585743
  · exact B585747
  · exact B585751
  · exact B585755
  · exact B585759
  · exact B585763
  · exact B585767
  · exact B585771
  · exact B585775
  · exact B585779
  · exact B585783
  · exact B585787
  · exact B585791
  · exact B585795
  · exact B585799
  · exact B585803
  · exact B585807
  · exact B585811
  · exact B585815
  · exact B585819
  · exact B585823
  · exact B585827
  · exact B585831
  · exact B585835
  · exact B585839
  · exact B585843
  · exact B585847
  · exact B585851
  · exact B585855
  · exact B585859
  · exact B585863
  · exact B585867
  · exact B585871
  · exact B585875
  · exact B585879
  · exact B585883
  · exact B585887
  · exact B585891
  · exact B585895
  · exact B585899
  · exact B585903
  · exact B585907
  · exact B585911
  · exact B585915
  · exact B585919
  · exact B585923
  · exact B585927
  · exact B585931
  · exact B585935
  · exact B585939
  · exact B585943
  · exact B585947
  · exact B585951
  · exact B585955
  · exact B585959
  · exact B585963
  · exact B585967
  · exact B585971
  · exact B585975
  · exact B585979
  · exact B585983
  · exact B585987
  · exact B585991
  · exact B585995
  · exact B585999
  · exact B586003
  · exact B586007
  · exact B586011
  · exact B586015
  · exact B586019
  · exact B586023
  · exact B586027
  · exact B586031
  · exact B586035
  · exact B586039
  · exact B586043
  · exact B586047
  · exact B586051
  · exact B586055
  · exact B586059
  · exact B586063
  · exact B586067
  · exact B586071
  · exact B586075
  · exact B586079
  · exact B586083
  · exact B586087

theorem C1 (j : ℕ) (h1 : 146522 ≤ j) (h2 : j ≤ 146821) : Blo 583288 (4 * j + 3) := by
  interval_cases j
  · exact B586091
  · exact B586095
  · exact B586099
  · exact B586103
  · exact B586107
  · exact B586111
  · exact B586115
  · exact B586119
  · exact B586123
  · exact B586127
  · exact B586131
  · exact B586135
  · exact B586139
  · exact B586143
  · exact B586147
  · exact B586151
  · exact B586155
  · exact B586159
  · exact B586163
  · exact B586167
  · exact B586171
  · exact B586175
  · exact B586179
  · exact B586183
  · exact B586187
  · exact B586191
  · exact B586195
  · exact B586199
  · exact B586203
  · exact B586207
  · exact B586211
  · exact B586215
  · exact B586219
  · exact B586223
  · exact B586227
  · exact B586231
  · exact B586235
  · exact B586239
  · exact B586243
  · exact B586247
  · exact B586251
  · exact B586255
  · exact B586259
  · exact B586263
  · exact B586267
  · exact B586271
  · exact B586275
  · exact B586279
  · exact B586283
  · exact B586287
  · exact B586291
  · exact B586295
  · exact B586299
  · exact B586303
  · exact B586307
  · exact B586311
  · exact B586315
  · exact B586319
  · exact B586323
  · exact B586327
  · exact B586331
  · exact B586335
  · exact B586339
  · exact B586343
  · exact B586347
  · exact B586351
  · exact B586355
  · exact B586359
  · exact B586363
  · exact B586367
  · exact B586371
  · exact B586375
  · exact B586379
  · exact B586383
  · exact B586387
  · exact B586391
  · exact B586395
  · exact B586399
  · exact B586403
  · exact B586407
  · exact B586411
  · exact B586415
  · exact B586419
  · exact B586423
  · exact B586427
  · exact B586431
  · exact B586435
  · exact B586439
  · exact B586443
  · exact B586447
  · exact B586451
  · exact B586455
  · exact B586459
  · exact B586463
  · exact B586467
  · exact B586471
  · exact B586475
  · exact B586479
  · exact B586483
  · exact B586487
  · exact B586491
  · exact B586495
  · exact B586499
  · exact B586503
  · exact B586507
  · exact B586511
  · exact B586515
  · exact B586519
  · exact B586523
  · exact B586527
  · exact B586531
  · exact B586535
  · exact B586539
  · exact B586543
  · exact B586547
  · exact B586551
  · exact B586555
  · exact B586559
  · exact B586563
  · exact B586567
  · exact B586571
  · exact B586575
  · exact B586579
  · exact B586583
  · exact B586587
  · exact B586591
  · exact B586595
  · exact B586599
  · exact B586603
  · exact B586607
  · exact B586611
  · exact B586615
  · exact B586619
  · exact B586623
  · exact B586627
  · exact B586631
  · exact B586635
  · exact B586639
  · exact B586643
  · exact B586647
  · exact B586651
  · exact B586655
  · exact B586659
  · exact B586663
  · exact B586667
  · exact B586671
  · exact B586675
  · exact B586679
  · exact B586683
  · exact B586687
  · exact B586691
  · exact B586695
  · exact B586699
  · exact B586703
  · exact B586707
  · exact B586711
  · exact B586715
  · exact B586719
  · exact B586723
  · exact B586727
  · exact B586731
  · exact B586735
  · exact B586739
  · exact B586743
  · exact B586747
  · exact B586751
  · exact B586755
  · exact B586759
  · exact B586763
  · exact B586767
  · exact B586771
  · exact B586775
  · exact B586779
  · exact B586783
  · exact B586787
  · exact B586791
  · exact B586795
  · exact B586799
  · exact B586803
  · exact B586807
  · exact B586811
  · exact B586815
  · exact B586819
  · exact B586823
  · exact B586827
  · exact B586831
  · exact B586835
  · exact B586839
  · exact B586843
  · exact B586847
  · exact B586851
  · exact B586855
  · exact B586859
  · exact B586863
  · exact B586867
  · exact B586871
  · exact B586875
  · exact B586879
  · exact B586883
  · exact B586887
  · exact B586891
  · exact B586895
  · exact B586899
  · exact B586903
  · exact B586907
  · exact B586911
  · exact B586915
  · exact B586919
  · exact B586923
  · exact B586927
  · exact B586931
  · exact B586935
  · exact B586939
  · exact B586943
  · exact B586947
  · exact B586951
  · exact B586955
  · exact B586959
  · exact B586963
  · exact B586967
  · exact B586971
  · exact B586975
  · exact B586979
  · exact B586983
  · exact B586987
  · exact B586991
  · exact B586995
  · exact B586999
  · exact B587003
  · exact B587007
  · exact B587011
  · exact B587015
  · exact B587019
  · exact B587023
  · exact B587027
  · exact B587031
  · exact B587035
  · exact B587039
  · exact B587043
  · exact B587047
  · exact B587051
  · exact B587055
  · exact B587059
  · exact B587063
  · exact B587067
  · exact B587071
  · exact B587075
  · exact B587079
  · exact B587083
  · exact B587087
  · exact B587091
  · exact B587095
  · exact B587099
  · exact B587103
  · exact B587107
  · exact B587111
  · exact B587115
  · exact B587119
  · exact B587123
  · exact B587127
  · exact B587131
  · exact B587135
  · exact B587139
  · exact B587143
  · exact B587147
  · exact B587151
  · exact B587155
  · exact B587159
  · exact B587163
  · exact B587167
  · exact B587171
  · exact B587175
  · exact B587179
  · exact B587183
  · exact B587187
  · exact B587191
  · exact B587195
  · exact B587199
  · exact B587203
  · exact B587207
  · exact B587211
  · exact B587215
  · exact B587219
  · exact B587223
  · exact B587227
  · exact B587231
  · exact B587235
  · exact B587239
  · exact B587243
  · exact B587247
  · exact B587251
  · exact B587255
  · exact B587259
  · exact B587263
  · exact B587267
  · exact B587271
  · exact B587275
  · exact B587279
  · exact B587283
  · exact B587287

theorem solution (m : ℕ) (hlo : 583288 ≤ m) (hhi : m ≤ 587288) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 145822 ≤ j := by omega
    have hj2 : j ≤ 146821 := by omega
    have hb : Blo 583288 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 146522 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
