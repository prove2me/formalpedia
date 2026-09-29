-- Prove2me | solution 1 for syracuse_descends_range_1543469_1545469
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:19.099984+00:00
-- url     : https://prove2.me/submissions/c9811cc3-79a3-41e7-a5ef-b41eeae282fe

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


theorem B2605061 : Blo 1543469 2605061 := bbase (se 4 (by rfl) ⟨244224, by rfl⟩ : syracuseStep 2605061 = 488449) (by norm_num)
theorem B1736725 : Blo 1543469 1736725 := bbase (se 6 (by rfl) ⟨40704, by rfl⟩ : syracuseStep 1736725 = 81409) (by norm_num)
theorem B11722805 : Blo 1543469 11722805 := bbase (se 5 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 11722805 = 1099013) (by norm_num)
theorem B1736761 : Blo 1543469 1736761 := bbase (se 2 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 1736761 = 1302571) (by norm_num)
theorem B1564741 : Blo 1543469 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B3473477 : Blo 1543469 3473477 := bbase (se 4 (by rfl) ⟨325638, by rfl⟩ : syracuseStep 3473477 = 651277) (by norm_num)
theorem B30097493 : Blo 1543469 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B1736797 : Blo 1543469 1736797 := bbase (se 3 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 1736797 = 651299) (by norm_num)
theorem B1736833 : Blo 1543469 1736833 := bbase (se 2 (by rfl) ⟨651312, by rfl⟩ : syracuseStep 1736833 = 1302625) (by norm_num)
theorem B2605189 : Blo 1543469 2605189 := bbase (se 4 (by rfl) ⟨244236, by rfl⟩ : syracuseStep 2605189 = 488473) (by norm_num)
theorem B3473549 : Blo 1543469 3473549 := bbase (se 3 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 3473549 = 1302581) (by norm_num)
theorem B1736869 : Blo 1543469 1736869 := bbase (se 4 (by rfl) ⟨162831, by rfl⟩ : syracuseStep 1736869 = 325663) (by norm_num)
theorem B7815365 : Blo 1543469 7815365 := bbase (se 4 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 7815365 = 1465381) (by norm_num)
theorem B1736905 : Blo 1543469 1736905 := bbase (se 2 (by rfl) ⟨651339, by rfl⟩ : syracuseStep 1736905 = 1302679) (by norm_num)
theorem B3473621 : Blo 1543469 3473621 := bbase (se 7 (by rfl) ⟨40706, by rfl⟩ : syracuseStep 3473621 = 81413) (by norm_num)
theorem B2932949 : Blo 1543469 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B2605277 : Blo 1543469 2605277 := bbase (se 3 (by rfl) ⟨488489, by rfl⟩ : syracuseStep 2605277 = 976979) (by norm_num)
theorem B1736941 : Blo 1543469 1736941 := bbase (se 3 (by rfl) ⟨325676, by rfl⟩ : syracuseStep 1736941 = 651353) (by norm_num)
theorem B1736977 : Blo 1543469 1736977 := bbase (se 2 (by rfl) ⟨651366, by rfl⟩ : syracuseStep 1736977 = 1302733) (by norm_num)
theorem B3473693 : Blo 1543469 3473693 := bbase (se 3 (by rfl) ⟨651317, by rfl⟩ : syracuseStep 3473693 = 1302635) (by norm_num)
theorem B5210405 : Blo 1543469 5210405 := bbase (se 4 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 5210405 = 976951) (by norm_num)
theorem B3907885 : Blo 1543469 3907885 := bbase (se 3 (by rfl) ⟨732728, by rfl⟩ : syracuseStep 3907885 = 1465457) (by norm_num)
theorem B1737013 : Blo 1543469 1737013 := bbase (se 5 (by rfl) ⟨81422, by rfl⟩ : syracuseStep 1737013 = 162845) (by norm_num)
theorem B1737049 : Blo 1543469 1737049 := bbase (se 2 (by rfl) ⟨651393, by rfl⟩ : syracuseStep 1737049 = 1302787) (by norm_num)
theorem B2605405 : Blo 1543469 2605405 := bbase (se 3 (by rfl) ⟨488513, by rfl⟩ : syracuseStep 2605405 = 977027) (by norm_num)
theorem B3473765 : Blo 1543469 3473765 := bbase (se 4 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 3473765 = 651331) (by norm_num)
theorem B2933101 : Blo 1543469 2933101 := bbase (se 3 (by rfl) ⟨549956, by rfl⟩ : syracuseStep 2933101 = 1099913) (by norm_num)
theorem B14098805 : Blo 1543469 14098805 := bbase (se 5 (by rfl) ⟨660881, by rfl⟩ : syracuseStep 14098805 = 1321763) (by norm_num)
theorem B1737085 : Blo 1543469 1737085 := bbase (se 3 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 1737085 = 651407) (by norm_num)
theorem B3907997 : Blo 1543469 3907997 := bbase (se 3 (by rfl) ⟨732749, by rfl⟩ : syracuseStep 3907997 = 1465499) (by norm_num)
theorem B1737121 : Blo 1543469 1737121 := bbase (se 2 (by rfl) ⟨651420, by rfl⟩ : syracuseStep 1737121 = 1302841) (by norm_num)
theorem B3473837 : Blo 1543469 3473837 := bbase (se 3 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 3473837 = 1302689) (by norm_num)
theorem B2605493 : Blo 1543469 2605493 := bbase (se 5 (by rfl) ⟨122132, by rfl⟩ : syracuseStep 2605493 = 244265) (by norm_num)
theorem B4456885 : Blo 1543469 4456885 := bbase (se 5 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 4456885 = 417833) (by norm_num)
theorem B1737157 : Blo 1543469 1737157 := bbase (se 4 (by rfl) ⟨162858, by rfl⟩ : syracuseStep 1737157 = 325717) (by norm_num)
theorem B8028629 : Blo 1543469 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B1737193 : Blo 1543469 1737193 := bbase (se 2 (by rfl) ⟨651447, by rfl⟩ : syracuseStep 1737193 = 1302895) (by norm_num)
theorem B3473909 : Blo 1543469 3473909 := bbase (se 5 (by rfl) ⟨162839, by rfl⟩ : syracuseStep 3473909 = 325679) (by norm_num)
theorem B1737229 : Blo 1543469 1737229 := bbase (se 3 (by rfl) ⟨325730, by rfl⟩ : syracuseStep 1737229 = 651461) (by norm_num)
theorem B1737265 : Blo 1543469 1737265 := bbase (se 2 (by rfl) ⟨651474, by rfl⟩ : syracuseStep 1737265 = 1302949) (by norm_num)
theorem B2605621 : Blo 1543469 2605621 := bbase (se 5 (by rfl) ⟨122138, by rfl⟩ : syracuseStep 2605621 = 244277) (by norm_num)
theorem B3473981 : Blo 1543469 3473981 := bbase (se 3 (by rfl) ⟨651371, by rfl⟩ : syracuseStep 3473981 = 1302743) (by norm_num)
theorem B1737301 : Blo 1543469 1737301 := bbase (se 8 (by rfl) ⟨10179, by rfl⟩ : syracuseStep 1737301 = 20359) (by norm_num)
theorem B21144149 : Blo 1543469 21144149 := bbase (se 8 (by rfl) ⟨123891, by rfl⟩ : syracuseStep 21144149 = 247783) (by norm_num)
theorem B3908189 : Blo 1543469 3908189 := bbase (se 3 (by rfl) ⟨732785, by rfl⟩ : syracuseStep 3908189 = 1465571) (by norm_num)
theorem B1565293 : Blo 1543469 1565293 := bbase (se 3 (by rfl) ⟨293492, by rfl⟩ : syracuseStep 1565293 = 586985) (by norm_num)
theorem B1737337 : Blo 1543469 1737337 := bbase (se 2 (by rfl) ⟨651501, by rfl⟩ : syracuseStep 1737337 = 1303003) (by norm_num)
theorem B3474053 : Blo 1543469 3474053 := bbase (se 4 (by rfl) ⟨325692, by rfl⟩ : syracuseStep 3474053 = 651385) (by norm_num)
theorem B2605709 : Blo 1543469 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B1737373 : Blo 1543469 1737373 := bbase (se 3 (by rfl) ⟨325757, by rfl⟩ : syracuseStep 1737373 = 651515) (by norm_num)
theorem B2933405 : Blo 1543469 2933405 := bbase (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) (by norm_num)
theorem B1737409 : Blo 1543469 1737409 := bbase (se 2 (by rfl) ⟨651528, by rfl⟩ : syracuseStep 1737409 = 1303057) (by norm_num)
theorem B3474125 : Blo 1543469 3474125 := bbase (se 3 (by rfl) ⟨651398, by rfl⟩ : syracuseStep 3474125 = 1302797) (by norm_num)
theorem B5210837 : Blo 1543469 5210837 := bbase (se 7 (by rfl) ⟨61064, by rfl⟩ : syracuseStep 5210837 = 122129) (by norm_num)
theorem B1737445 : Blo 1543469 1737445 := bbase (se 4 (by rfl) ⟨162885, by rfl⟩ : syracuseStep 1737445 = 325771) (by norm_num)
theorem B7045861 : Blo 1543469 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B1737481 : Blo 1543469 1737481 := bbase (se 2 (by rfl) ⟨651555, by rfl⟩ : syracuseStep 1737481 = 1303111) (by norm_num)
theorem B2605837 : Blo 1543469 2605837 := bbase (se 3 (by rfl) ⟨488594, by rfl⟩ : syracuseStep 2605837 = 977189) (by norm_num)
theorem B3474197 : Blo 1543469 3474197 := bbase (se 6 (by rfl) ⟨81426, by rfl⟩ : syracuseStep 3474197 = 162853) (by norm_num)
theorem B1737517 : Blo 1543469 1737517 := bbase (se 3 (by rfl) ⟨325784, by rfl⟩ : syracuseStep 1737517 = 651569) (by norm_num)
theorem B4948789 : Blo 1543469 4948789 := bbase (se 5 (by rfl) ⟨231974, by rfl⟩ : syracuseStep 4948789 = 463949) (by norm_num)
theorem B1737553 : Blo 1543469 1737553 := bbase (se 2 (by rfl) ⟨651582, by rfl⟩ : syracuseStep 1737553 = 1303165) (by norm_num)
theorem B20071253 : Blo 1543469 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B3474269 : Blo 1543469 3474269 := bbase (se 3 (by rfl) ⟨651425, by rfl⟩ : syracuseStep 3474269 = 1302851) (by norm_num)
theorem B2605925 : Blo 1543469 2605925 := bbase (se 4 (by rfl) ⟨244305, by rfl⟩ : syracuseStep 2605925 = 488611) (by norm_num)
theorem B6595445 : Blo 1543469 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B1737589 : Blo 1543469 1737589 := bbase (se 5 (by rfl) ⟨81449, by rfl⟩ : syracuseStep 1737589 = 162899) (by norm_num)
theorem B2007937 : Blo 1543469 2007937 := bbase (se 2 (by rfl) ⟨752976, by rfl⟩ : syracuseStep 2007937 = 1505953) (by norm_num)
theorem B3761045 : Blo 1543469 3761045 := bbase (se 6 (by rfl) ⟨88149, by rfl⟩ : syracuseStep 3761045 = 176299) (by norm_num)
theorem B1737625 : Blo 1543469 1737625 := bbase (se 2 (by rfl) ⟨651609, by rfl⟩ : syracuseStep 1737625 = 1303219) (by norm_num)
theorem B3474341 : Blo 1543469 3474341 := bbase (se 4 (by rfl) ⟨325719, by rfl⟩ : syracuseStep 3474341 = 651439) (by norm_num)
theorem B3908533 : Blo 1543469 3908533 := bbase (se 5 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 3908533 = 366425) (by norm_num)
theorem B1737661 : Blo 1543469 1737661 := bbase (se 3 (by rfl) ⟨325811, by rfl⟩ : syracuseStep 1737661 = 651623) (by norm_num)
theorem B1737697 : Blo 1543469 1737697 := bbase (se 2 (by rfl) ⟨651636, by rfl⟩ : syracuseStep 1737697 = 1303273) (by norm_num)
theorem B2606053 : Blo 1543469 2606053 := bbase (se 4 (by rfl) ⟨244317, by rfl⟩ : syracuseStep 2606053 = 488635) (by norm_num)
theorem B3474413 : Blo 1543469 3474413 := bbase (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) (by norm_num)
theorem B3343357 : Blo 1543469 3343357 := bbase (se 3 (by rfl) ⟨626879, by rfl⟩ : syracuseStep 3343357 = 1253759) (by norm_num)
theorem B1737733 : Blo 1543469 1737733 := bbase (se 4 (by rfl) ⟨162912, by rfl⟩ : syracuseStep 1737733 = 325825) (by norm_num)
theorem B3908645 : Blo 1543469 3908645 := bbase (se 4 (by rfl) ⟨366435, by rfl⟩ : syracuseStep 3908645 = 732871) (by norm_num)
theorem B1737769 : Blo 1543469 1737769 := bbase (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) (by norm_num)
theorem B3474485 : Blo 1543469 3474485 := bbase (se 5 (by rfl) ⟨162866, by rfl⟩ : syracuseStep 3474485 = 325733) (by norm_num)
theorem B2606141 : Blo 1543469 2606141 := bbase (se 3 (by rfl) ⟨488651, by rfl⟩ : syracuseStep 2606141 = 977303) (by norm_num)
theorem B1737805 : Blo 1543469 1737805 := bbase (se 3 (by rfl) ⟨325838, by rfl⟩ : syracuseStep 1737805 = 651677) (by norm_num)
theorem B1737841 : Blo 1543469 1737841 := bbase (se 2 (by rfl) ⟨651690, by rfl⟩ : syracuseStep 1737841 = 1303381) (by norm_num)
theorem B5866613 : Blo 1543469 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B3474557 : Blo 1543469 3474557 := bbase (se 3 (by rfl) ⟨651479, by rfl⟩ : syracuseStep 3474557 = 1302959) (by norm_num)
theorem B5211269 : Blo 1543469 5211269 := bbase (se 4 (by rfl) ⟨488556, by rfl⟩ : syracuseStep 5211269 = 977113) (by norm_num)
theorem B1737877 : Blo 1543469 1737877 := bbase (se 6 (by rfl) ⟨40731, by rfl⟩ : syracuseStep 1737877 = 81463) (by norm_num)
theorem B1737913 : Blo 1543469 1737913 := bbase (se 2 (by rfl) ⟨651717, by rfl⟩ : syracuseStep 1737913 = 1303435) (by norm_num)
theorem B2606269 : Blo 1543469 2606269 := bbase (se 3 (by rfl) ⟨488675, by rfl⟩ : syracuseStep 2606269 = 977351) (by norm_num)
theorem B3474629 : Blo 1543469 3474629 := bbase (se 4 (by rfl) ⟨325746, by rfl⟩ : syracuseStep 3474629 = 651493) (by norm_num)
theorem B1737949 : Blo 1543469 1737949 := bbase (se 3 (by rfl) ⟨325865, by rfl⟩ : syracuseStep 1737949 = 651731) (by norm_num)
theorem B3908837 : Blo 1543469 3908837 := bbase (se 4 (by rfl) ⟨366453, by rfl⟩ : syracuseStep 3908837 = 732907) (by norm_num)
theorem B1737985 : Blo 1543469 1737985 := bbase (se 2 (by rfl) ⟨651744, by rfl⟩ : syracuseStep 1737985 = 1303489) (by norm_num)
theorem B3474701 : Blo 1543469 3474701 := bbase (se 3 (by rfl) ⟨651506, by rfl⟩ : syracuseStep 3474701 = 1303013) (by norm_num)
theorem B2606357 : Blo 1543469 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B1738021 : Blo 1543469 1738021 := bbase (se 4 (by rfl) ⟨162939, by rfl⟩ : syracuseStep 1738021 = 325879) (by norm_num)
theorem B2475317 : Blo 1543469 2475317 := bbase (se 5 (by rfl) ⟨116030, by rfl⟩ : syracuseStep 2475317 = 232061) (by norm_num)
theorem B3343685 : Blo 1543469 3343685 := bbase (se 4 (by rfl) ⟨313470, by rfl⟩ : syracuseStep 3343685 = 626941) (by norm_num)
theorem B1738057 : Blo 1543469 1738057 := bbase (se 2 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 1738057 = 1303543) (by norm_num)
theorem B3474773 : Blo 1543469 3474773 := bbase (se 12 (by rfl) ⟨1272, by rfl⟩ : syracuseStep 3474773 = 2545) (by norm_num)
theorem B1738093 : Blo 1543469 1738093 := bbase (se 3 (by rfl) ⟨325892, by rfl⟩ : syracuseStep 1738093 = 651785) (by norm_num)
theorem B1738129 : Blo 1543469 1738129 := bbase (se 2 (by rfl) ⟨651798, by rfl⟩ : syracuseStep 1738129 = 1303597) (by norm_num)
theorem B2606485 : Blo 1543469 2606485 := bbase (se 6 (by rfl) ⟨61089, by rfl⟩ : syracuseStep 2606485 = 122179) (by norm_num)
theorem B5866901 : Blo 1543469 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B3474845 : Blo 1543469 3474845 := bbase (se 3 (by rfl) ⟨651533, by rfl⟩ : syracuseStep 3474845 = 1303067) (by norm_num)
theorem B7423397 : Blo 1543469 7423397 := bbase (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) (by norm_num)
theorem B2860469 : Blo 1543469 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1738165 : Blo 1543469 1738165 := bbase (se 5 (by rfl) ⟨81476, by rfl⟩ : syracuseStep 1738165 = 162953) (by norm_num)
theorem B2475445 : Blo 1543469 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B7816661 : Blo 1543469 7816661 := bbase (se 7 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 7816661 = 183203) (by norm_num)
theorem B1738201 : Blo 1543469 1738201 := bbase (se 2 (by rfl) ⟨651825, by rfl⟩ : syracuseStep 1738201 = 1303651) (by norm_num)
theorem B3474917 : Blo 1543469 3474917 := bbase (se 4 (by rfl) ⟨325773, by rfl⟩ : syracuseStep 3474917 = 651547) (by norm_num)
theorem B2606573 : Blo 1543469 2606573 := bbase (se 3 (by rfl) ⟨488732, by rfl⟩ : syracuseStep 2606573 = 977465) (by norm_num)
theorem B1738237 : Blo 1543469 1738237 := bbase (se 3 (by rfl) ⟨325919, by rfl⟩ : syracuseStep 1738237 = 651839) (by norm_num)
theorem B1738273 : Blo 1543469 1738273 := bbase (se 2 (by rfl) ⟨651852, by rfl⟩ : syracuseStep 1738273 = 1303705) (by norm_num)
theorem B3474989 : Blo 1543469 3474989 := bbase (se 3 (by rfl) ⟨651560, by rfl⟩ : syracuseStep 3474989 = 1303121) (by norm_num)
theorem B12518965 : Blo 1543469 12518965 := bbase (se 5 (by rfl) ⟨586826, by rfl⟩ : syracuseStep 12518965 = 1173653) (by norm_num)
theorem B5211701 : Blo 1543469 5211701 := bbase (se 5 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 5211701 = 488597) (by norm_num)
theorem B3909181 : Blo 1543469 3909181 := bbase (se 3 (by rfl) ⟨732971, by rfl⟩ : syracuseStep 3909181 = 1465943) (by norm_num)
theorem B4458053 : Blo 1543469 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B1738309 : Blo 1543469 1738309 := bbase (se 4 (by rfl) ⟨162966, by rfl⟩ : syracuseStep 1738309 = 325933) (by norm_num)
theorem B1738345 : Blo 1543469 1738345 := bbase (se 2 (by rfl) ⟨651879, by rfl⟩ : syracuseStep 1738345 = 1303759) (by norm_num)
theorem B2606701 : Blo 1543469 2606701 := bbase (se 3 (by rfl) ⟨488756, by rfl⟩ : syracuseStep 2606701 = 977513) (by norm_num)
theorem B3475061 : Blo 1543469 3475061 := bbase (se 5 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 3475061 = 325787) (by norm_num)
theorem B1738381 : Blo 1543469 1738381 := bbase (se 3 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 1738381 = 651893) (by norm_num)
theorem B1672849 : Blo 1543469 1672849 := bbase (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) (by norm_num)
theorem B3909293 : Blo 1543469 3909293 := bbase (se 3 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 3909293 = 1465985) (by norm_num)
theorem B1738417 : Blo 1543469 1738417 := bbase (se 2 (by rfl) ⟨651906, by rfl⟩ : syracuseStep 1738417 = 1303813) (by norm_num)
theorem B3475133 : Blo 1543469 3475133 := bbase (se 3 (by rfl) ⟨651587, by rfl⟩ : syracuseStep 3475133 = 1303175) (by norm_num)
theorem B2606789 : Blo 1543469 2606789 := bbase (se 4 (by rfl) ⟨244386, by rfl⟩ : syracuseStep 2606789 = 488773) (by norm_num)
theorem B4400837 : Blo 1543469 4400837 := bbase (se 4 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 4400837 = 825157) (by norm_num)
theorem B8914645 : Blo 1543469 8914645 := bbase (se 7 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 8914645 = 208937) (by norm_num)
theorem B1738453 : Blo 1543469 1738453 := bbase (se 7 (by rfl) ⟨20372, by rfl⟩ : syracuseStep 1738453 = 40745) (by norm_num)
theorem B1648345 : Blo 1543469 1648345 := bbase (se 2 (by rfl) ⟨618129, by rfl⟩ : syracuseStep 1648345 = 1236259) (by norm_num)
theorem B1738489 : Blo 1543469 1738489 := bbase (se 2 (by rfl) ⟨651933, by rfl⟩ : syracuseStep 1738489 = 1303867) (by norm_num)
theorem B3475205 : Blo 1543469 3475205 := bbase (se 4 (by rfl) ⟨325800, by rfl⟩ : syracuseStep 3475205 = 651601) (by norm_num)
theorem B1566469 : Blo 1543469 1566469 := bbase (se 4 (by rfl) ⟨146856, by rfl⟩ : syracuseStep 1566469 = 293713) (by norm_num)
theorem B15255317 : Blo 1543469 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B1738525 : Blo 1543469 1738525 := bbase (se 3 (by rfl) ⟨325973, by rfl⟩ : syracuseStep 1738525 = 651947) (by norm_num)
theorem B1738561 : Blo 1543469 1738561 := bbase (se 2 (by rfl) ⟨651960, by rfl⟩ : syracuseStep 1738561 = 1303921) (by norm_num)
theorem B2606917 : Blo 1543469 2606917 := bbase (se 4 (by rfl) ⟨244398, by rfl⟩ : syracuseStep 2606917 = 488797) (by norm_num)
theorem B3475277 : Blo 1543469 3475277 := bbase (se 3 (by rfl) ⟨651614, by rfl⟩ : syracuseStep 3475277 = 1303229) (by norm_num)
theorem B6596437 : Blo 1543469 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B1738597 : Blo 1543469 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B3909485 : Blo 1543469 3909485 := bbase (se 3 (by rfl) ⟨733028, by rfl⟩ : syracuseStep 3909485 = 1466057) (by norm_num)
theorem B1738633 : Blo 1543469 1738633 := bbase (se 2 (by rfl) ⟨651987, by rfl⟩ : syracuseStep 1738633 = 1303975) (by norm_num)
theorem B3475349 : Blo 1543469 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B2607005 : Blo 1543469 2607005 := bbase (se 3 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 2607005 = 977627) (by norm_num)
theorem B3475421 : Blo 1543469 3475421 := bbase (se 3 (by rfl) ⟨651641, by rfl⟩ : syracuseStep 3475421 = 1303283) (by norm_num)
theorem B5564389 : Blo 1543469 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B5212133 : Blo 1543469 5212133 := bbase (se 4 (by rfl) ⟨488637, by rfl⟩ : syracuseStep 5212133 = 977275) (by norm_num)
theorem B7047173 : Blo 1543469 7047173 := bbase (se 4 (by rfl) ⟨660672, by rfl⟩ : syracuseStep 7047173 = 1321345) (by norm_num)
theorem B2607133 : Blo 1543469 2607133 := bbase (se 3 (by rfl) ⟨488837, by rfl⟩ : syracuseStep 2607133 = 977675) (by norm_num)
theorem B3475493 : Blo 1543469 3475493 := bbase (se 4 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 3475493 = 651655) (by norm_num)
theorem B1648721 : Blo 1543469 1648721 := bbase (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) (by norm_num)
theorem B3475565 : Blo 1543469 3475565 := bbase (se 3 (by rfl) ⟨651668, by rfl⟩ : syracuseStep 3475565 = 1303337) (by norm_num)
theorem B2607221 : Blo 1543469 2607221 := bbase (se 5 (by rfl) ⟨122213, by rfl⟩ : syracuseStep 2607221 = 244427) (by norm_num)
theorem B11126933 : Blo 1543469 11126933 := bbase (se 6 (by rfl) ⟨260787, by rfl⟩ : syracuseStep 11126933 = 521575) (by norm_num)
theorem B1648793 : Blo 1543469 1648793 := bbase (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) (by norm_num)
theorem B3475637 : Blo 1543469 3475637 := bbase (se 5 (by rfl) ⟨162920, by rfl⟩ : syracuseStep 3475637 = 325841) (by norm_num)
theorem B3909829 : Blo 1543469 3909829 := bbase (se 4 (by rfl) ⟨366546, by rfl⟩ : syracuseStep 3909829 = 733093) (by norm_num)
theorem B2607349 : Blo 1543469 2607349 := bbase (se 5 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 2607349 = 244439) (by norm_num)
theorem B3475709 : Blo 1543469 3475709 := bbase (se 3 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 3475709 = 1303391) (by norm_num)
theorem B3909941 : Blo 1543469 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B3475781 : Blo 1543469 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B3344717 : Blo 1543469 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B2607437 : Blo 1543469 2607437 := bbase (se 3 (by rfl) ⟨488894, by rfl⟩ : syracuseStep 2607437 = 977789) (by norm_num)
theorem B1648981 : Blo 1543469 1648981 := bbase (se 10 (by rfl) ⟨2415, by rfl⟩ : syracuseStep 1648981 = 4831) (by norm_num)
theorem B2197901 : Blo 1543469 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B3475853 : Blo 1543469 3475853 := bbase (se 3 (by rfl) ⟨651722, by rfl⟩ : syracuseStep 3475853 = 1303445) (by norm_num)
theorem B5212565 : Blo 1543469 5212565 := bbase (se 6 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 5212565 = 244339) (by norm_num)
theorem B2607565 : Blo 1543469 2607565 := bbase (se 3 (by rfl) ⟨488918, by rfl⟩ : syracuseStep 2607565 = 977837) (by norm_num)
theorem B3475925 : Blo 1543469 3475925 := bbase (se 7 (by rfl) ⟨40733, by rfl⟩ : syracuseStep 3475925 = 81467) (by norm_num)
theorem B3910133 : Blo 1543469 3910133 := bbase (se 5 (by rfl) ⟨183287, by rfl⟩ : syracuseStep 3910133 = 366575) (by norm_num)
theorem B1649165 : Blo 1543469 1649165 := bbase (se 3 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 1649165 = 618437) (by norm_num)
theorem B3475997 : Blo 1543469 3475997 := bbase (se 3 (by rfl) ⟨651749, by rfl⟩ : syracuseStep 3475997 = 1303499) (by norm_num)
theorem B2607653 : Blo 1543469 2607653 := bbase (se 4 (by rfl) ⟨244467, by rfl⟩ : syracuseStep 2607653 = 488935) (by norm_num)
theorem B3476069 : Blo 1543469 3476069 := bbase (se 4 (by rfl) ⟨325881, by rfl⟩ : syracuseStep 3476069 = 651763) (by norm_num)
theorem B2607781 : Blo 1543469 2607781 := bbase (se 4 (by rfl) ⟨244479, by rfl⟩ : syracuseStep 2607781 = 488959) (by norm_num)
theorem B3476141 : Blo 1543469 3476141 := bbase (se 3 (by rfl) ⟨651776, by rfl⟩ : syracuseStep 3476141 = 1303553) (by norm_num)
theorem B7817957 : Blo 1543469 7817957 := bbase (se 4 (by rfl) ⟨732933, by rfl⟩ : syracuseStep 7817957 = 1465867) (by norm_num)
theorem B3476213 : Blo 1543469 3476213 := bbase (se 5 (by rfl) ⟨162947, by rfl⟩ : syracuseStep 3476213 = 325895) (by norm_num)
theorem B2607869 : Blo 1543469 2607869 := bbase (se 3 (by rfl) ⟨488975, by rfl⟩ : syracuseStep 2607869 = 977951) (by norm_num)
theorem B3476285 : Blo 1543469 3476285 := bbase (se 3 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 3476285 = 1303607) (by norm_num)
theorem B5212997 : Blo 1543469 5212997 := bbase (se 4 (by rfl) ⟨488718, by rfl⟩ : syracuseStep 5212997 = 977437) (by norm_num)
theorem B3910477 : Blo 1543469 3910477 := bbase (se 3 (by rfl) ⟨733214, by rfl⟩ : syracuseStep 3910477 = 1466429) (by norm_num)
theorem B21146453 : Blo 1543469 21146453 := bbase (se 9 (by rfl) ⟨61952, by rfl⟩ : syracuseStep 21146453 = 123905) (by norm_num)
theorem B3476357 : Blo 1543469 3476357 := bbase (se 4 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 3476357 = 651817) (by norm_num)
theorem B3910589 : Blo 1543469 3910589 := bbase (se 3 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 3910589 = 1466471) (by norm_num)
theorem B3476429 : Blo 1543469 3476429 := bbase (se 3 (by rfl) ⟨651830, by rfl⟩ : syracuseStep 3476429 = 1303661) (by norm_num)
theorem B3476501 : Blo 1543469 3476501 := bbase (se 6 (by rfl) ⟨81480, by rfl⟩ : syracuseStep 3476501 = 162961) (by norm_num)
theorem B3476573 : Blo 1543469 3476573 := bbase (se 3 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 3476573 = 1303715) (by norm_num)
theorem B3132533 : Blo 1543469 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B3910781 : Blo 1543469 3910781 := bbase (se 3 (by rfl) ⟨733271, by rfl⟩ : syracuseStep 3910781 = 1466543) (by norm_num)
theorem B3476645 : Blo 1543469 3476645 := bbase (se 4 (by rfl) ⟨325935, by rfl⟩ : syracuseStep 3476645 = 651871) (by norm_num)
theorem B3476717 : Blo 1543469 3476717 := bbase (se 3 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 3476717 = 1303769) (by norm_num)
theorem B5213429 : Blo 1543469 5213429 := bbase (se 5 (by rfl) ⟨244379, by rfl⟩ : syracuseStep 5213429 = 488759) (by norm_num)
theorem B1649917 : Blo 1543469 1649917 := bbase (se 3 (by rfl) ⟨309359, by rfl⟩ : syracuseStep 1649917 = 618719) (by norm_num)
theorem B5860613 : Blo 1543469 5860613 := bbase (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) (by norm_num)
theorem B7417109 : Blo 1543469 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B12520757 : Blo 1543469 12520757 := bbase (se 5 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 12520757 = 1173821) (by norm_num)
theorem B3476789 : Blo 1543469 3476789 := bbase (se 5 (by rfl) ⟨162974, by rfl⟩ : syracuseStep 3476789 = 325949) (by norm_num)
theorem B1649989 : Blo 1543469 1649989 := bbase (se 4 (by rfl) ⟨154686, by rfl⟩ : syracuseStep 1649989 = 309373) (by norm_num)
theorem B3296629 : Blo 1543469 3296629 := bbase (se 5 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 3296629 = 309059) (by norm_num)
theorem B7048565 : Blo 1543469 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B3476861 : Blo 1543469 3476861 := bbase (se 3 (by rfl) ⟨651911, by rfl⟩ : syracuseStep 3476861 = 1303823) (by norm_num)
theorem B3476933 : Blo 1543469 3476933 := bbase (se 4 (by rfl) ⟨325962, by rfl⟩ : syracuseStep 3476933 = 651925) (by norm_num)
theorem B28184021 : Blo 1543469 28184021 := bbase (se 7 (by rfl) ⟨330281, by rfl⟩ : syracuseStep 28184021 = 660563) (by norm_num)
theorem B3911125 : Blo 1543469 3911125 := bbase (se 7 (by rfl) ⟨45833, by rfl⟩ : syracuseStep 3911125 = 91667) (by norm_num)
theorem B2715125 : Blo 1543469 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B1650169 : Blo 1543469 1650169 := bbase (se 2 (by rfl) ⟨618813, by rfl⟩ : syracuseStep 1650169 = 1237627) (by norm_num)
theorem B3477005 : Blo 1543469 3477005 := bbase (se 3 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 3477005 = 1303877) (by norm_num)
theorem B3911237 : Blo 1543469 3911237 := bbase (se 4 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 3911237 = 733357) (by norm_num)
theorem B3477077 : Blo 1543469 3477077 := bbase (se 8 (by rfl) ⟨20373, by rfl⟩ : syracuseStep 3477077 = 40747) (by norm_num)
theorem B6262373 : Blo 1543469 6262373 := bbase (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) (by norm_num)
theorem B3477149 : Blo 1543469 3477149 := bbase (se 3 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 3477149 = 1303931) (by norm_num)
theorem B5213861 : Blo 1543469 5213861 := bbase (se 4 (by rfl) ⟨488799, by rfl⟩ : syracuseStep 5213861 = 977599) (by norm_num)
theorem B1855157 : Blo 1543469 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1855181 : Blo 1543469 1855181 := bbase (se 3 (by rfl) ⟨347846, by rfl⟩ : syracuseStep 1855181 = 695693) (by norm_num)
theorem B1953497 : Blo 1543469 1953497 := bbase (se 2 (by rfl) ⟨732561, by rfl⟩ : syracuseStep 1953497 = 1465123) (by norm_num)
theorem B3477221 : Blo 1543469 3477221 := bbase (se 4 (by rfl) ⟨325989, by rfl⟩ : syracuseStep 3477221 = 651979) (by norm_num)
theorem B3911429 : Blo 1543469 3911429 := bbase (se 4 (by rfl) ⟨366696, by rfl⟩ : syracuseStep 3911429 = 733393) (by norm_num)
theorem B1953553 : Blo 1543469 1953553 := bbase (se 2 (by rfl) ⟨732582, by rfl⟩ : syracuseStep 1953553 = 1465165) (by norm_num)
theorem B2199325 : Blo 1543469 2199325 := bbase (se 3 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 2199325 = 824747) (by norm_num)
theorem B3477293 : Blo 1543469 3477293 := bbase (se 3 (by rfl) ⟨651992, by rfl⟩ : syracuseStep 3477293 = 1303985) (by norm_num)
theorem B3297125 : Blo 1543469 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B1953649 : Blo 1543469 1953649 := bbase (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) (by norm_num)
theorem B13193077 : Blo 1543469 13193077 := bbase (se 5 (by rfl) ⟨618425, by rfl⟩ : syracuseStep 13193077 = 1236851) (by norm_num)
theorem B16691093 : Blo 1543469 16691093 := bbase (se 6 (by rfl) ⟨391197, by rfl⟩ : syracuseStep 16691093 = 782395) (by norm_num)
theorem B9891733 : Blo 1543469 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B7819253 : Blo 1543469 7819253 := bbase (se 5 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 7819253 = 733055) (by norm_num)
theorem B6688757 : Blo 1543469 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1855489 : Blo 1543469 1855489 := bbase (se 2 (by rfl) ⟨695808, by rfl⟩ : syracuseStep 1855489 = 1391617) (by norm_num)
theorem B1953821 : Blo 1543469 1953821 := bbase (se 3 (by rfl) ⟨366341, by rfl⟩ : syracuseStep 1953821 = 732683) (by norm_num)
theorem B1953877 : Blo 1543469 1953877 := bbase (se 8 (by rfl) ⟨11448, by rfl⟩ : syracuseStep 1953877 = 22897) (by norm_num)
theorem B5214293 : Blo 1543469 5214293 := bbase (se 8 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 5214293 = 61105) (by norm_num)
theorem B3911773 : Blo 1543469 3911773 := bbase (se 3 (by rfl) ⟨733457, by rfl⟩ : syracuseStep 3911773 = 1466915) (by norm_num)
theorem B7426181 : Blo 1543469 7426181 := bbase (se 4 (by rfl) ⟨696204, by rfl⟩ : syracuseStep 7426181 = 1392409) (by norm_num)
theorem B1855661 : Blo 1543469 1855661 := bbase (se 3 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 1855661 = 695873) (by norm_num)
theorem B1953973 : Blo 1543469 1953973 := bbase (se 5 (by rfl) ⟨91592, by rfl⟩ : syracuseStep 1953973 = 183185) (by norm_num)
theorem B3911885 : Blo 1543469 3911885 := bbase (se 3 (by rfl) ⟨733478, by rfl⟩ : syracuseStep 3911885 = 1466957) (by norm_num)
theorem B1855777 : Blo 1543469 1855777 := bbase (se 2 (by rfl) ⟨695916, by rfl⟩ : syracuseStep 1855777 = 1391833) (by norm_num)
theorem B2642213 : Blo 1543469 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B1954145 : Blo 1543469 1954145 := bbase (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) (by norm_num)
theorem B2199917 : Blo 1543469 2199917 := bbase (se 3 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 2199917 = 824969) (by norm_num)
theorem B1855873 : Blo 1543469 1855873 := bbase (se 2 (by rfl) ⟨695952, by rfl⟩ : syracuseStep 1855873 = 1391905) (by norm_num)
theorem B2781589 : Blo 1543469 2781589 := bbase (se 6 (by rfl) ⟨65193, by rfl⟩ : syracuseStep 2781589 = 130387) (by norm_num)
theorem B1954201 : Blo 1543469 1954201 := bbase (se 2 (by rfl) ⟨732825, by rfl⟩ : syracuseStep 1954201 = 1465651) (by norm_num)
theorem B2347429 : Blo 1543469 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B2199997 : Blo 1543469 2199997 := bbase (se 3 (by rfl) ⟨412499, by rfl⟩ : syracuseStep 2199997 = 824999) (by norm_num)
theorem B2781677 : Blo 1543469 2781677 := bbase (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) (by norm_num)
theorem B1954297 : Blo 1543469 1954297 := bbase (se 2 (by rfl) ⟨732861, by rfl⟩ : syracuseStep 1954297 = 1465723) (by norm_num)
theorem B5214725 : Blo 1543469 5214725 := bbase (se 4 (by rfl) ⟨488880, by rfl⟩ : syracuseStep 5214725 = 977761) (by norm_num)
theorem B1856017 : Blo 1543469 1856017 := bbase (se 2 (by rfl) ⟨696006, by rfl⟩ : syracuseStep 1856017 = 1392013) (by norm_num)
theorem B2200117 : Blo 1543469 2200117 := bbase (se 5 (by rfl) ⟨103130, by rfl⟩ : syracuseStep 2200117 = 206261) (by norm_num)
theorem B2200213 : Blo 1543469 2200213 := bbase (se 6 (by rfl) ⟨51567, by rfl⟩ : syracuseStep 2200213 = 103135) (by norm_num)
theorem B1954469 : Blo 1543469 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B3297989 : Blo 1543469 3297989 := bbase (se 4 (by rfl) ⟨309186, by rfl⟩ : syracuseStep 3297989 = 618373) (by norm_num)
theorem B1954525 : Blo 1543469 1954525 := bbase (se 3 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 1954525 = 732947) (by norm_num)
theorem B2781965 : Blo 1543469 2781965 := bbase (se 3 (by rfl) ⟨521618, by rfl⟩ : syracuseStep 2781965 = 1043237) (by norm_num)
theorem B1954621 : Blo 1543469 1954621 := bbase (se 3 (by rfl) ⟨366491, by rfl⟩ : syracuseStep 1954621 = 732983) (by norm_num)
theorem B3298133 : Blo 1543469 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B5215157 : Blo 1543469 5215157 := bbase (se 5 (by rfl) ⟨244460, by rfl⟩ : syracuseStep 5215157 = 488921) (by norm_num)
theorem B2315213 : Blo 1543469 2315213 := bbase (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) (by norm_num)
theorem B12530645 : Blo 1543469 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B2315237 : Blo 1543469 2315237 := bbase (se 4 (by rfl) ⟨217053, by rfl⟩ : syracuseStep 2315237 = 434107) (by norm_num)
theorem B2782181 : Blo 1543469 2782181 := bbase (se 4 (by rfl) ⟨260829, by rfl⟩ : syracuseStep 2782181 = 521659) (by norm_num)
theorem B1954793 : Blo 1543469 1954793 := bbase (se 2 (by rfl) ⟨733047, by rfl⟩ : syracuseStep 1954793 = 1466095) (by norm_num)
theorem B2315261 : Blo 1543469 2315261 := bbase (se 3 (by rfl) ⟨434111, by rfl⟩ : syracuseStep 2315261 = 868223) (by norm_num)
theorem B2315285 : Blo 1543469 2315285 := bbase (se 6 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 2315285 = 108529) (by norm_num)
theorem B1954849 : Blo 1543469 1954849 := bbase (se 2 (by rfl) ⟨733068, by rfl⟩ : syracuseStep 1954849 = 1466137) (by norm_num)
theorem B2315309 : Blo 1543469 2315309 := bbase (se 3 (by rfl) ⟨434120, by rfl⟩ : syracuseStep 2315309 = 868241) (by norm_num)
theorem B2315333 : Blo 1543469 2315333 := bbase (se 4 (by rfl) ⟨217062, by rfl⟩ : syracuseStep 2315333 = 434125) (by norm_num)
theorem B2315357 : Blo 1543469 2315357 := bbase (se 3 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 2315357 = 868259) (by norm_num)
theorem B4396133 : Blo 1543469 4396133 := bbase (se 4 (by rfl) ⟨412137, by rfl⟩ : syracuseStep 4396133 = 824275) (by norm_num)
theorem B2315381 : Blo 1543469 2315381 := bbase (se 5 (by rfl) ⟨108533, by rfl⟩ : syracuseStep 2315381 = 217067) (by norm_num)
theorem B1954945 : Blo 1543469 1954945 := bbase (se 2 (by rfl) ⟨733104, by rfl⟩ : syracuseStep 1954945 = 1466209) (by norm_num)
theorem B2315405 : Blo 1543469 2315405 := bbase (se 3 (by rfl) ⟨434138, by rfl⟩ : syracuseStep 2315405 = 868277) (by norm_num)
theorem B2315429 : Blo 1543469 2315429 := bbase (se 4 (by rfl) ⟨217071, by rfl⟩ : syracuseStep 2315429 = 434143) (by norm_num)
theorem B2315453 : Blo 1543469 2315453 := bbase (se 3 (by rfl) ⟨434147, by rfl⟩ : syracuseStep 2315453 = 868295) (by norm_num)
theorem B2315477 : Blo 1543469 2315477 := bbase (se 7 (by rfl) ⟨27134, by rfl⟩ : syracuseStep 2315477 = 54269) (by norm_num)
theorem B2315501 : Blo 1543469 2315501 := bbase (se 3 (by rfl) ⟨434156, by rfl⟩ : syracuseStep 2315501 = 868313) (by norm_num)
theorem B2315525 : Blo 1543469 2315525 := bbase (se 4 (by rfl) ⟨217080, by rfl⟩ : syracuseStep 2315525 = 434161) (by norm_num)
theorem B7820549 : Blo 1543469 7820549 := bbase (se 4 (by rfl) ⟨733176, by rfl⟩ : syracuseStep 7820549 = 1466353) (by norm_num)
theorem B2315549 : Blo 1543469 2315549 := bbase (se 3 (by rfl) ⟨434165, by rfl⟩ : syracuseStep 2315549 = 868331) (by norm_num)
theorem B1955117 : Blo 1543469 1955117 := bbase (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) (by norm_num)
theorem B2315573 : Blo 1543469 2315573 := bbase (se 5 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 2315573 = 217085) (by norm_num)
theorem B5862725 : Blo 1543469 5862725 := bbase (se 4 (by rfl) ⟨549630, by rfl⟩ : syracuseStep 5862725 = 1099261) (by norm_num)
theorem B2315597 : Blo 1543469 2315597 := bbase (se 3 (by rfl) ⟨434174, by rfl⟩ : syracuseStep 2315597 = 868349) (by norm_num)
theorem B17593685 : Blo 1543469 17593685 := bbase (se 13 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 17593685 = 6443) (by norm_num)
theorem B14849365 : Blo 1543469 14849365 := bbase (se 14 (by rfl) ⟨1359, by rfl⟩ : syracuseStep 14849365 = 2719) (by norm_num)
theorem B2315621 : Blo 1543469 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B1955173 : Blo 1543469 1955173 := bbase (se 4 (by rfl) ⟨183297, by rfl⟩ : syracuseStep 1955173 = 366595) (by norm_num)
theorem B5215589 : Blo 1543469 5215589 := bbase (se 4 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 5215589 = 977923) (by norm_num)
theorem B2315645 : Blo 1543469 2315645 := bbase (se 3 (by rfl) ⟨434183, by rfl⟩ : syracuseStep 2315645 = 868367) (by norm_num)
theorem B2315669 : Blo 1543469 2315669 := bbase (se 6 (by rfl) ⟨54273, by rfl⟩ : syracuseStep 2315669 = 108547) (by norm_num)
theorem B2315693 : Blo 1543469 2315693 := bbase (se 3 (by rfl) ⟨434192, by rfl⟩ : syracuseStep 2315693 = 868385) (by norm_num)
theorem B2315717 : Blo 1543469 2315717 := bbase (se 4 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 2315717 = 434197) (by norm_num)
theorem B1955269 : Blo 1543469 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B2315741 : Blo 1543469 2315741 := bbase (se 3 (by rfl) ⟨434201, by rfl⟩ : syracuseStep 2315741 = 868403) (by norm_num)
theorem B2315765 : Blo 1543469 2315765 := bbase (se 5 (by rfl) ⟨108551, by rfl⟩ : syracuseStep 2315765 = 217103) (by norm_num)
theorem B2315789 : Blo 1543469 2315789 := bbase (se 3 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 2315789 = 868421) (by norm_num)
theorem B4945445 : Blo 1543469 4945445 := bbase (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) (by norm_num)
theorem B2315813 : Blo 1543469 2315813 := bbase (se 4 (by rfl) ⟨217107, by rfl⟩ : syracuseStep 2315813 = 434215) (by norm_num)
theorem B2315837 : Blo 1543469 2315837 := bbase (se 3 (by rfl) ⟨434219, by rfl⟩ : syracuseStep 2315837 = 868439) (by norm_num)
theorem B3298877 : Blo 1543469 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B2315861 : Blo 1543469 2315861 := bbase (se 8 (by rfl) ⟨13569, by rfl⟩ : syracuseStep 2315861 = 27139) (by norm_num)
theorem B2930269 : Blo 1543469 2930269 := bbase (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) (by norm_num)
theorem B3708517 : Blo 1543469 3708517 := bbase (se 4 (by rfl) ⟨347673, by rfl⟩ : syracuseStep 3708517 = 695347) (by norm_num)
theorem B5863013 : Blo 1543469 5863013 := bbase (se 4 (by rfl) ⟨549657, by rfl⟩ : syracuseStep 5863013 = 1099315) (by norm_num)
theorem B2315885 : Blo 1543469 2315885 := bbase (se 3 (by rfl) ⟨434228, by rfl⟩ : syracuseStep 2315885 = 868457) (by norm_num)
theorem B1955441 : Blo 1543469 1955441 := bbase (se 2 (by rfl) ⟨733290, by rfl⟩ : syracuseStep 1955441 = 1466581) (by norm_num)
theorem B2315909 : Blo 1543469 2315909 := bbase (se 4 (by rfl) ⟨217116, by rfl⟩ : syracuseStep 2315909 = 434233) (by norm_num)
theorem B2315933 : Blo 1543469 2315933 := bbase (se 3 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 2315933 = 868475) (by norm_num)
theorem B1955497 : Blo 1543469 1955497 := bbase (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) (by norm_num)
theorem B2315957 : Blo 1543469 2315957 := bbase (se 5 (by rfl) ⟨108560, by rfl⟩ : syracuseStep 2315957 = 217121) (by norm_num)
theorem B2315981 : Blo 1543469 2315981 := bbase (se 3 (by rfl) ⟨434246, by rfl⟩ : syracuseStep 2315981 = 868493) (by norm_num)
theorem B2316005 : Blo 1543469 2316005 := bbase (se 4 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 2316005 = 434251) (by norm_num)
theorem B2930413 : Blo 1543469 2930413 := bbase (se 3 (by rfl) ⟨549452, by rfl⟩ : syracuseStep 2930413 = 1098905) (by norm_num)
theorem B2316029 : Blo 1543469 2316029 := bbase (se 3 (by rfl) ⟨434255, by rfl⟩ : syracuseStep 2316029 = 868511) (by norm_num)
theorem B4396805 : Blo 1543469 4396805 := bbase (se 4 (by rfl) ⟨412200, by rfl⟩ : syracuseStep 4396805 = 824401) (by norm_num)
theorem B1955593 : Blo 1543469 1955593 := bbase (se 2 (by rfl) ⟨733347, by rfl⟩ : syracuseStep 1955593 = 1466695) (by norm_num)
theorem B1980181 : Blo 1543469 1980181 := bbase (se 6 (by rfl) ⟨46410, by rfl⟩ : syracuseStep 1980181 = 92821) (by norm_num)
theorem B2316053 : Blo 1543469 2316053 := bbase (se 6 (by rfl) ⟨54282, by rfl⟩ : syracuseStep 2316053 = 108565) (by norm_num)
theorem B2316077 : Blo 1543469 2316077 := bbase (se 3 (by rfl) ⟨434264, by rfl⟩ : syracuseStep 2316077 = 868529) (by norm_num)
theorem B13195061 : Blo 1543469 13195061 := bbase (se 5 (by rfl) ⟨618518, by rfl⟩ : syracuseStep 13195061 = 1237037) (by norm_num)
theorem B2316101 : Blo 1543469 2316101 := bbase (se 4 (by rfl) ⟨217134, by rfl⟩ : syracuseStep 2316101 = 434269) (by norm_num)
theorem B2316125 : Blo 1543469 2316125 := bbase (se 3 (by rfl) ⟨434273, by rfl⟩ : syracuseStep 2316125 = 868547) (by norm_num)
theorem B2316149 : Blo 1543469 2316149 := bbase (se 5 (by rfl) ⟨108569, by rfl⟩ : syracuseStep 2316149 = 217139) (by norm_num)
theorem B2930573 : Blo 1543469 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B2316173 : Blo 1543469 2316173 := bbase (se 3 (by rfl) ⟨434282, by rfl⟩ : syracuseStep 2316173 = 868565) (by norm_num)
theorem B2783117 : Blo 1543469 2783117 := bbase (se 3 (by rfl) ⟨521834, by rfl⟩ : syracuseStep 2783117 = 1043669) (by norm_num)
theorem B2316197 : Blo 1543469 2316197 := bbase (se 4 (by rfl) ⟨217143, by rfl⟩ : syracuseStep 2316197 = 434287) (by norm_num)
theorem B1955765 : Blo 1543469 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B2316221 : Blo 1543469 2316221 := bbase (se 3 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 2316221 = 868583) (by norm_num)
theorem B2316245 : Blo 1543469 2316245 := bbase (se 7 (by rfl) ⟨27143, by rfl⟩ : syracuseStep 2316245 = 54287) (by norm_num)
theorem B2783197 : Blo 1543469 2783197 := bbase (se 3 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 2783197 = 1043699) (by norm_num)
theorem B2316269 : Blo 1543469 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B1955821 : Blo 1543469 1955821 := bbase (se 3 (by rfl) ⟨366716, by rfl⟩ : syracuseStep 1955821 = 733433) (by norm_num)
theorem B2316293 : Blo 1543469 2316293 := bbase (se 4 (by rfl) ⟨217152, by rfl⟩ : syracuseStep 2316293 = 434305) (by norm_num)
theorem B29677589 : Blo 1543469 29677589 := bbase (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) (by norm_num)
theorem B2930717 : Blo 1543469 2930717 := bbase (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) (by norm_num)
theorem B2316317 : Blo 1543469 2316317 := bbase (se 3 (by rfl) ⟨434309, by rfl⟩ : syracuseStep 2316317 = 868619) (by norm_num)
theorem B2316341 : Blo 1543469 2316341 := bbase (se 5 (by rfl) ⟨108578, by rfl⟩ : syracuseStep 2316341 = 217157) (by norm_num)
theorem B2316365 : Blo 1543469 2316365 := bbase (se 3 (by rfl) ⟨434318, by rfl⟩ : syracuseStep 2316365 = 868637) (by norm_num)
theorem B1955917 : Blo 1543469 1955917 := bbase (se 3 (by rfl) ⟨366734, by rfl⟩ : syracuseStep 1955917 = 733469) (by norm_num)
theorem B5281877 : Blo 1543469 5281877 := bbase (se 8 (by rfl) ⟨30948, by rfl⟩ : syracuseStep 5281877 = 61897) (by norm_num)
theorem B2316389 : Blo 1543469 2316389 := bbase (se 4 (by rfl) ⟨217161, by rfl⟩ : syracuseStep 2316389 = 434323) (by norm_num)
theorem B2316413 : Blo 1543469 2316413 := bbase (se 3 (by rfl) ⟨434327, by rfl⟩ : syracuseStep 2316413 = 868655) (by norm_num)
theorem B2316437 : Blo 1543469 2316437 := bbase (se 6 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 2316437 = 108583) (by norm_num)
theorem B3709093 : Blo 1543469 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B2316461 : Blo 1543469 2316461 := bbase (se 3 (by rfl) ⟨434336, by rfl⟩ : syracuseStep 2316461 = 868673) (by norm_num)
theorem B4397237 : Blo 1543469 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B1587389 : Blo 1543469 1587389 := bbase (se 3 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 1587389 = 595271) (by norm_num)
theorem B2316485 : Blo 1543469 2316485 := bbase (se 4 (by rfl) ⟨217170, by rfl⟩ : syracuseStep 2316485 = 434341) (by norm_num)
theorem B2349253 : Blo 1543469 2349253 := bbase (se 4 (by rfl) ⟨220242, by rfl⟩ : syracuseStep 2349253 = 440485) (by norm_num)
theorem B2316509 : Blo 1543469 2316509 := bbase (se 3 (by rfl) ⟨434345, by rfl⟩ : syracuseStep 2316509 = 868691) (by norm_num)
theorem B2316533 : Blo 1543469 2316533 := bbase (se 5 (by rfl) ⟨108587, by rfl⟩ : syracuseStep 2316533 = 217175) (by norm_num)
theorem B2087165 : Blo 1543469 2087165 := bbase (se 3 (by rfl) ⟨391343, by rfl⟩ : syracuseStep 2087165 = 782687) (by norm_num)
theorem B2316557 : Blo 1543469 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B2316581 : Blo 1543469 2316581 := bbase (se 4 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 2316581 = 434359) (by norm_num)
theorem B3299629 : Blo 1543469 3299629 := bbase (se 3 (by rfl) ⟨618680, by rfl⟩ : syracuseStep 3299629 = 1237361) (by norm_num)
theorem B2931005 : Blo 1543469 2931005 := bbase (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) (by norm_num)
theorem B2316605 : Blo 1543469 2316605 := bbase (se 3 (by rfl) ⟨434363, by rfl⟩ : syracuseStep 2316605 = 868727) (by norm_num)
theorem B2316629 : Blo 1543469 2316629 := bbase (se 10 (by rfl) ⟨3393, by rfl⟩ : syracuseStep 2316629 = 6787) (by norm_num)
theorem B2316653 : Blo 1543469 2316653 := bbase (se 3 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 2316653 = 868745) (by norm_num)
theorem B2316677 : Blo 1543469 2316677 := bbase (se 4 (by rfl) ⟨217188, by rfl⟩ : syracuseStep 2316677 = 434377) (by norm_num)
theorem B2087317 : Blo 1543469 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B2316701 : Blo 1543469 2316701 := bbase (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) (by norm_num)
theorem B2316725 : Blo 1543469 2316725 := bbase (se 5 (by rfl) ⟨108596, by rfl⟩ : syracuseStep 2316725 = 217193) (by norm_num)
theorem B3299773 : Blo 1543469 3299773 := bbase (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) (by norm_num)
theorem B2316749 : Blo 1543469 2316749 := bbase (se 3 (by rfl) ⟨434390, by rfl⟩ : syracuseStep 2316749 = 868781) (by norm_num)
theorem B2931157 : Blo 1543469 2931157 := bbase (se 7 (by rfl) ⟨34349, by rfl⟩ : syracuseStep 2931157 = 68699) (by norm_num)
theorem B2316773 : Blo 1543469 2316773 := bbase (se 4 (by rfl) ⟨217197, by rfl⟩ : syracuseStep 2316773 = 434395) (by norm_num)
theorem B3709421 : Blo 1543469 3709421 := bbase (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) (by norm_num)
theorem B2316797 : Blo 1543469 2316797 := bbase (se 3 (by rfl) ⟨434399, by rfl⟩ : syracuseStep 2316797 = 868799) (by norm_num)
theorem B2316821 : Blo 1543469 2316821 := bbase (se 6 (by rfl) ⟨54300, by rfl⟩ : syracuseStep 2316821 = 108601) (by norm_num)
theorem B7821845 : Blo 1543469 7821845 := bbase (se 6 (by rfl) ⟨183324, by rfl⟩ : syracuseStep 7821845 = 366649) (by norm_num)
theorem B3709477 : Blo 1543469 3709477 := bbase (se 4 (by rfl) ⟨347763, by rfl⟩ : syracuseStep 3709477 = 695527) (by norm_num)
theorem B2316845 : Blo 1543469 2316845 := bbase (se 3 (by rfl) ⟨434408, by rfl⟩ : syracuseStep 2316845 = 868817) (by norm_num)
theorem B2316869 : Blo 1543469 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B5642821 : Blo 1543469 5642821 := bbase (se 4 (by rfl) ⟨529014, by rfl⟩ : syracuseStep 5642821 = 1058029) (by norm_num)
theorem B2316893 : Blo 1543469 2316893 := bbase (se 3 (by rfl) ⟨434417, by rfl⟩ : syracuseStep 2316893 = 868835) (by norm_num)
theorem B2316917 : Blo 1543469 2316917 := bbase (se 5 (by rfl) ⟨108605, by rfl⟩ : syracuseStep 2316917 = 217211) (by norm_num)
theorem B2316941 : Blo 1543469 2316941 := bbase (se 3 (by rfl) ⟨434426, by rfl⟩ : syracuseStep 2316941 = 868853) (by norm_num)
theorem B2316965 : Blo 1543469 2316965 := bbase (se 4 (by rfl) ⟨217215, by rfl⟩ : syracuseStep 2316965 = 434431) (by norm_num)
theorem B9894581 : Blo 1543469 9894581 := bbase (se 5 (by rfl) ⟨463808, by rfl⟩ : syracuseStep 9894581 = 927617) (by norm_num)
theorem B2316989 : Blo 1543469 2316989 := bbase (se 3 (by rfl) ⟨434435, by rfl⟩ : syracuseStep 2316989 = 868871) (by norm_num)
theorem B1784533 : Blo 1543469 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B2317013 : Blo 1543469 2317013 := bbase (se 7 (by rfl) ⟨27152, by rfl⟩ : syracuseStep 2317013 = 54305) (by norm_num)
theorem B6601445 : Blo 1543469 6601445 := bbase (se 4 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 6601445 = 1237771) (by norm_num)
theorem B2317037 : Blo 1543469 2317037 := bbase (se 3 (by rfl) ⟨434444, by rfl⟩ : syracuseStep 2317037 = 868889) (by norm_num)
theorem B2931461 : Blo 1543469 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B5864197 : Blo 1543469 5864197 := bbase (se 4 (by rfl) ⟨549768, by rfl⟩ : syracuseStep 5864197 = 1099537) (by norm_num)
theorem B2317061 : Blo 1543469 2317061 := bbase (se 4 (by rfl) ⟨217224, by rfl⟩ : syracuseStep 2317061 = 434449) (by norm_num)
theorem B3709709 : Blo 1543469 3709709 := bbase (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) (by norm_num)
theorem B2317085 : Blo 1543469 2317085 := bbase (se 3 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 2317085 = 868907) (by norm_num)
theorem B2317109 : Blo 1543469 2317109 := bbase (se 5 (by rfl) ⟨108614, by rfl⟩ : syracuseStep 2317109 = 217229) (by norm_num)
theorem B3300149 : Blo 1543469 3300149 := bbase (se 5 (by rfl) ⟨154694, by rfl⟩ : syracuseStep 3300149 = 309389) (by norm_num)
theorem B2317133 : Blo 1543469 2317133 := bbase (se 3 (by rfl) ⟨434462, by rfl⟩ : syracuseStep 2317133 = 868925) (by norm_num)
theorem B4946789 : Blo 1543469 4946789 := bbase (se 4 (by rfl) ⟨463761, by rfl⟩ : syracuseStep 4946789 = 927523) (by norm_num)
theorem B2317157 : Blo 1543469 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B2317181 : Blo 1543469 2317181 := bbase (se 3 (by rfl) ⟨434471, by rfl⟩ : syracuseStep 2317181 = 868943) (by norm_num)
theorem B2317205 : Blo 1543469 2317205 := bbase (se 6 (by rfl) ⟨54309, by rfl⟩ : syracuseStep 2317205 = 108619) (by norm_num)
theorem B4234133 : Blo 1543469 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B4397989 : Blo 1543469 4397989 := bbase (se 4 (by rfl) ⟨412311, by rfl⟩ : syracuseStep 4397989 = 824623) (by norm_num)
theorem B2317229 : Blo 1543469 2317229 := bbase (se 3 (by rfl) ⟨434480, by rfl⟩ : syracuseStep 2317229 = 868961) (by norm_num)
theorem B7814069 : Blo 1543469 7814069 := bbase (se 5 (by rfl) ⟨366284, by rfl⟩ : syracuseStep 7814069 = 732569) (by norm_num)
theorem B2317253 : Blo 1543469 2317253 := bbase (se 4 (by rfl) ⟨217242, by rfl⟩ : syracuseStep 2317253 = 434485) (by norm_num)
theorem B3709901 : Blo 1543469 3709901 := bbase (se 3 (by rfl) ⟨695606, by rfl⟩ : syracuseStep 3709901 = 1391213) (by norm_num)
theorem B2317277 : Blo 1543469 2317277 := bbase (se 3 (by rfl) ⟨434489, by rfl⟩ : syracuseStep 2317277 = 868979) (by norm_num)
theorem B2317301 : Blo 1543469 2317301 := bbase (se 5 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 2317301 = 217247) (by norm_num)
theorem B2317325 : Blo 1543469 2317325 := bbase (se 3 (by rfl) ⟨434498, by rfl⟩ : syracuseStep 2317325 = 868997) (by norm_num)
theorem B2087965 : Blo 1543469 2087965 := bbase (se 3 (by rfl) ⟨391493, by rfl⟩ : syracuseStep 2087965 = 782987) (by norm_num)
theorem B2317349 : Blo 1543469 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B5864501 : Blo 1543469 5864501 := bbase (se 5 (by rfl) ⟨274898, by rfl⟩ : syracuseStep 5864501 = 549797) (by norm_num)
theorem B2317373 : Blo 1543469 2317373 := bbase (se 3 (by rfl) ⟨434507, by rfl⟩ : syracuseStep 2317373 = 869015) (by norm_num)
theorem B2317397 : Blo 1543469 2317397 := bbase (se 8 (by rfl) ⟨13578, by rfl⟩ : syracuseStep 2317397 = 27157) (by norm_num)
theorem B3013733 : Blo 1543469 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2317421 : Blo 1543469 2317421 := bbase (se 3 (by rfl) ⟨434516, by rfl⟩ : syracuseStep 2317421 = 869033) (by norm_num)
theorem B6593669 : Blo 1543469 6593669 := bbase (se 4 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 6593669 = 1236313) (by norm_num)
theorem B2317445 : Blo 1543469 2317445 := bbase (se 4 (by rfl) ⟨217260, by rfl⟩ : syracuseStep 2317445 = 434521) (by norm_num)
theorem B4177045 : Blo 1543469 4177045 := bbase (se 6 (by rfl) ⟨97899, by rfl⟩ : syracuseStep 4177045 = 195799) (by norm_num)
theorem B2317469 : Blo 1543469 2317469 := bbase (se 3 (by rfl) ⟨434525, by rfl⟩ : syracuseStep 2317469 = 869051) (by norm_num)
theorem B3300517 : Blo 1543469 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B3054773 : Blo 1543469 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B2317493 : Blo 1543469 2317493 := bbase (se 5 (by rfl) ⟨108632, by rfl⟩ : syracuseStep 2317493 = 217265) (by norm_num)
theorem B2317517 : Blo 1543469 2317517 := bbase (se 3 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 2317517 = 869069) (by norm_num)
theorem B1981669 : Blo 1543469 1981669 := bbase (se 4 (by rfl) ⟨185781, by rfl⟩ : syracuseStep 1981669 = 371563) (by norm_num)
theorem B2317541 : Blo 1543469 2317541 := bbase (se 4 (by rfl) ⟨217269, by rfl⟩ : syracuseStep 2317541 = 434539) (by norm_num)
theorem B2317565 : Blo 1543469 2317565 := bbase (se 3 (by rfl) ⟨434543, by rfl⟩ : syracuseStep 2317565 = 869087) (by norm_num)
theorem B2317589 : Blo 1543469 2317589 := bbase (se 6 (by rfl) ⟨54318, by rfl⟩ : syracuseStep 2317589 = 108637) (by norm_num)
theorem B2317613 : Blo 1543469 2317613 := bbase (se 3 (by rfl) ⟨434552, by rfl⟩ : syracuseStep 2317613 = 869105) (by norm_num)
theorem B6266165 : Blo 1543469 6266165 := bbase (se 5 (by rfl) ⟨293726, by rfl⟩ : syracuseStep 6266165 = 587453) (by norm_num)
theorem B2317637 : Blo 1543469 2317637 := bbase (se 4 (by rfl) ⟨217278, by rfl⟩ : syracuseStep 2317637 = 434557) (by norm_num)
theorem B38083925 : Blo 1543469 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B2317661 : Blo 1543469 2317661 := bbase (se 3 (by rfl) ⟨434561, by rfl⟩ : syracuseStep 2317661 = 869123) (by norm_num)
theorem B2317685 : Blo 1543469 2317685 := bbase (se 5 (by rfl) ⟨108641, by rfl⟩ : syracuseStep 2317685 = 217283) (by norm_num)
theorem B15859061 : Blo 1543469 15859061 := bbase (se 5 (by rfl) ⟨743393, by rfl⟩ : syracuseStep 15859061 = 1486787) (by norm_num)
theorem B2473357 : Blo 1543469 2473357 := bbase (se 3 (by rfl) ⟨463754, by rfl⟩ : syracuseStep 2473357 = 927509) (by norm_num)
theorem B2317709 : Blo 1543469 2317709 := bbase (se 3 (by rfl) ⟨434570, by rfl⟩ : syracuseStep 2317709 = 869141) (by norm_num)
theorem B2317733 : Blo 1543469 2317733 := bbase (se 4 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 2317733 = 434575) (by norm_num)
theorem B3472829 : Blo 1543469 3472829 := bbase (se 3 (by rfl) ⟨651155, by rfl⟩ : syracuseStep 3472829 = 1302311) (by norm_num)
theorem B2317757 : Blo 1543469 2317757 := bbase (se 3 (by rfl) ⟨434579, by rfl⟩ : syracuseStep 2317757 = 869159) (by norm_num)
theorem B5209541 : Blo 1543469 5209541 := bbase (se 4 (by rfl) ⟨488394, by rfl⟩ : syracuseStep 5209541 = 976789) (by norm_num)
theorem B2317781 : Blo 1543469 2317781 := bbase (se 7 (by rfl) ⟨27161, by rfl⟩ : syracuseStep 2317781 = 54323) (by norm_num)
theorem B5283301 : Blo 1543469 5283301 := bbase (se 4 (by rfl) ⟨495309, by rfl⟩ : syracuseStep 5283301 = 990619) (by norm_num)
theorem B2317805 : Blo 1543469 2317805 := bbase (se 3 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 2317805 = 869177) (by norm_num)
theorem B2932213 : Blo 1543469 2932213 := bbase (se 5 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 2932213 = 274895) (by norm_num)
theorem B3472901 : Blo 1543469 3472901 := bbase (se 4 (by rfl) ⟨325584, by rfl⟩ : syracuseStep 3472901 = 651169) (by norm_num)
theorem B2317829 : Blo 1543469 2317829 := bbase (se 4 (by rfl) ⟨217296, by rfl⟩ : syracuseStep 2317829 = 434593) (by norm_num)
theorem B2317853 : Blo 1543469 2317853 := bbase (se 3 (by rfl) ⟨434597, by rfl⟩ : syracuseStep 2317853 = 869195) (by norm_num)
theorem B2317877 : Blo 1543469 2317877 := bbase (se 5 (by rfl) ⟨108650, by rfl⟩ : syracuseStep 2317877 = 217301) (by norm_num)
theorem B3472973 : Blo 1543469 3472973 := bbase (se 3 (by rfl) ⟨651182, by rfl⟩ : syracuseStep 3472973 = 1302365) (by norm_num)
theorem B2317901 : Blo 1543469 2317901 := bbase (se 3 (by rfl) ⟨434606, by rfl⟩ : syracuseStep 2317901 = 869213) (by norm_num)
theorem B2604629 : Blo 1543469 2604629 := bbase (se 8 (by rfl) ⟨15261, by rfl⟩ : syracuseStep 2604629 = 30523) (by norm_num)
theorem B2317925 : Blo 1543469 2317925 := bbase (se 4 (by rfl) ⟨217305, by rfl⟩ : syracuseStep 2317925 = 434611) (by norm_num)
theorem B2317949 : Blo 1543469 2317949 := bbase (se 3 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 2317949 = 869231) (by norm_num)
theorem B2932357 : Blo 1543469 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B3473045 : Blo 1543469 3473045 := bbase (se 6 (by rfl) ⟨81399, by rfl⟩ : syracuseStep 3473045 = 162799) (by norm_num)
theorem B11730581 : Blo 1543469 11730581 := bbase (se 6 (by rfl) ⟨274935, by rfl⟩ : syracuseStep 11730581 = 549871) (by norm_num)
theorem B2317973 : Blo 1543469 2317973 := bbase (se 6 (by rfl) ⟨54327, by rfl⟩ : syracuseStep 2317973 = 108655) (by norm_num)
theorem B3907237 : Blo 1543469 3907237 := bbase (se 4 (by rfl) ⟨366303, by rfl⟩ : syracuseStep 3907237 = 732607) (by norm_num)
theorem B2317997 : Blo 1543469 2317997 := bbase (se 3 (by rfl) ⟨434624, by rfl⟩ : syracuseStep 2317997 = 869249) (by norm_num)
theorem B2318021 : Blo 1543469 2318021 := bbase (se 4 (by rfl) ⟨217314, by rfl⟩ : syracuseStep 2318021 = 434629) (by norm_num)
theorem B2604757 : Blo 1543469 2604757 := bbase (se 7 (by rfl) ⟨30524, by rfl⟩ : syracuseStep 2604757 = 61049) (by norm_num)
theorem B1670873 : Blo 1543469 1670873 := bbase (se 2 (by rfl) ⟨626577, by rfl⟩ : syracuseStep 1670873 = 1253155) (by norm_num)
theorem B3473117 : Blo 1543469 3473117 := bbase (se 3 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 3473117 = 1302419) (by norm_num)
theorem B2318045 : Blo 1543469 2318045 := bbase (se 3 (by rfl) ⟨434633, by rfl⟩ : syracuseStep 2318045 = 869267) (by norm_num)
theorem B1736437 : Blo 1543469 1736437 := bbase (se 5 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 1736437 = 162791) (by norm_num)
theorem B2318069 : Blo 1543469 2318069 := bbase (se 5 (by rfl) ⟨108659, by rfl⟩ : syracuseStep 2318069 = 217319) (by norm_num)
theorem B2318093 : Blo 1543469 2318093 := bbase (se 3 (by rfl) ⟨434642, by rfl⟩ : syracuseStep 2318093 = 869285) (by norm_num)
theorem B3907349 : Blo 1543469 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1736473 : Blo 1543469 1736473 := bbase (se 2 (by rfl) ⟨651177, by rfl⟩ : syracuseStep 1736473 = 1302355) (by norm_num)
theorem B3473189 : Blo 1543469 3473189 := bbase (se 4 (by rfl) ⟨325611, by rfl⟩ : syracuseStep 3473189 = 651223) (by norm_num)
theorem B2932517 : Blo 1543469 2932517 := bbase (se 4 (by rfl) ⟨274923, by rfl⟩ : syracuseStep 2932517 = 549847) (by norm_num)
theorem B7823141 : Blo 1543469 7823141 := bbase (se 4 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 7823141 = 1466839) (by norm_num)
theorem B2318117 : Blo 1543469 2318117 := bbase (se 4 (by rfl) ⟨217323, by rfl⟩ : syracuseStep 2318117 = 434647) (by norm_num)
theorem B2604845 : Blo 1543469 2604845 := bbase (se 3 (by rfl) ⟨488408, by rfl⟩ : syracuseStep 2604845 = 976817) (by norm_num)
theorem B1736509 : Blo 1543469 1736509 := bbase (se 3 (by rfl) ⟨325595, by rfl⟩ : syracuseStep 1736509 = 651191) (by norm_num)
theorem B2318141 : Blo 1543469 2318141 := bbase (se 3 (by rfl) ⟨434651, by rfl⟩ : syracuseStep 2318141 = 869303) (by norm_num)
theorem B2678597 : Blo 1543469 2678597 := bbase (se 4 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 2678597 = 502237) (by norm_num)
theorem B2473805 : Blo 1543469 2473805 := bbase (se 3 (by rfl) ⟨463838, by rfl⟩ : syracuseStep 2473805 = 927677) (by norm_num)
theorem B2318165 : Blo 1543469 2318165 := bbase (se 9 (by rfl) ⟨6791, by rfl⟩ : syracuseStep 2318165 = 13583) (by norm_num)
theorem B1736545 : Blo 1543469 1736545 := bbase (se 2 (by rfl) ⟨651204, by rfl⟩ : syracuseStep 1736545 = 1302409) (by norm_num)
theorem B3473261 : Blo 1543469 3473261 := bbase (se 3 (by rfl) ⟨651236, by rfl⟩ : syracuseStep 3473261 = 1302473) (by norm_num)
theorem B2318189 : Blo 1543469 2318189 := bbase (se 3 (by rfl) ⟨434660, by rfl⟩ : syracuseStep 2318189 = 869321) (by norm_num)
theorem B5209973 : Blo 1543469 5209973 := bbase (se 5 (by rfl) ⟨244217, by rfl⟩ : syracuseStep 5209973 = 488435) (by norm_num)
theorem B1736581 : Blo 1543469 1736581 := bbase (se 4 (by rfl) ⟨162804, by rfl⟩ : syracuseStep 1736581 = 325609) (by norm_num)
theorem B3710861 : Blo 1543469 3710861 := bbase (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) (by norm_num)
theorem B1736617 : Blo 1543469 1736617 := bbase (se 2 (by rfl) ⟨651231, by rfl⟩ : syracuseStep 1736617 = 1302463) (by norm_num)
theorem B2604973 : Blo 1543469 2604973 := bbase (se 3 (by rfl) ⟨488432, by rfl⟩ : syracuseStep 2604973 = 976865) (by norm_num)
theorem B3473333 : Blo 1543469 3473333 := bbase (se 5 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 3473333 = 325625) (by norm_num)
theorem B2932661 : Blo 1543469 2932661 := bbase (se 5 (by rfl) ⟨137468, by rfl⟩ : syracuseStep 2932661 = 274937) (by norm_num)
theorem B1736653 : Blo 1543469 1736653 := bbase (se 3 (by rfl) ⟨325622, by rfl⟩ : syracuseStep 1736653 = 651245) (by norm_num)
theorem B3907541 : Blo 1543469 3907541 := bbase (se 7 (by rfl) ⟨45791, by rfl⟩ : syracuseStep 3907541 = 91583) (by norm_num)
theorem B8798165 : Blo 1543469 8798165 := bbase (se 7 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 8798165 = 206207) (by norm_num)
theorem B1736689 : Blo 1543469 1736689 := bbase (se 2 (by rfl) ⟨651258, by rfl⟩ : syracuseStep 1736689 = 1302517) (by norm_num)
theorem B3473405 : Blo 1543469 3473405 := bbase (se 3 (by rfl) ⟨651263, by rfl⟩ : syracuseStep 3473405 = 1302527) (by norm_num)
theorem B2473985 : Blo 1543469 2473985 := bstep (se 2 (by rfl) ⟨927744, by rfl⟩ : syracuseStep 2473985 = 1855489) B1855489
theorem B1736707 : Blo 1543469 1736707 := bstep (se 1 (by rfl) ⟨1302530, by rfl⟩ : syracuseStep 1736707 = 2605061) B2605061
theorem B18792461 : Blo 1543469 18792461 := bstep (se 3 (by rfl) ⟨3523586, by rfl⟩ : syracuseStep 18792461 = 7047173) B7047173
theorem B7815203 : Blo 1543469 7815203 := bstep (se 1 (by rfl) ⟨5861402, by rfl⟩ : syracuseStep 7815203 = 11722805) B11722805
theorem B5210189 : Blo 1543469 5210189 := bstep (se 3 (by rfl) ⟨976910, by rfl⟩ : syracuseStep 5210189 = 1953821) B1953821
theorem B2605169 : Blo 1543469 2605169 := bstep (se 2 (by rfl) ⟨976938, by rfl⟩ : syracuseStep 2605169 = 1953877) B1953877
theorem B5210243 : Blo 1543469 5210243 := bstep (se 1 (by rfl) ⟨3907682, by rfl⟩ : syracuseStep 5210243 = 7815365) B7815365
theorem B1736851 : Blo 1543469 1736851 := bstep (se 1 (by rfl) ⟨1302638, by rfl⟩ : syracuseStep 1736851 = 2605277) B2605277
theorem B3473585 : Blo 1543469 3473585 := bstep (se 2 (by rfl) ⟨1302594, by rfl⟩ : syracuseStep 3473585 = 2605189) B2605189
theorem B3473603 : Blo 1543469 3473603 := bstep (se 1 (by rfl) ⟨2605202, by rfl⟩ : syracuseStep 3473603 = 5210405) B5210405
theorem B1761475 : Blo 1543469 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B2605297 : Blo 1543469 2605297 := bstep (se 2 (by rfl) ⟨976986, by rfl⟩ : syracuseStep 2605297 = 1953973) B1953973
theorem B2605331 : Blo 1543469 2605331 := bstep (se 1 (by rfl) ⟨1953998, by rfl⟩ : syracuseStep 2605331 = 3907997) B3907997
theorem B1736995 : Blo 1543469 1736995 := bstep (se 1 (by rfl) ⟨1302746, by rfl⟩ : syracuseStep 1736995 = 2605493) B2605493
theorem B2474369 : Blo 1543469 2474369 := bstep (se 2 (by rfl) ⟨927888, by rfl⟩ : syracuseStep 2474369 = 1855777) B1855777
theorem B5210513 : Blo 1543469 5210513 := bstep (se 2 (by rfl) ⟨1953942, by rfl⟩ : syracuseStep 5210513 = 3907885) B3907885
theorem B4399505 : Blo 1543469 4399505 := bstep (se 2 (by rfl) ⟨1649814, by rfl⟩ : syracuseStep 4399505 = 3299629) B3299629
theorem B2605459 : Blo 1543469 2605459 := bstep (se 1 (by rfl) ⟨1954094, by rfl⟩ : syracuseStep 2605459 = 3908189) B3908189
theorem B1737139 : Blo 1543469 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B3473873 : Blo 1543469 3473873 := bstep (se 2 (by rfl) ⟨1302702, by rfl⟩ : syracuseStep 3473873 = 2605405) B2605405
theorem B3473891 : Blo 1543469 3473891 := bstep (se 1 (by rfl) ⟨2605418, by rfl⟩ : syracuseStep 3473891 = 5210837) B5210837
theorem B2474497 : Blo 1543469 2474497 := bstep (se 2 (by rfl) ⟨927936, by rfl⟩ : syracuseStep 2474497 = 1855873) B1855873
theorem B2605601 : Blo 1543469 2605601 := bstep (se 2 (by rfl) ⟨977100, by rfl⟩ : syracuseStep 2605601 = 1954201) B1954201
theorem B3129905 : Blo 1543469 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B66839093 : Blo 1543469 66839093 := bstep (se 5 (by rfl) ⟨3133082, by rfl⟩ : syracuseStep 66839093 = 6266165) B6266165
theorem B1737283 : Blo 1543469 1737283 := bstep (se 1 (by rfl) ⟨1302962, by rfl⟩ : syracuseStep 1737283 = 2605925) B2605925
theorem B4399697 : Blo 1543469 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B2933329 : Blo 1543469 2933329 := bstep (se 2 (by rfl) ⟨1099998, by rfl⟩ : syracuseStep 2933329 = 2199997) B2199997
theorem B2507363 : Blo 1543469 2507363 := bstep (se 1 (by rfl) ⟨1880522, by rfl⟩ : syracuseStep 2507363 = 3761045) B3761045
theorem B3908209 : Blo 1543469 3908209 := bstep (se 2 (by rfl) ⟨1465578, by rfl⟩ : syracuseStep 3908209 = 2931157) B2931157
theorem B2605729 : Blo 1543469 2605729 := bstep (se 2 (by rfl) ⟨977148, by rfl⟩ : syracuseStep 2605729 = 1954297) B1954297
theorem B2605763 : Blo 1543469 2605763 := bstep (se 1 (by rfl) ⟨1954322, by rfl⟩ : syracuseStep 2605763 = 3908645) B3908645
theorem B1737427 : Blo 1543469 1737427 := bstep (se 1 (by rfl) ⟨1303070, by rfl⟩ : syracuseStep 1737427 = 2606141) B2606141
theorem B3474161 : Blo 1543469 3474161 := bstep (se 2 (by rfl) ⟨1302810, by rfl⟩ : syracuseStep 3474161 = 2605621) B2605621
theorem B2933489 : Blo 1543469 2933489 := bstep (se 2 (by rfl) ⟨1100058, by rfl⟩ : syracuseStep 2933489 = 2200117) B2200117
theorem B3474179 : Blo 1543469 3474179 := bstep (se 1 (by rfl) ⟨2605634, by rfl⟩ : syracuseStep 3474179 = 5211269) B5211269
theorem B2605891 : Blo 1543469 2605891 := bstep (se 1 (by rfl) ⟨1954418, by rfl⟩ : syracuseStep 2605891 = 3908837) B3908837
theorem B7816013 : Blo 1543469 7816013 := bstep (se 3 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 7816013 = 2931005) B2931005
theorem B1737571 : Blo 1543469 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B3908483 : Blo 1543469 3908483 := bstep (se 1 (by rfl) ⟨2931362, by rfl⟩ : syracuseStep 3908483 = 5862725) B5862725
theorem B5211053 : Blo 1543469 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B4948931 : Blo 1543469 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B5866445 : Blo 1543469 5866445 := bstep (se 3 (by rfl) ⟨1099958, by rfl⟩ : syracuseStep 5866445 = 2199917) B2199917
theorem B2606033 : Blo 1543469 2606033 := bstep (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) B1954525
theorem B5211107 : Blo 1543469 5211107 := bstep (se 1 (by rfl) ⟨3908330, by rfl⟩ : syracuseStep 5211107 = 7816661) B7816661
theorem B1737715 : Blo 1543469 1737715 := bstep (se 1 (by rfl) ⟨1303286, by rfl⟩ : syracuseStep 1737715 = 2606573) B2606573
theorem B3474449 : Blo 1543469 3474449 := bstep (se 2 (by rfl) ⟨1302918, by rfl⟩ : syracuseStep 3474449 = 2605837) B2605837
theorem B3474467 : Blo 1543469 3474467 := bstep (se 1 (by rfl) ⟨2605850, by rfl⟩ : syracuseStep 3474467 = 5211701) B5211701
theorem B3908675 : Blo 1543469 3908675 := bstep (se 1 (by rfl) ⟨2931506, by rfl⟩ : syracuseStep 3908675 = 5863013) B5863013
theorem B2606161 : Blo 1543469 2606161 := bstep (se 2 (by rfl) ⟨977310, by rfl⟩ : syracuseStep 2606161 = 1954621) B1954621
theorem B2606195 : Blo 1543469 2606195 := bstep (se 1 (by rfl) ⟨1954646, by rfl⟩ : syracuseStep 2606195 = 3909293) B3909293
theorem B1737859 : Blo 1543469 1737859 := bstep (se 1 (by rfl) ⟨1303394, by rfl⟩ : syracuseStep 1737859 = 2606789) B2606789
theorem B2933891 : Blo 1543469 2933891 := bstep (se 1 (by rfl) ⟨2200418, by rfl⟩ : syracuseStep 2933891 = 4400837) B4400837
theorem B5211377 : Blo 1543469 5211377 := bstep (se 2 (by rfl) ⟨1954266, by rfl⟩ : syracuseStep 5211377 = 3908533) B3908533
theorem B2606323 : Blo 1543469 2606323 := bstep (se 1 (by rfl) ⟨1954742, by rfl⟩ : syracuseStep 2606323 = 3909485) B3909485
theorem B1738003 : Blo 1543469 1738003 := bstep (se 1 (by rfl) ⟨1303502, by rfl⟩ : syracuseStep 1738003 = 2607005) B2607005
theorem B3474737 : Blo 1543469 3474737 := bstep (se 2 (by rfl) ⟨1303026, by rfl⟩ : syracuseStep 3474737 = 2606053) B2606053
theorem B3474755 : Blo 1543469 3474755 := bstep (se 1 (by rfl) ⟨2606066, by rfl⟩ : syracuseStep 3474755 = 5212133) B5212133
theorem B4457809 : Blo 1543469 4457809 := bstep (se 2 (by rfl) ⟨1671678, by rfl⟩ : syracuseStep 4457809 = 3343357) B3343357
theorem B19785059 : Blo 1543469 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B2606465 : Blo 1543469 2606465 := bstep (se 2 (by rfl) ⟨977424, by rfl⟩ : syracuseStep 2606465 = 1954849) B1954849
theorem B1738147 : Blo 1543469 1738147 := bstep (se 1 (by rfl) ⟨1303610, by rfl⟩ : syracuseStep 1738147 = 2607221) B2607221
theorem B2606593 : Blo 1543469 2606593 := bstep (se 2 (by rfl) ⟨977472, by rfl⟩ : syracuseStep 2606593 = 1954945) B1954945
theorem B2606627 : Blo 1543469 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B4400689 : Blo 1543469 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B2229811 : Blo 1543469 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B1738291 : Blo 1543469 1738291 := bstep (se 1 (by rfl) ⟨1303718, by rfl⟩ : syracuseStep 1738291 = 2607437) B2607437
theorem B3475025 : Blo 1543469 3475025 := bstep (se 2 (by rfl) ⟨1303134, by rfl⟩ : syracuseStep 3475025 = 2606269) B2606269
theorem B3475043 : Blo 1543469 3475043 := bstep (se 1 (by rfl) ⟨2606282, by rfl⟩ : syracuseStep 3475043 = 5212565) B5212565
theorem B2606755 : Blo 1543469 2606755 := bstep (se 1 (by rfl) ⟨1955066, by rfl⟩ : syracuseStep 2606755 = 3910133) B3910133
theorem B1738435 : Blo 1543469 1738435 := bstep (se 1 (by rfl) ⟨1303826, by rfl⟩ : syracuseStep 1738435 = 2607653) B2607653
theorem B8799941 : Blo 1543469 8799941 := bstep (se 4 (by rfl) ⟨824994, by rfl⟩ : syracuseStep 8799941 = 1649989) B1649989
theorem B5211917 : Blo 1543469 5211917 := bstep (se 3 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 5211917 = 1954469) B1954469
theorem B6596387 : Blo 1543469 6596387 := bstep (se 1 (by rfl) ⟨4947290, by rfl⟩ : syracuseStep 6596387 = 9894581) B9894581
theorem B2606897 : Blo 1543469 2606897 := bstep (se 2 (by rfl) ⟨977586, by rfl⟩ : syracuseStep 2606897 = 1955173) B1955173
theorem B19793717 : Blo 1543469 19793717 := bstep (se 5 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 19793717 = 1855661) B1855661
theorem B5211971 : Blo 1543469 5211971 := bstep (se 1 (by rfl) ⟨3908978, by rfl⟩ : syracuseStep 5211971 = 7817957) B7817957
theorem B4400963 : Blo 1543469 4400963 := bstep (se 1 (by rfl) ⟨3300722, by rfl⟩ : syracuseStep 4400963 = 6601445) B6601445
theorem B1738579 : Blo 1543469 1738579 := bstep (se 1 (by rfl) ⟨1303934, by rfl⟩ : syracuseStep 1738579 = 2607869) B2607869
theorem B3475313 : Blo 1543469 3475313 := bstep (se 2 (by rfl) ⟨1303242, by rfl⟩ : syracuseStep 3475313 = 2606485) B2606485
theorem B3475331 : Blo 1543469 3475331 := bstep (se 1 (by rfl) ⟨2606498, by rfl⟩ : syracuseStep 3475331 = 5212997) B5212997
theorem B2607025 : Blo 1543469 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B17582021 : Blo 1543469 17582021 := bstep (se 4 (by rfl) ⟨1648314, by rfl⟩ : syracuseStep 17582021 = 3296629) B3296629
theorem B2607059 : Blo 1543469 2607059 := bstep (se 1 (by rfl) ⟨1955294, by rfl⟩ : syracuseStep 2607059 = 3910589) B3910589
theorem B3909617 : Blo 1543469 3909617 := bstep (se 2 (by rfl) ⟨1466106, by rfl⟩ : syracuseStep 3909617 = 2932213) B2932213
theorem B3909667 : Blo 1543469 3909667 := bstep (se 1 (by rfl) ⟨2932250, by rfl⟩ : syracuseStep 3909667 = 5864501) B5864501
theorem B2009155 : Blo 1543469 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B5212241 : Blo 1543469 5212241 := bstep (se 2 (by rfl) ⟨1954590, by rfl⟩ : syracuseStep 5212241 = 3909181) B3909181
theorem B2607187 : Blo 1543469 2607187 := bstep (se 1 (by rfl) ⟨1955390, by rfl⟩ : syracuseStep 2607187 = 3910781) B3910781
theorem B8800397 : Blo 1543469 8800397 := bstep (se 3 (by rfl) ⟨1650074, by rfl⟩ : syracuseStep 8800397 = 3300149) B3300149
theorem B3475601 : Blo 1543469 3475601 := bstep (se 2 (by rfl) ⟨1303350, by rfl⟩ : syracuseStep 3475601 = 2606701) B2606701
theorem B3475619 : Blo 1543469 3475619 := bstep (se 1 (by rfl) ⟨2606714, by rfl⟩ : syracuseStep 3475619 = 5213429) B5213429
theorem B3909809 : Blo 1543469 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B2230465 : Blo 1543469 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B2607329 : Blo 1543469 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B25389283 : Blo 1543469 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B8792333 : Blo 1543469 8792333 := bstep (se 3 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 8792333 = 3297125) B3297125
theorem B13191437 : Blo 1543469 13191437 := bstep (se 3 (by rfl) ⟨2473394, by rfl⟩ : syracuseStep 13191437 = 4946789) B4946789
theorem B2197793 : Blo 1543469 2197793 := bstep (se 2 (by rfl) ⟨824172, by rfl⟩ : syracuseStep 2197793 = 1648345) B1648345
theorem B2607457 : Blo 1543469 2607457 := bstep (se 2 (by rfl) ⟨977796, by rfl⟩ : syracuseStep 2607457 = 1955593) B1955593
theorem B2640241 : Blo 1543469 2640241 := bstep (se 2 (by rfl) ⟨990090, by rfl⟩ : syracuseStep 2640241 = 1980181) B1980181
theorem B2607491 : Blo 1543469 2607491 := bstep (se 1 (by rfl) ⟨1955618, by rfl⟩ : syracuseStep 2607491 = 3911237) B3911237
theorem B3475889 : Blo 1543469 3475889 := bstep (se 2 (by rfl) ⟨1303458, by rfl⟩ : syracuseStep 3475889 = 2606917) B2606917
theorem B3475907 : Blo 1543469 3475907 := bstep (se 1 (by rfl) ⟨2606930, by rfl⟩ : syracuseStep 3475907 = 5213861) B5213861
theorem B17590769 : Blo 1543469 17590769 := bstep (se 2 (by rfl) ⟨6596538, by rfl⟩ : syracuseStep 17590769 = 13193077) B13193077
theorem B2607619 : Blo 1543469 2607619 := bstep (se 1 (by rfl) ⟨1955714, by rfl⟩ : syracuseStep 2607619 = 3911429) B3911429
theorem B1649203 : Blo 1543469 1649203 := bstep (se 1 (by rfl) ⟨1236902, by rfl⟩ : syracuseStep 1649203 = 2473805) B2473805
theorem B28961333 : Blo 1543469 28961333 := bstep (se 5 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 28961333 = 2715125) B2715125
theorem B11127395 : Blo 1543469 11127395 := bstep (se 1 (by rfl) ⟨8345546, by rfl⟩ : syracuseStep 11127395 = 16691093) B16691093
theorem B5212781 : Blo 1543469 5212781 := bstep (se 3 (by rfl) ⟨977396, by rfl⟩ : syracuseStep 5212781 = 1954793) B1954793
theorem B17836685 : Blo 1543469 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B2607761 : Blo 1543469 2607761 := bstep (se 2 (by rfl) ⟨977910, by rfl⟩ : syracuseStep 2607761 = 1955821) B1955821
theorem B5212835 : Blo 1543469 5212835 := bstep (se 1 (by rfl) ⟨3909626, by rfl⟩ : syracuseStep 5212835 = 7819253) B7819253
theorem B3476177 : Blo 1543469 3476177 := bstep (se 2 (by rfl) ⟨1303566, by rfl⟩ : syracuseStep 3476177 = 2607133) B2607133
theorem B20064995 : Blo 1543469 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B3476195 : Blo 1543469 3476195 := bstep (se 1 (by rfl) ⟨2607146, by rfl⟩ : syracuseStep 3476195 = 5214293) B5214293
theorem B9898757 : Blo 1543469 9898757 := bstep (se 4 (by rfl) ⟨928008, by rfl⟩ : syracuseStep 9898757 = 1856017) B1856017
theorem B2607889 : Blo 1543469 2607889 := bstep (se 2 (by rfl) ⟨977958, by rfl⟩ : syracuseStep 2607889 = 1955917) B1955917
theorem B2607923 : Blo 1543469 2607923 := bstep (se 1 (by rfl) ⟨1955942, by rfl⟩ : syracuseStep 2607923 = 3911885) B3911885
theorem B9399203 : Blo 1543469 9399203 := bstep (se 1 (by rfl) ⟨7049402, by rfl⟩ : syracuseStep 9399203 = 14098805) B14098805
theorem B5213105 : Blo 1543469 5213105 := bstep (se 2 (by rfl) ⟨1954914, by rfl⟩ : syracuseStep 5213105 = 3909829) B3909829
theorem B3132337 : Blo 1543469 3132337 := bstep (se 2 (by rfl) ⟨1174626, by rfl⟩ : syracuseStep 3132337 = 2349253) B2349253
theorem B66767813 : Blo 1543469 66767813 := bstep (se 4 (by rfl) ⟨6259482, by rfl⟩ : syracuseStep 66767813 = 12518965) B12518965
theorem B5352419 : Blo 1543469 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B3476465 : Blo 1543469 3476465 := bstep (se 2 (by rfl) ⟨1303674, by rfl⟩ : syracuseStep 3476465 = 2607349) B2607349
theorem B1854451 : Blo 1543469 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B3476483 : Blo 1543469 3476483 := bstep (se 1 (by rfl) ⟨2607362, by rfl⟩ : syracuseStep 3476483 = 5214725) B5214725
theorem B19803149 : Blo 1543469 19803149 := bstep (se 3 (by rfl) ⟨3713090, by rfl⟩ : syracuseStep 19803149 = 7426181) B7426181
theorem B2198659 : Blo 1543469 2198659 := bstep (se 1 (by rfl) ⟨1648994, by rfl⟩ : syracuseStep 2198659 = 3297989) B3297989
theorem B8146061 : Blo 1543469 8146061 := bstep (se 3 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 8146061 = 3054773) B3054773
theorem B3910801 : Blo 1543469 3910801 := bstep (se 2 (by rfl) ⟨1466550, by rfl⟩ : syracuseStep 3910801 = 2933101) B2933101
theorem B1854643 : Blo 1543469 1854643 := bstep (se 1 (by rfl) ⟨1390982, by rfl⟩ : syracuseStep 1854643 = 2781965) B2781965
theorem B2198755 : Blo 1543469 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B5942513 : Blo 1543469 5942513 := bstep (se 2 (by rfl) ⟨2228442, by rfl⟩ : syracuseStep 5942513 = 4456885) B4456885
theorem B3476753 : Blo 1543469 3476753 := bstep (se 2 (by rfl) ⟨1303782, by rfl⟩ : syracuseStep 3476753 = 2607565) B2607565
theorem B3476771 : Blo 1543469 3476771 := bstep (se 1 (by rfl) ⟨2607578, by rfl⟩ : syracuseStep 3476771 = 5215157) B5215157
theorem B1543475 : Blo 1543469 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1543491 : Blo 1543469 1543491 := bstep (se 1 (by rfl) ⟨1157618, by rfl⟩ : syracuseStep 1543491 = 2315237) B2315237
theorem B1854787 : Blo 1543469 1854787 := bstep (se 1 (by rfl) ⟨1391090, by rfl⟩ : syracuseStep 1854787 = 2782181) B2782181
theorem B5565773 : Blo 1543469 5565773 := bstep (se 3 (by rfl) ⟨1043582, by rfl⟩ : syracuseStep 5565773 = 2087165) B2087165
theorem B1543507 : Blo 1543469 1543507 := bstep (se 1 (by rfl) ⟨1157630, by rfl⟩ : syracuseStep 1543507 = 2315261) B2315261
theorem B1543523 : Blo 1543469 1543523 := bstep (se 1 (by rfl) ⟨1157642, by rfl⟩ : syracuseStep 1543523 = 2315285) B2315285
theorem B1543539 : Blo 1543469 1543539 := bstep (se 1 (by rfl) ⟨1157654, by rfl⟩ : syracuseStep 1543539 = 2315309) B2315309
theorem B1543555 : Blo 1543469 1543555 := bstep (se 1 (by rfl) ⟨1157666, by rfl⟩ : syracuseStep 1543555 = 2315333) B2315333
theorem B1543571 : Blo 1543469 1543571 := bstep (se 1 (by rfl) ⟨1157678, by rfl⟩ : syracuseStep 1543571 = 2315357) B2315357
theorem B1543587 : Blo 1543469 1543587 := bstep (se 1 (by rfl) ⟨1157690, by rfl⟩ : syracuseStep 1543587 = 2315381) B2315381
theorem B3911075 : Blo 1543469 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B7523761 : Blo 1543469 7523761 := bstep (se 2 (by rfl) ⟨2821410, by rfl⟩ : syracuseStep 7523761 = 5642821) B5642821
theorem B1543603 : Blo 1543469 1543603 := bstep (se 1 (by rfl) ⟨1157702, by rfl⟩ : syracuseStep 1543603 = 2315405) B2315405
theorem B1543619 : Blo 1543469 1543619 := bstep (se 1 (by rfl) ⟨1157714, by rfl⟩ : syracuseStep 1543619 = 2315429) B2315429
theorem B11734469 : Blo 1543469 11734469 := bstep (se 4 (by rfl) ⟨1100106, by rfl⟩ : syracuseStep 11734469 = 2200213) B2200213
theorem B5213645 : Blo 1543469 5213645 := bstep (se 3 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 5213645 = 1955117) B1955117
theorem B1543635 : Blo 1543469 1543635 := bstep (se 1 (by rfl) ⟨1157726, by rfl⟩ : syracuseStep 1543635 = 2315453) B2315453
theorem B1543651 : Blo 1543469 1543651 := bstep (se 1 (by rfl) ⟨1157738, by rfl⟩ : syracuseStep 1543651 = 2315477) B2315477
theorem B1543667 : Blo 1543469 1543667 := bstep (se 1 (by rfl) ⟨1157750, by rfl⟩ : syracuseStep 1543667 = 2315501) B2315501
theorem B1543683 : Blo 1543469 1543683 := bstep (se 1 (by rfl) ⟨1157762, by rfl⟩ : syracuseStep 1543683 = 2315525) B2315525
theorem B5213699 : Blo 1543469 5213699 := bstep (se 1 (by rfl) ⟨3910274, by rfl⟩ : syracuseStep 5213699 = 7820549) B7820549
theorem B1543699 : Blo 1543469 1543699 := bstep (se 1 (by rfl) ⟨1157774, by rfl⟩ : syracuseStep 1543699 = 2315549) B2315549
theorem B1543715 : Blo 1543469 1543715 := bstep (se 1 (by rfl) ⟨1157786, by rfl⟩ : syracuseStep 1543715 = 2315573) B2315573
theorem B3477041 : Blo 1543469 3477041 := bstep (se 2 (by rfl) ⟨1303890, by rfl⟩ : syracuseStep 3477041 = 2607781) B2607781
theorem B1543731 : Blo 1543469 1543731 := bstep (se 1 (by rfl) ⟨1157798, by rfl⟩ : syracuseStep 1543731 = 2315597) B2315597
theorem B1543747 : Blo 1543469 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B3477059 : Blo 1543469 3477059 := bstep (se 1 (by rfl) ⟨2607794, by rfl⟩ : syracuseStep 3477059 = 5215589) B5215589
theorem B1543763 : Blo 1543469 1543763 := bstep (se 1 (by rfl) ⟨1157822, by rfl⟩ : syracuseStep 1543763 = 2315645) B2315645
theorem B1543779 : Blo 1543469 1543779 := bstep (se 1 (by rfl) ⟨1157834, by rfl⟩ : syracuseStep 1543779 = 2315669) B2315669
theorem B3911267 : Blo 1543469 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B2379377 : Blo 1543469 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B1543795 : Blo 1543469 1543795 := bstep (se 1 (by rfl) ⟨1157846, by rfl⟩ : syracuseStep 1543795 = 2315693) B2315693
theorem B1543811 : Blo 1543469 1543811 := bstep (se 1 (by rfl) ⟨1157858, by rfl⟩ : syracuseStep 1543811 = 2315717) B2315717
theorem B1543827 : Blo 1543469 1543827 := bstep (se 1 (by rfl) ⟨1157870, by rfl⟩ : syracuseStep 1543827 = 2315741) B2315741
theorem B1543843 : Blo 1543469 1543843 := bstep (se 1 (by rfl) ⟨1157882, by rfl⟩ : syracuseStep 1543843 = 2315765) B2315765
theorem B7818929 : Blo 1543469 7818929 := bstep (se 2 (by rfl) ⟨2932098, by rfl⟩ : syracuseStep 7818929 = 5864197) B5864197
theorem B1543859 : Blo 1543469 1543859 := bstep (se 1 (by rfl) ⟨1157894, by rfl⟩ : syracuseStep 1543859 = 2315789) B2315789
theorem B3296963 : Blo 1543469 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B1543875 : Blo 1543469 1543875 := bstep (se 1 (by rfl) ⟨1157906, by rfl⟩ : syracuseStep 1543875 = 2315813) B2315813
theorem B5861069 : Blo 1543469 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B1543891 : Blo 1543469 1543891 := bstep (se 1 (by rfl) ⟨1157918, by rfl⟩ : syracuseStep 1543891 = 2315837) B2315837
theorem B2199251 : Blo 1543469 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B1543907 : Blo 1543469 1543907 := bstep (se 1 (by rfl) ⟨1157930, by rfl⟩ : syracuseStep 1543907 = 2315861) B2315861
theorem B6598385 : Blo 1543469 6598385 := bstep (se 2 (by rfl) ⟨2474394, by rfl⟩ : syracuseStep 6598385 = 4948789) B4948789
theorem B1543923 : Blo 1543469 1543923 := bstep (se 1 (by rfl) ⟨1157942, by rfl⟩ : syracuseStep 1543923 = 2315885) B2315885
theorem B1543939 : Blo 1543469 1543939 := bstep (se 1 (by rfl) ⟨1157954, by rfl⟩ : syracuseStep 1543939 = 2315909) B2315909
theorem B5213969 : Blo 1543469 5213969 := bstep (se 2 (by rfl) ⟨1955238, by rfl⟩ : syracuseStep 5213969 = 3910477) B3910477
theorem B1543955 : Blo 1543469 1543955 := bstep (se 1 (by rfl) ⟨1157966, by rfl⟩ : syracuseStep 1543955 = 2315933) B2315933
theorem B1543971 : Blo 1543469 1543971 := bstep (se 1 (by rfl) ⟨1157978, by rfl⟩ : syracuseStep 1543971 = 2315957) B2315957
theorem B1543987 : Blo 1543469 1543987 := bstep (se 1 (by rfl) ⟨1157990, by rfl⟩ : syracuseStep 1543987 = 2315981) B2315981
theorem B1544003 : Blo 1543469 1544003 := bstep (se 1 (by rfl) ⟨1158002, by rfl⟩ : syracuseStep 1544003 = 2316005) B2316005
theorem B1544019 : Blo 1543469 1544019 := bstep (se 1 (by rfl) ⟨1158014, by rfl⟩ : syracuseStep 1544019 = 2316029) B2316029
theorem B1544035 : Blo 1543469 1544035 := bstep (se 1 (by rfl) ⟨1158026, by rfl⟩ : syracuseStep 1544035 = 2316053) B2316053
theorem B10170211 : Blo 1543469 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B1544051 : Blo 1543469 1544051 := bstep (se 1 (by rfl) ⟨1158038, by rfl⟩ : syracuseStep 1544051 = 2316077) B2316077
theorem B1544067 : Blo 1543469 1544067 := bstep (se 1 (by rfl) ⟨1158050, by rfl⟩ : syracuseStep 1544067 = 2316101) B2316101
theorem B1544083 : Blo 1543469 1544083 := bstep (se 1 (by rfl) ⟨1158062, by rfl⟩ : syracuseStep 1544083 = 2316125) B2316125
theorem B1544099 : Blo 1543469 1544099 := bstep (se 1 (by rfl) ⟨1158074, by rfl⟩ : syracuseStep 1544099 = 2316149) B2316149
theorem B1953715 : Blo 1543469 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B1544115 : Blo 1543469 1544115 := bstep (se 1 (by rfl) ⟨1158086, by rfl⟩ : syracuseStep 1544115 = 2316173) B2316173
theorem B1544131 : Blo 1543469 1544131 := bstep (se 1 (by rfl) ⟨1158098, by rfl⟩ : syracuseStep 1544131 = 2316197) B2316197
theorem B1544147 : Blo 1543469 1544147 := bstep (se 1 (by rfl) ⟨1158110, by rfl⟩ : syracuseStep 1544147 = 2316221) B2316221
theorem B1544163 : Blo 1543469 1544163 := bstep (se 1 (by rfl) ⟨1158122, by rfl⟩ : syracuseStep 1544163 = 2316245) B2316245
theorem B1544179 : Blo 1543469 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B1544195 : Blo 1543469 1544195 := bstep (se 1 (by rfl) ⟨1158146, by rfl⟩ : syracuseStep 1544195 = 2316293) B2316293
theorem B1953811 : Blo 1543469 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B1544211 : Blo 1543469 1544211 := bstep (se 1 (by rfl) ⟨1158158, by rfl⟩ : syracuseStep 1544211 = 2316317) B2316317
theorem B1544227 : Blo 1543469 1544227 := bstep (se 1 (by rfl) ⟨1158170, by rfl⟩ : syracuseStep 1544227 = 2316341) B2316341
theorem B1544243 : Blo 1543469 1544243 := bstep (se 1 (by rfl) ⟨1158182, by rfl⟩ : syracuseStep 1544243 = 2316365) B2316365
theorem B1544259 : Blo 1543469 1544259 := bstep (se 1 (by rfl) ⟨1158194, by rfl⟩ : syracuseStep 1544259 = 2316389) B2316389
theorem B1544275 : Blo 1543469 1544275 := bstep (se 1 (by rfl) ⟨1158206, by rfl⟩ : syracuseStep 1544275 = 2316413) B2316413
theorem B7417955 : Blo 1543469 7417955 := bstep (se 1 (by rfl) ⟨5563466, by rfl⟩ : syracuseStep 7417955 = 11126933) B11126933
theorem B1544291 : Blo 1543469 1544291 := bstep (se 1 (by rfl) ⟨1158218, by rfl⟩ : syracuseStep 1544291 = 2316437) B2316437
theorem B1544307 : Blo 1543469 1544307 := bstep (se 1 (by rfl) ⟨1158230, by rfl⟩ : syracuseStep 1544307 = 2316461) B2316461
theorem B1544323 : Blo 1543469 1544323 := bstep (se 1 (by rfl) ⟨1158242, by rfl⟩ : syracuseStep 1544323 = 2316485) B2316485
theorem B1544339 : Blo 1543469 1544339 := bstep (se 1 (by rfl) ⟨1158254, by rfl⟩ : syracuseStep 1544339 = 2316509) B2316509
theorem B1544355 : Blo 1543469 1544355 := bstep (se 1 (by rfl) ⟨1158266, by rfl⟩ : syracuseStep 1544355 = 2316533) B2316533
theorem B1544371 : Blo 1543469 1544371 := bstep (se 1 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 1544371 = 2316557) B2316557
theorem B1544387 : Blo 1543469 1544387 := bstep (se 1 (by rfl) ⟨1158290, by rfl⟩ : syracuseStep 1544387 = 2316581) B2316581
theorem B1544403 : Blo 1543469 1544403 := bstep (se 1 (by rfl) ⟨1158302, by rfl⟩ : syracuseStep 1544403 = 2316605) B2316605
theorem B1544419 : Blo 1543469 1544419 := bstep (se 1 (by rfl) ⟨1158314, by rfl⟩ : syracuseStep 1544419 = 2316629) B2316629
theorem B1544435 : Blo 1543469 1544435 := bstep (se 1 (by rfl) ⟨1158326, by rfl⟩ : syracuseStep 1544435 = 2316653) B2316653
theorem B1544451 : Blo 1543469 1544451 := bstep (se 1 (by rfl) ⟨1158338, by rfl⟩ : syracuseStep 1544451 = 2316677) B2316677
theorem B1544467 : Blo 1543469 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B1544483 : Blo 1543469 1544483 := bstep (se 1 (by rfl) ⟨1158362, by rfl⟩ : syracuseStep 1544483 = 2316725) B2316725
theorem B5214509 : Blo 1543469 5214509 := bstep (se 3 (by rfl) ⟨977720, by rfl⟩ : syracuseStep 5214509 = 1955441) B1955441
theorem B2642225 : Blo 1543469 2642225 := bstep (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) B1981669
theorem B1544499 : Blo 1543469 1544499 := bstep (se 1 (by rfl) ⟨1158374, by rfl⟩ : syracuseStep 1544499 = 2316749) B2316749
theorem B1544515 : Blo 1543469 1544515 := bstep (se 1 (by rfl) ⟨1158386, by rfl⟩ : syracuseStep 1544515 = 2316773) B2316773
theorem B2199889 : Blo 1543469 2199889 := bstep (se 2 (by rfl) ⟨824958, by rfl⟩ : syracuseStep 2199889 = 1649917) B1649917
theorem B1544531 : Blo 1543469 1544531 := bstep (se 1 (by rfl) ⟨1158398, by rfl⟩ : syracuseStep 1544531 = 2316797) B2316797
theorem B1544547 : Blo 1543469 1544547 := bstep (se 1 (by rfl) ⟨1158410, by rfl⟩ : syracuseStep 1544547 = 2316821) B2316821
theorem B5214563 : Blo 1543469 5214563 := bstep (se 1 (by rfl) ⟨3910922, by rfl⟩ : syracuseStep 5214563 = 7821845) B7821845
theorem B1544563 : Blo 1543469 1544563 := bstep (se 1 (by rfl) ⟨1158422, by rfl⟩ : syracuseStep 1544563 = 2316845) B2316845
theorem B1544579 : Blo 1543469 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B1544595 : Blo 1543469 1544595 := bstep (se 1 (by rfl) ⟨1158446, by rfl⟩ : syracuseStep 1544595 = 2316893) B2316893
theorem B1544611 : Blo 1543469 1544611 := bstep (se 1 (by rfl) ⟨1158458, by rfl⟩ : syracuseStep 1544611 = 2316917) B2316917
theorem B1544627 : Blo 1543469 1544627 := bstep (se 1 (by rfl) ⟨1158470, by rfl⟩ : syracuseStep 1544627 = 2316941) B2316941
theorem B1544643 : Blo 1543469 1544643 := bstep (se 1 (by rfl) ⟨1158482, by rfl⟩ : syracuseStep 1544643 = 2316965) B2316965
theorem B8794565 : Blo 1543469 8794565 := bstep (se 4 (by rfl) ⟨824490, by rfl⟩ : syracuseStep 8794565 = 1648981) B1648981
theorem B1544659 : Blo 1543469 1544659 := bstep (se 1 (by rfl) ⟨1158494, by rfl⟩ : syracuseStep 1544659 = 2316989) B2316989
theorem B1544675 : Blo 1543469 1544675 := bstep (se 1 (by rfl) ⟨1158506, by rfl⟩ : syracuseStep 1544675 = 2317013) B2317013
theorem B1544691 : Blo 1543469 1544691 := bstep (se 1 (by rfl) ⟨1158518, by rfl⟩ : syracuseStep 1544691 = 2317037) B2317037
theorem B1954307 : Blo 1543469 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1544707 : Blo 1543469 1544707 := bstep (se 1 (by rfl) ⟨1158530, by rfl⟩ : syracuseStep 1544707 = 2317061) B2317061
theorem B3297809 : Blo 1543469 3297809 := bstep (se 2 (by rfl) ⟨1236678, by rfl⟩ : syracuseStep 3297809 = 2473357) B2473357
theorem B1544723 : Blo 1543469 1544723 := bstep (se 1 (by rfl) ⟨1158542, by rfl⟩ : syracuseStep 1544723 = 2317085) B2317085
theorem B1544739 : Blo 1543469 1544739 := bstep (se 1 (by rfl) ⟨1158554, by rfl⟩ : syracuseStep 1544739 = 2317109) B2317109
theorem B1544755 : Blo 1543469 1544755 := bstep (se 1 (by rfl) ⟨1158566, by rfl⟩ : syracuseStep 1544755 = 2317133) B2317133
theorem B30511669 : Blo 1543469 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1544771 : Blo 1543469 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B1544787 : Blo 1543469 1544787 := bstep (se 1 (by rfl) ⟨1158590, by rfl⟩ : syracuseStep 1544787 = 2317181) B2317181
theorem B1544803 : Blo 1543469 1544803 := bstep (se 1 (by rfl) ⟨1158602, by rfl⟩ : syracuseStep 1544803 = 2317205) B2317205
theorem B2822755 : Blo 1543469 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B5214833 : Blo 1543469 5214833 := bstep (se 2 (by rfl) ⟨1955562, by rfl⟩ : syracuseStep 5214833 = 3911125) B3911125
theorem B1544819 : Blo 1543469 1544819 := bstep (se 1 (by rfl) ⟨1158614, by rfl⟩ : syracuseStep 1544819 = 2317229) B2317229
theorem B1544835 : Blo 1543469 1544835 := bstep (se 1 (by rfl) ⟨1158626, by rfl⟩ : syracuseStep 1544835 = 2317253) B2317253
theorem B1544851 : Blo 1543469 1544851 := bstep (se 1 (by rfl) ⟨1158638, by rfl⟩ : syracuseStep 1544851 = 2317277) B2317277
theorem B2200225 : Blo 1543469 2200225 := bstep (se 2 (by rfl) ⟨825084, by rfl⟩ : syracuseStep 2200225 = 1650169) B1650169
theorem B1544867 : Blo 1543469 1544867 := bstep (se 1 (by rfl) ⟨1158650, by rfl⟩ : syracuseStep 1544867 = 2317301) B2317301
theorem B1544883 : Blo 1543469 1544883 := bstep (se 1 (by rfl) ⟨1158662, by rfl⟩ : syracuseStep 1544883 = 2317325) B2317325
theorem B1544899 : Blo 1543469 1544899 := bstep (se 1 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 1544899 = 2317349) B2317349
theorem B1544915 : Blo 1543469 1544915 := bstep (se 1 (by rfl) ⟨1158686, by rfl⟩ : syracuseStep 1544915 = 2317373) B2317373
theorem B1544931 : Blo 1543469 1544931 := bstep (se 1 (by rfl) ⟨1158698, by rfl⟩ : syracuseStep 1544931 = 2317397) B2317397
theorem B1544947 : Blo 1543469 1544947 := bstep (se 1 (by rfl) ⟨1158710, by rfl⟩ : syracuseStep 1544947 = 2317421) B2317421
theorem B4395779 : Blo 1543469 4395779 := bstep (se 1 (by rfl) ⟨3296834, by rfl⟩ : syracuseStep 4395779 = 6593669) B6593669
theorem B1544963 : Blo 1543469 1544963 := bstep (se 1 (by rfl) ⟨1158722, by rfl⟩ : syracuseStep 1544963 = 2317445) B2317445
theorem B1544979 : Blo 1543469 1544979 := bstep (se 1 (by rfl) ⟨1158734, by rfl⟩ : syracuseStep 1544979 = 2317469) B2317469
theorem B1544995 : Blo 1543469 1544995 := bstep (se 1 (by rfl) ⟨1158746, by rfl⟩ : syracuseStep 1544995 = 2317493) B2317493
theorem B4944689 : Blo 1543469 4944689 := bstep (se 2 (by rfl) ⟨1854258, by rfl⟩ : syracuseStep 4944689 = 3708517) B3708517
theorem B1545011 : Blo 1543469 1545011 := bstep (se 1 (by rfl) ⟨1158758, by rfl⟩ : syracuseStep 1545011 = 2317517) B2317517
theorem B1545027 : Blo 1543469 1545027 := bstep (se 1 (by rfl) ⟨1158770, by rfl⟩ : syracuseStep 1545027 = 2317541) B2317541
theorem B1545043 : Blo 1543469 1545043 := bstep (se 1 (by rfl) ⟨1158782, by rfl⟩ : syracuseStep 1545043 = 2317565) B2317565
theorem B4944739 : Blo 1543469 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B1545059 : Blo 1543469 1545059 := bstep (se 1 (by rfl) ⟨1158794, by rfl⟩ : syracuseStep 1545059 = 2317589) B2317589
theorem B1545075 : Blo 1543469 1545075 := bstep (se 1 (by rfl) ⟨1158806, by rfl⟩ : syracuseStep 1545075 = 2317613) B2317613
theorem B1545091 : Blo 1543469 1545091 := bstep (se 1 (by rfl) ⟨1158818, by rfl⟩ : syracuseStep 1545091 = 2317637) B2317637
theorem B53523341 : Blo 1543469 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B1545107 : Blo 1543469 1545107 := bstep (se 1 (by rfl) ⟨1158830, by rfl⟩ : syracuseStep 1545107 = 2317661) B2317661
theorem B1545123 : Blo 1543469 1545123 := bstep (se 1 (by rfl) ⟨1158842, by rfl⟩ : syracuseStep 1545123 = 2317685) B2317685
theorem B10572707 : Blo 1543469 10572707 := bstep (se 1 (by rfl) ⟨7929530, by rfl⟩ : syracuseStep 10572707 = 15859061) B15859061
theorem B4699043 : Blo 1543469 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1545139 : Blo 1543469 1545139 := bstep (se 1 (by rfl) ⟨1158854, by rfl⟩ : syracuseStep 1545139 = 2317709) B2317709
theorem B1545155 : Blo 1543469 1545155 := bstep (se 1 (by rfl) ⟨1158866, by rfl⟩ : syracuseStep 1545155 = 2317733) B2317733
theorem B2315219 : Blo 1543469 2315219 := bstep (se 1 (by rfl) ⟨1736414, by rfl⟩ : syracuseStep 2315219 = 3472829) B3472829
theorem B1545171 : Blo 1543469 1545171 := bstep (se 1 (by rfl) ⟨1158878, by rfl⟩ : syracuseStep 1545171 = 2317757) B2317757
theorem B18789347 : Blo 1543469 18789347 := bstep (se 1 (by rfl) ⟨14092010, by rfl⟩ : syracuseStep 18789347 = 28184021) B28184021
theorem B1545187 : Blo 1543469 1545187 := bstep (se 1 (by rfl) ⟨1158890, by rfl⟩ : syracuseStep 1545187 = 2317781) B2317781
theorem B2315249 : Blo 1543469 2315249 := bstep (se 2 (by rfl) ⟨868218, by rfl⟩ : syracuseStep 2315249 = 1736437) B1736437
theorem B1545203 : Blo 1543469 1545203 := bstep (se 1 (by rfl) ⟨1158902, by rfl⟩ : syracuseStep 1545203 = 2317805) B2317805
theorem B2315267 : Blo 1543469 2315267 := bstep (se 1 (by rfl) ⟨1736450, by rfl⟩ : syracuseStep 2315267 = 3472901) B3472901
theorem B1545219 : Blo 1543469 1545219 := bstep (se 1 (by rfl) ⟨1158914, by rfl⟩ : syracuseStep 1545219 = 2317829) B2317829
theorem B1545235 : Blo 1543469 1545235 := bstep (se 1 (by rfl) ⟨1158926, by rfl⟩ : syracuseStep 1545235 = 2317853) B2317853
theorem B2315297 : Blo 1543469 2315297 := bstep (se 2 (by rfl) ⟨868236, by rfl⟩ : syracuseStep 2315297 = 1736473) B1736473
theorem B1545251 : Blo 1543469 1545251 := bstep (se 1 (by rfl) ⟨1158938, by rfl⟩ : syracuseStep 1545251 = 2317877) B2317877
theorem B2315315 : Blo 1543469 2315315 := bstep (se 1 (by rfl) ⟨1736486, by rfl⟩ : syracuseStep 2315315 = 3472973) B3472973
theorem B1545267 : Blo 1543469 1545267 := bstep (se 1 (by rfl) ⟨1158950, by rfl⟩ : syracuseStep 1545267 = 2317901) B2317901
theorem B4174915 : Blo 1543469 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B1545283 : Blo 1543469 1545283 := bstep (se 1 (by rfl) ⟨1158962, by rfl⟩ : syracuseStep 1545283 = 2317925) B2317925
theorem B2315345 : Blo 1543469 2315345 := bstep (se 2 (by rfl) ⟨868254, by rfl⟩ : syracuseStep 2315345 = 1736509) B1736509
theorem B1545299 : Blo 1543469 1545299 := bstep (se 1 (by rfl) ⟨1158974, by rfl⟩ : syracuseStep 1545299 = 2317949) B2317949
theorem B2315363 : Blo 1543469 2315363 := bstep (se 1 (by rfl) ⟨1736522, by rfl⟩ : syracuseStep 2315363 = 3473045) B3473045
theorem B7820387 : Blo 1543469 7820387 := bstep (se 1 (by rfl) ⟨5865290, by rfl⟩ : syracuseStep 7820387 = 11730581) B11730581
theorem B1545315 : Blo 1543469 1545315 := bstep (se 1 (by rfl) ⟨1158986, by rfl⟩ : syracuseStep 1545315 = 2317973) B2317973
theorem B8795249 : Blo 1543469 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B1545331 : Blo 1543469 1545331 := bstep (se 1 (by rfl) ⟨1158998, by rfl⟩ : syracuseStep 1545331 = 2317997) B2317997
theorem B2315393 : Blo 1543469 2315393 := bstep (se 2 (by rfl) ⟨868272, by rfl⟩ : syracuseStep 2315393 = 1736545) B1736545
theorem B1545347 : Blo 1543469 1545347 := bstep (se 1 (by rfl) ⟨1159010, by rfl⟩ : syracuseStep 1545347 = 2318021) B2318021
theorem B5215373 : Blo 1543469 5215373 := bstep (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) B1955765
theorem B2315411 : Blo 1543469 2315411 := bstep (se 1 (by rfl) ⟨1736558, by rfl⟩ : syracuseStep 2315411 = 3473117) B3473117
theorem B1545363 : Blo 1543469 1545363 := bstep (se 1 (by rfl) ⟨1159022, by rfl⟩ : syracuseStep 1545363 = 2318045) B2318045
theorem B1545379 : Blo 1543469 1545379 := bstep (se 1 (by rfl) ⟨1159034, by rfl⟩ : syracuseStep 1545379 = 2318069) B2318069
theorem B2315441 : Blo 1543469 2315441 := bstep (se 2 (by rfl) ⟨868290, by rfl⟩ : syracuseStep 2315441 = 1736581) B1736581
theorem B1545395 : Blo 1543469 1545395 := bstep (se 1 (by rfl) ⟨1159046, by rfl⟩ : syracuseStep 1545395 = 2318093) B2318093
theorem B2315459 : Blo 1543469 2315459 := bstep (se 1 (by rfl) ⟨1736594, by rfl⟩ : syracuseStep 2315459 = 3473189) B3473189
theorem B1955011 : Blo 1543469 1955011 := bstep (se 1 (by rfl) ⟨1466258, by rfl⟩ : syracuseStep 1955011 = 2932517) B2932517
theorem B5215427 : Blo 1543469 5215427 := bstep (se 1 (by rfl) ⟨3911570, by rfl⟩ : syracuseStep 5215427 = 7823141) B7823141
theorem B1545411 : Blo 1543469 1545411 := bstep (se 1 (by rfl) ⟨1159058, by rfl⟩ : syracuseStep 1545411 = 2318117) B2318117
theorem B1545427 : Blo 1543469 1545427 := bstep (se 1 (by rfl) ⟨1159070, by rfl⟩ : syracuseStep 1545427 = 2318141) B2318141
theorem B2315489 : Blo 1543469 2315489 := bstep (se 2 (by rfl) ⟨868308, by rfl⟩ : syracuseStep 2315489 = 1736617) B1736617
theorem B1545443 : Blo 1543469 1545443 := bstep (se 1 (by rfl) ⟨1159082, by rfl⟩ : syracuseStep 1545443 = 2318165) B2318165
theorem B2315507 : Blo 1543469 2315507 := bstep (se 1 (by rfl) ⟨1736630, by rfl⟩ : syracuseStep 2315507 = 3473261) B3473261
theorem B1545459 : Blo 1543469 1545459 := bstep (se 1 (by rfl) ⟨1159094, by rfl⟩ : syracuseStep 1545459 = 2318189) B2318189
theorem B2315537 : Blo 1543469 2315537 := bstep (se 2 (by rfl) ⟨868326, by rfl⟩ : syracuseStep 2315537 = 1736653) B1736653
theorem B2315555 : Blo 1543469 2315555 := bstep (se 1 (by rfl) ⟨1736666, by rfl⟩ : syracuseStep 2315555 = 3473333) B3473333
theorem B1955107 : Blo 1543469 1955107 := bstep (se 1 (by rfl) ⟨1466330, by rfl⟩ : syracuseStep 1955107 = 2932661) B2932661
theorem B7419185 : Blo 1543469 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B2315585 : Blo 1543469 2315585 := bstep (se 2 (by rfl) ⟨868344, by rfl⟩ : syracuseStep 2315585 = 1736689) B1736689
theorem B2315603 : Blo 1543469 2315603 := bstep (se 1 (by rfl) ⟨1736702, by rfl⟩ : syracuseStep 2315603 = 3473405) B3473405
theorem B2315633 : Blo 1543469 2315633 := bstep (se 2 (by rfl) ⟨868362, by rfl⟩ : syracuseStep 2315633 = 1736725) B1736725
theorem B2315651 : Blo 1543469 2315651 := bstep (se 1 (by rfl) ⟨1736738, by rfl⟩ : syracuseStep 2315651 = 3473477) B3473477
theorem B2315681 : Blo 1543469 2315681 := bstep (se 2 (by rfl) ⟨868380, by rfl⟩ : syracuseStep 2315681 = 1736761) B1736761
theorem B2315699 : Blo 1543469 2315699 := bstep (se 1 (by rfl) ⟨1736774, by rfl⟩ : syracuseStep 2315699 = 3473549) B3473549
theorem B2315729 : Blo 1543469 2315729 := bstep (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) B1736797
theorem B5215697 : Blo 1543469 5215697 := bstep (se 2 (by rfl) ⟨1955886, by rfl⟩ : syracuseStep 5215697 = 3911773) B3911773
theorem B2315747 : Blo 1543469 2315747 := bstep (se 1 (by rfl) ⟨1736810, by rfl⟩ : syracuseStep 2315747 = 3473621) B3473621
theorem B2315777 : Blo 1543469 2315777 := bstep (se 2 (by rfl) ⟨868416, by rfl⟩ : syracuseStep 2315777 = 1736833) B1736833
theorem B2315795 : Blo 1543469 2315795 := bstep (se 1 (by rfl) ⟨1736846, by rfl⟩ : syracuseStep 2315795 = 3473693) B3473693
theorem B4396589 : Blo 1543469 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B4945457 : Blo 1543469 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B2315825 : Blo 1543469 2315825 := bstep (se 2 (by rfl) ⟨868434, by rfl⟩ : syracuseStep 2315825 = 1736869) B1736869
theorem B2315843 : Blo 1543469 2315843 := bstep (se 1 (by rfl) ⟨1736882, by rfl⟩ : syracuseStep 2315843 = 3473765) B3473765
theorem B2315873 : Blo 1543469 2315873 := bstep (se 2 (by rfl) ⟨868452, by rfl⟩ : syracuseStep 2315873 = 1736905) B1736905
theorem B2315891 : Blo 1543469 2315891 := bstep (se 1 (by rfl) ⟨1736918, by rfl⟩ : syracuseStep 2315891 = 3473837) B3473837
theorem B2315921 : Blo 1543469 2315921 := bstep (se 2 (by rfl) ⟨868470, by rfl⟩ : syracuseStep 2315921 = 1736941) B1736941
theorem B2315939 : Blo 1543469 2315939 := bstep (se 1 (by rfl) ⟨1736954, by rfl⟩ : syracuseStep 2315939 = 3473909) B3473909
theorem B2315969 : Blo 1543469 2315969 := bstep (se 2 (by rfl) ⟨868488, by rfl⟩ : syracuseStep 2315969 = 1736977) B1736977
theorem B8345285 : Blo 1543469 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B2315987 : Blo 1543469 2315987 := bstep (se 1 (by rfl) ⟨1736990, by rfl⟩ : syracuseStep 2315987 = 3473981) B3473981
theorem B14096099 : Blo 1543469 14096099 := bstep (se 1 (by rfl) ⟨10572074, by rfl⟩ : syracuseStep 14096099 = 21144149) B21144149
theorem B4396781 : Blo 1543469 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B2316017 : Blo 1543469 2316017 := bstep (se 2 (by rfl) ⟨868506, by rfl⟩ : syracuseStep 2316017 = 1737013) B1737013
theorem B2316035 : Blo 1543469 2316035 := bstep (se 1 (by rfl) ⟨1737026, by rfl⟩ : syracuseStep 2316035 = 3474053) B3474053
theorem B1955603 : Blo 1543469 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B2316065 : Blo 1543469 2316065 := bstep (se 2 (by rfl) ⟨868524, by rfl⟩ : syracuseStep 2316065 = 1737049) B1737049
theorem B2316083 : Blo 1543469 2316083 := bstep (se 1 (by rfl) ⟨1737062, by rfl⟩ : syracuseStep 2316083 = 3474125) B3474125
theorem B2316113 : Blo 1543469 2316113 := bstep (se 2 (by rfl) ⟨868542, by rfl⟩ : syracuseStep 2316113 = 1737085) B1737085
theorem B2316131 : Blo 1543469 2316131 := bstep (se 1 (by rfl) ⟨1737098, by rfl⟩ : syracuseStep 2316131 = 3474197) B3474197
theorem B3708785 : Blo 1543469 3708785 := bstep (se 2 (by rfl) ⟨1390794, by rfl⟩ : syracuseStep 3708785 = 2781589) B2781589
theorem B2783089 : Blo 1543469 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B2316161 : Blo 1543469 2316161 := bstep (se 2 (by rfl) ⟨868560, by rfl⟩ : syracuseStep 2316161 = 1737121) B1737121
theorem B7821197 : Blo 1543469 7821197 := bstep (se 3 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 7821197 = 2932949) B2932949
theorem B2316179 : Blo 1543469 2316179 := bstep (se 1 (by rfl) ⟨1737134, by rfl⟩ : syracuseStep 2316179 = 3474269) B3474269
theorem B2316209 : Blo 1543469 2316209 := bstep (se 2 (by rfl) ⟨868578, by rfl⟩ : syracuseStep 2316209 = 1737157) B1737157
theorem B2316227 : Blo 1543469 2316227 := bstep (se 1 (by rfl) ⟨1737170, by rfl⟩ : syracuseStep 2316227 = 3474341) B3474341
theorem B2316257 : Blo 1543469 2316257 := bstep (se 2 (by rfl) ⟨868596, by rfl⟩ : syracuseStep 2316257 = 1737193) B1737193
theorem B8353763 : Blo 1543469 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B2316275 : Blo 1543469 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B2316305 : Blo 1543469 2316305 := bstep (se 2 (by rfl) ⟨868614, by rfl⟩ : syracuseStep 2316305 = 1737229) B1737229
theorem B2316323 : Blo 1543469 2316323 := bstep (se 1 (by rfl) ⟨1737242, by rfl⟩ : syracuseStep 2316323 = 3474485) B3474485
theorem B4945969 : Blo 1543469 4945969 := bstep (se 2 (by rfl) ⟨1854738, by rfl⟩ : syracuseStep 4945969 = 3709477) B3709477
theorem B35665973 : Blo 1543469 35665973 := bstep (se 5 (by rfl) ⟨1671842, by rfl⟩ : syracuseStep 35665973 = 3343685) B3343685
theorem B2316353 : Blo 1543469 2316353 := bstep (se 2 (by rfl) ⟨868632, by rfl⟩ : syracuseStep 2316353 = 1737265) B1737265
theorem B2930755 : Blo 1543469 2930755 := bstep (se 1 (by rfl) ⟨2198066, by rfl⟩ : syracuseStep 2930755 = 4396133) B4396133
theorem B2316371 : Blo 1543469 2316371 := bstep (se 1 (by rfl) ⟨1737278, by rfl⟩ : syracuseStep 2316371 = 3474557) B3474557
theorem B2316401 : Blo 1543469 2316401 := bstep (se 2 (by rfl) ⟨868650, by rfl⟩ : syracuseStep 2316401 = 1737301) B1737301
theorem B2316419 : Blo 1543469 2316419 := bstep (se 1 (by rfl) ⟨1737314, by rfl⟩ : syracuseStep 2316419 = 3474629) B3474629
theorem B6600845 : Blo 1543469 6600845 := bstep (se 3 (by rfl) ⟨1237658, by rfl⟩ : syracuseStep 6600845 = 2475317) B2475317
theorem B2087057 : Blo 1543469 2087057 := bstep (se 2 (by rfl) ⟨782646, by rfl⟩ : syracuseStep 2087057 = 1565293) B1565293
theorem B2316449 : Blo 1543469 2316449 := bstep (se 2 (by rfl) ⟨868668, by rfl⟩ : syracuseStep 2316449 = 1737337) B1737337
theorem B2316467 : Blo 1543469 2316467 := bstep (se 1 (by rfl) ⟨1737350, by rfl⟩ : syracuseStep 2316467 = 3474701) B3474701
theorem B2316497 : Blo 1543469 2316497 := bstep (se 2 (by rfl) ⟨868686, by rfl⟩ : syracuseStep 2316497 = 1737373) B1737373
theorem B2316515 : Blo 1543469 2316515 := bstep (se 1 (by rfl) ⟨1737386, by rfl⟩ : syracuseStep 2316515 = 3474773) B3474773
theorem B11729123 : Blo 1543469 11729123 := bstep (se 1 (by rfl) ⟨8796842, by rfl⟩ : syracuseStep 11729123 = 17593685) B17593685
theorem B2316545 : Blo 1543469 2316545 := bstep (se 2 (by rfl) ⟨868704, by rfl⟩ : syracuseStep 2316545 = 1737409) B1737409
theorem B2316563 : Blo 1543469 2316563 := bstep (se 1 (by rfl) ⟨1737422, by rfl⟩ : syracuseStep 2316563 = 3474845) B3474845
theorem B2316593 : Blo 1543469 2316593 := bstep (se 2 (by rfl) ⟨868722, by rfl⟩ : syracuseStep 2316593 = 1737445) B1737445
theorem B9394481 : Blo 1543469 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B2316611 : Blo 1543469 2316611 := bstep (se 1 (by rfl) ⟨1737458, by rfl⟩ : syracuseStep 2316611 = 3474917) B3474917
theorem B2316641 : Blo 1543469 2316641 := bstep (se 2 (by rfl) ⟨868740, by rfl⟩ : syracuseStep 2316641 = 1737481) B1737481
theorem B2316659 : Blo 1543469 2316659 := bstep (se 1 (by rfl) ⟨1737494, by rfl⟩ : syracuseStep 2316659 = 3474989) B3474989
theorem B2972035 : Blo 1543469 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B2316689 : Blo 1543469 2316689 := bstep (se 2 (by rfl) ⟨868758, by rfl⟩ : syracuseStep 2316689 = 1737517) B1737517
theorem B2316707 : Blo 1543469 2316707 := bstep (se 1 (by rfl) ⟨1737530, by rfl⟩ : syracuseStep 2316707 = 3475061) B3475061
theorem B2316737 : Blo 1543469 2316737 := bstep (se 2 (by rfl) ⟨868776, by rfl⟩ : syracuseStep 2316737 = 1737553) B1737553
theorem B2316755 : Blo 1543469 2316755 := bstep (se 1 (by rfl) ⟨1737566, by rfl⟩ : syracuseStep 2316755 = 3475133) B3475133
theorem B2316785 : Blo 1543469 2316785 := bstep (se 2 (by rfl) ⟨868794, by rfl⟩ : syracuseStep 2316785 = 1737589) B1737589
theorem B2677249 : Blo 1543469 2677249 := bstep (se 2 (by rfl) ⟨1003968, by rfl⟩ : syracuseStep 2677249 = 2007937) B2007937
theorem B2931203 : Blo 1543469 2931203 := bstep (se 1 (by rfl) ⟨2198402, by rfl⟩ : syracuseStep 2931203 = 4396805) B4396805
theorem B2316803 : Blo 1543469 2316803 := bstep (se 1 (by rfl) ⟨1737602, by rfl⟩ : syracuseStep 2316803 = 3475205) B3475205
theorem B2316833 : Blo 1543469 2316833 := bstep (se 2 (by rfl) ⟨868812, by rfl⟩ : syracuseStep 2316833 = 1737625) B1737625
theorem B8796707 : Blo 1543469 8796707 := bstep (se 1 (by rfl) ⟨6597530, by rfl⟩ : syracuseStep 8796707 = 13195061) B13195061
theorem B5863985 : Blo 1543469 5863985 := bstep (se 2 (by rfl) ⟨2198994, by rfl⟩ : syracuseStep 5863985 = 4397989) B4397989
theorem B2316851 : Blo 1543469 2316851 := bstep (se 1 (by rfl) ⟨1737638, by rfl⟩ : syracuseStep 2316851 = 3475277) B3475277
theorem B2316881 : Blo 1543469 2316881 := bstep (se 2 (by rfl) ⟨868830, by rfl⟩ : syracuseStep 2316881 = 1737661) B1737661
theorem B2316899 : Blo 1543469 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B2316929 : Blo 1543469 2316929 := bstep (se 2 (by rfl) ⟨868848, by rfl⟩ : syracuseStep 2316929 = 1737697) B1737697
theorem B2316947 : Blo 1543469 2316947 := bstep (se 1 (by rfl) ⟨1737710, by rfl⟩ : syracuseStep 2316947 = 3475421) B3475421
theorem B2316977 : Blo 1543469 2316977 := bstep (se 2 (by rfl) ⟨868866, by rfl⟩ : syracuseStep 2316977 = 1737733) B1737733
theorem B2316995 : Blo 1543469 2316995 := bstep (se 1 (by rfl) ⟨1737746, by rfl⟩ : syracuseStep 2316995 = 3475493) B3475493
theorem B8354501 : Blo 1543469 8354501 := bstep (se 4 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 8354501 = 1566469) B1566469
theorem B4397773 : Blo 1543469 4397773 := bstep (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) B1649165
theorem B2783953 : Blo 1543469 2783953 := bstep (se 2 (by rfl) ⟨1043982, by rfl⟩ : syracuseStep 2783953 = 2087965) B2087965
theorem B2317025 : Blo 1543469 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B3521251 : Blo 1543469 3521251 := bstep (se 1 (by rfl) ⟨2640938, by rfl⟩ : syracuseStep 3521251 = 5281877) B5281877
theorem B2317043 : Blo 1543469 2317043 := bstep (se 1 (by rfl) ⟨1737782, by rfl⟩ : syracuseStep 2317043 = 3475565) B3475565
theorem B2317073 : Blo 1543469 2317073 := bstep (se 2 (by rfl) ⟨868902, by rfl⟩ : syracuseStep 2317073 = 1737805) B1737805
theorem B2931491 : Blo 1543469 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B2317091 : Blo 1543469 2317091 := bstep (se 1 (by rfl) ⟨1737818, by rfl⟩ : syracuseStep 2317091 = 3475637) B3475637
theorem B2317121 : Blo 1543469 2317121 := bstep (se 2 (by rfl) ⟨868920, by rfl⟩ : syracuseStep 2317121 = 1737841) B1737841
theorem B2317139 : Blo 1543469 2317139 := bstep (se 1 (by rfl) ⟨1737854, by rfl⟩ : syracuseStep 2317139 = 3475709) B3475709
theorem B2317169 : Blo 1543469 2317169 := bstep (se 2 (by rfl) ⟨868938, by rfl⟩ : syracuseStep 2317169 = 1737877) B1737877
theorem B5569393 : Blo 1543469 5569393 := bstep (se 2 (by rfl) ⟨2088522, by rfl⟩ : syracuseStep 5569393 = 4177045) B4177045
theorem B2317187 : Blo 1543469 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B2317217 : Blo 1543469 2317217 := bstep (se 2 (by rfl) ⟨868956, by rfl⟩ : syracuseStep 2317217 = 1737913) B1737913
theorem B2317235 : Blo 1543469 2317235 := bstep (se 1 (by rfl) ⟨1737926, by rfl⟩ : syracuseStep 2317235 = 3475853) B3475853
theorem B2317265 : Blo 1543469 2317265 := bstep (se 2 (by rfl) ⟨868974, by rfl⟩ : syracuseStep 2317265 = 1737949) B1737949
theorem B2317283 : Blo 1543469 2317283 := bstep (se 1 (by rfl) ⟨1737962, by rfl⟩ : syracuseStep 2317283 = 3475925) B3475925
theorem B2472947 : Blo 1543469 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B2317313 : Blo 1543469 2317313 := bstep (se 2 (by rfl) ⟨868992, by rfl⟩ : syracuseStep 2317313 = 1737985) B1737985
theorem B2317331 : Blo 1543469 2317331 := bstep (se 1 (by rfl) ⟨1737998, by rfl⟩ : syracuseStep 2317331 = 3475997) B3475997
theorem B2317361 : Blo 1543469 2317361 := bstep (se 2 (by rfl) ⟨869010, by rfl⟩ : syracuseStep 2317361 = 1738021) B1738021
theorem B2317379 : Blo 1543469 2317379 := bstep (se 1 (by rfl) ⟨1738034, by rfl⟩ : syracuseStep 2317379 = 3476069) B3476069
theorem B2317409 : Blo 1543469 2317409 := bstep (se 2 (by rfl) ⟨869028, by rfl⟩ : syracuseStep 2317409 = 1738057) B1738057
theorem B19799153 : Blo 1543469 19799153 := bstep (se 2 (by rfl) ⟨7424682, by rfl⟩ : syracuseStep 19799153 = 14849365) B14849365
theorem B2317427 : Blo 1543469 2317427 := bstep (se 1 (by rfl) ⟨1738070, by rfl⟩ : syracuseStep 2317427 = 3476141) B3476141
theorem B4947085 : Blo 1543469 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B2317457 : Blo 1543469 2317457 := bstep (se 2 (by rfl) ⟨869046, by rfl⟩ : syracuseStep 2317457 = 1738093) B1738093
theorem B2317475 : Blo 1543469 2317475 := bstep (se 1 (by rfl) ⟨1738106, by rfl⟩ : syracuseStep 2317475 = 3476213) B3476213
theorem B2473139 : Blo 1543469 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B2317505 : Blo 1543469 2317505 := bstep (se 2 (by rfl) ⟨869064, by rfl⟩ : syracuseStep 2317505 = 1738129) B1738129
theorem B4947149 : Blo 1543469 4947149 := bstep (se 3 (by rfl) ⟨927590, by rfl⟩ : syracuseStep 4947149 = 1855181) B1855181
theorem B2317523 : Blo 1543469 2317523 := bstep (se 1 (by rfl) ⟨1738142, by rfl⟩ : syracuseStep 2317523 = 3476285) B3476285
theorem B14097635 : Blo 1543469 14097635 := bstep (se 1 (by rfl) ⟨10573226, by rfl⟩ : syracuseStep 14097635 = 21146453) B21146453
theorem B5209325 : Blo 1543469 5209325 := bstep (se 3 (by rfl) ⟨976748, by rfl⟩ : syracuseStep 5209325 = 1953497) B1953497
theorem B4455661 : Blo 1543469 4455661 := bstep (se 3 (by rfl) ⟨835436, by rfl⟩ : syracuseStep 4455661 = 1670873) B1670873
theorem B2317553 : Blo 1543469 2317553 := bstep (se 2 (by rfl) ⟨869082, by rfl⟩ : syracuseStep 2317553 = 1738165) B1738165
theorem B3300593 : Blo 1543469 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B2317571 : Blo 1543469 2317571 := bstep (se 1 (by rfl) ⟨1738178, by rfl⟩ : syracuseStep 2317571 = 3476357) B3476357
theorem B2317601 : Blo 1543469 2317601 := bstep (se 2 (by rfl) ⟨869100, by rfl⟩ : syracuseStep 2317601 = 1738201) B1738201
theorem B5209379 : Blo 1543469 5209379 := bstep (se 1 (by rfl) ⟨3907034, by rfl⟩ : syracuseStep 5209379 = 7814069) B7814069
theorem B7044401 : Blo 1543469 7044401 := bstep (se 2 (by rfl) ⟨2641650, by rfl⟩ : syracuseStep 7044401 = 5283301) B5283301
theorem B2473267 : Blo 1543469 2473267 := bstep (se 1 (by rfl) ⟨1854950, by rfl⟩ : syracuseStep 2473267 = 3709901) B3709901
theorem B2317619 : Blo 1543469 2317619 := bstep (se 1 (by rfl) ⟨1738214, by rfl⟩ : syracuseStep 2317619 = 3476429) B3476429
theorem B16932149 : Blo 1543469 16932149 := bstep (se 5 (by rfl) ⟨793694, by rfl⟩ : syracuseStep 16932149 = 1587389) B1587389
theorem B2317649 : Blo 1543469 2317649 := bstep (se 2 (by rfl) ⟨869118, by rfl⟩ : syracuseStep 2317649 = 1738237) B1738237
theorem B2317667 : Blo 1543469 2317667 := bstep (se 1 (by rfl) ⟨1738250, by rfl⟩ : syracuseStep 2317667 = 3476501) B3476501
theorem B2317697 : Blo 1543469 2317697 := bstep (se 2 (by rfl) ⟨869136, by rfl⟩ : syracuseStep 2317697 = 1738273) B1738273
theorem B2317715 : Blo 1543469 2317715 := bstep (se 1 (by rfl) ⟨1738286, by rfl⟩ : syracuseStep 2317715 = 3476573) B3476573
theorem B2088355 : Blo 1543469 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B2317745 : Blo 1543469 2317745 := bstep (se 2 (by rfl) ⟨869154, by rfl⟩ : syracuseStep 2317745 = 1738309) B1738309
theorem B2317763 : Blo 1543469 2317763 := bstep (se 1 (by rfl) ⟨1738322, by rfl⟩ : syracuseStep 2317763 = 3476645) B3476645
theorem B3907025 : Blo 1543469 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B2317793 : Blo 1543469 2317793 := bstep (se 2 (by rfl) ⟨869172, by rfl⟩ : syracuseStep 2317793 = 1738345) B1738345
theorem B2317811 : Blo 1543469 2317811 := bstep (se 1 (by rfl) ⟨1738358, by rfl⟩ : syracuseStep 2317811 = 3476717) B3476717
theorem B3907075 : Blo 1543469 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B2317841 : Blo 1543469 2317841 := bstep (se 2 (by rfl) ⟨869190, by rfl⟩ : syracuseStep 2317841 = 1738381) B1738381
theorem B8347171 : Blo 1543469 8347171 := bstep (se 1 (by rfl) ⟨6260378, by rfl⟩ : syracuseStep 8347171 = 12520757) B12520757
theorem B2317859 : Blo 1543469 2317859 := bstep (se 1 (by rfl) ⟨1738394, by rfl⟩ : syracuseStep 2317859 = 3476789) B3476789
theorem B5209649 : Blo 1543469 5209649 := bstep (se 2 (by rfl) ⟨1953618, by rfl⟩ : syracuseStep 5209649 = 3907237) B3907237
theorem B2317889 : Blo 1543469 2317889 := bstep (se 2 (by rfl) ⟨869208, by rfl⟩ : syracuseStep 2317889 = 1738417) B1738417
theorem B2317907 : Blo 1543469 2317907 := bstep (se 1 (by rfl) ⟨1738430, by rfl⟩ : syracuseStep 2317907 = 3476861) B3476861
theorem B3473009 : Blo 1543469 3473009 := bstep (se 2 (by rfl) ⟨1302378, by rfl⟩ : syracuseStep 3473009 = 2604757) B2604757
theorem B11886193 : Blo 1543469 11886193 := bstep (se 2 (by rfl) ⟨4457322, by rfl⟩ : syracuseStep 11886193 = 8914645) B8914645
theorem B2317937 : Blo 1543469 2317937 := bstep (se 2 (by rfl) ⟨869226, by rfl⟩ : syracuseStep 2317937 = 1738453) B1738453
theorem B3473027 : Blo 1543469 3473027 := bstep (se 1 (by rfl) ⟨2604770, by rfl⟩ : syracuseStep 3473027 = 5209541) B5209541
theorem B2317955 : Blo 1543469 2317955 := bstep (se 1 (by rfl) ⟨1738466, by rfl⟩ : syracuseStep 2317955 = 3476933) B3476933
theorem B17587853 : Blo 1543469 17587853 := bstep (se 3 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 17587853 = 6595445) B6595445
theorem B3907217 : Blo 1543469 3907217 := bstep (se 2 (by rfl) ⟨1465206, by rfl⟩ : syracuseStep 3907217 = 2930413) B2930413
theorem B2317985 : Blo 1543469 2317985 := bstep (se 2 (by rfl) ⟨869244, by rfl⟩ : syracuseStep 2317985 = 1738489) B1738489
theorem B2318003 : Blo 1543469 2318003 := bstep (se 1 (by rfl) ⟨1738502, by rfl⟩ : syracuseStep 2318003 = 3477005) B3477005
theorem B2604737 : Blo 1543469 2604737 := bstep (se 2 (by rfl) ⟨976776, by rfl⟩ : syracuseStep 2604737 = 1953553) B1953553
theorem B7421645 : Blo 1543469 7421645 := bstep (se 3 (by rfl) ⟨1391558, by rfl⟩ : syracuseStep 7421645 = 2783117) B2783117
theorem B2932433 : Blo 1543469 2932433 := bstep (se 2 (by rfl) ⟨1099662, by rfl⟩ : syracuseStep 2932433 = 2199325) B2199325
theorem B2318033 : Blo 1543469 2318033 := bstep (se 2 (by rfl) ⟨869262, by rfl⟩ : syracuseStep 2318033 = 1738525) B1738525
theorem B1736419 : Blo 1543469 1736419 := bstep (se 1 (by rfl) ⟨1302314, by rfl⟩ : syracuseStep 1736419 = 2604629) B2604629
theorem B2318051 : Blo 1543469 2318051 := bstep (se 1 (by rfl) ⟨1738538, by rfl⟩ : syracuseStep 2318051 = 3477077) B3477077
theorem B2318081 : Blo 1543469 2318081 := bstep (se 2 (by rfl) ⟨869280, by rfl⟩ : syracuseStep 2318081 = 1738561) B1738561
theorem B2318099 : Blo 1543469 2318099 := bstep (se 1 (by rfl) ⟨1738574, by rfl⟩ : syracuseStep 2318099 = 3477149) B3477149
theorem B2318129 : Blo 1543469 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B2604865 : Blo 1543469 2604865 := bstep (se 2 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 2604865 = 1953649) B1953649
theorem B2318147 : Blo 1543469 2318147 := bstep (se 1 (by rfl) ⟨1738610, by rfl⟩ : syracuseStep 2318147 = 3477221) B3477221
theorem B2318177 : Blo 1543469 2318177 := bstep (se 2 (by rfl) ⟨869316, by rfl⟩ : syracuseStep 2318177 = 1738633) B1738633
theorem B2604899 : Blo 1543469 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B13188977 : Blo 1543469 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B1736563 : Blo 1543469 1736563 := bstep (se 1 (by rfl) ⟨1302422, by rfl⟩ : syracuseStep 1736563 = 2604845) B2604845
theorem B2318195 : Blo 1543469 2318195 := bstep (se 1 (by rfl) ⟨1738646, by rfl⟩ : syracuseStep 2318195 = 3477293) B3477293
theorem B1785731 : Blo 1543469 1785731 := bstep (se 1 (by rfl) ⟨1339298, by rfl⟩ : syracuseStep 1785731 = 2678597) B2678597
theorem B3473297 : Blo 1543469 3473297 := bstep (se 2 (by rfl) ⟨1302486, by rfl⟩ : syracuseStep 3473297 = 2604973) B2604973
theorem B3473315 : Blo 1543469 3473315 := bstep (se 1 (by rfl) ⟨2604986, by rfl⟩ : syracuseStep 3473315 = 5209973) B5209973
theorem B2473907 : Blo 1543469 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B3710929 : Blo 1543469 3710929 := bstep (se 2 (by rfl) ⟨1391598, by rfl⟩ : syracuseStep 3710929 = 2783197) B2783197
theorem B2605027 : Blo 1543469 2605027 := bstep (se 1 (by rfl) ⟨1953770, by rfl⟩ : syracuseStep 2605027 = 3907541) B3907541
theorem B5865443 : Blo 1543469 5865443 := bstep (se 1 (by rfl) ⟨4399082, by rfl⟩ : syracuseStep 5865443 = 8798165) B8798165
theorem B5210135 : Blo 1543469 5210135 := bstep (se 1 (by rfl) ⟨3907601, by rfl⟩ : syracuseStep 5210135 = 7815203) B7815203
theorem B2605081 : Blo 1543469 2605081 := bstep (se 2 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 2605081 = 1953811) B1953811
theorem B3473459 : Blo 1543469 3473459 := bstep (se 1 (by rfl) ⟨2605094, by rfl⟩ : syracuseStep 3473459 = 5210189) B5210189
theorem B6594625 : Blo 1543469 6594625 := bstep (se 2 (by rfl) ⟨2472984, by rfl⟩ : syracuseStep 6594625 = 4945969) B4945969
theorem B1736779 : Blo 1543469 1736779 := bstep (se 1 (by rfl) ⟨1302584, by rfl⟩ : syracuseStep 1736779 = 2605169) B2605169
theorem B3473495 : Blo 1543469 3473495 := bstep (se 1 (by rfl) ⟨2605121, by rfl⟩ : syracuseStep 3473495 = 5210243) B5210243
theorem B3907673 : Blo 1543469 3907673 := bstep (se 2 (by rfl) ⟨1465377, by rfl⟩ : syracuseStep 3907673 = 2930755) B2930755
theorem B2678873 : Blo 1543469 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B1736887 : Blo 1543469 1736887 := bstep (se 1 (by rfl) ⟨1302665, by rfl⟩ : syracuseStep 1736887 = 2605331) B2605331
theorem B2973953 : Blo 1543469 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B3473675 : Blo 1543469 3473675 := bstep (se 1 (by rfl) ⟨2605256, by rfl⟩ : syracuseStep 3473675 = 5210513) B5210513
theorem B2933003 : Blo 1543469 2933003 := bstep (se 1 (by rfl) ⟨2199752, by rfl⟩ : syracuseStep 2933003 = 4399505) B4399505
theorem B3473729 : Blo 1543469 3473729 := bstep (se 2 (by rfl) ⟨1302648, by rfl⟩ : syracuseStep 3473729 = 2605297) B2605297
theorem B1737067 : Blo 1543469 1737067 := bstep (se 1 (by rfl) ⟨1302800, by rfl⟩ : syracuseStep 1737067 = 2605601) B2605601
theorem B1671575 : Blo 1543469 1671575 := bstep (se 1 (by rfl) ⟨1253681, by rfl⟩ : syracuseStep 1671575 = 2507363) B2507363
theorem B2933185 : Blo 1543469 2933185 := bstep (se 2 (by rfl) ⟨1099944, by rfl⟩ : syracuseStep 2933185 = 2199889) B2199889
theorem B1737175 : Blo 1543469 1737175 := bstep (se 1 (by rfl) ⟨1302881, by rfl⟩ : syracuseStep 1737175 = 2605763) B2605763
theorem B3473945 : Blo 1543469 3473945 := bstep (se 2 (by rfl) ⟨1302729, by rfl⟩ : syracuseStep 3473945 = 2605459) B2605459
theorem B5210675 : Blo 1543469 5210675 := bstep (se 1 (by rfl) ⟨3908006, by rfl⟩ : syracuseStep 5210675 = 7816013) B7816013
theorem B2605655 : Blo 1543469 2605655 := bstep (se 1 (by rfl) ⟨1954241, by rfl⟩ : syracuseStep 2605655 = 3908483) B3908483
theorem B3474035 : Blo 1543469 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B1737355 : Blo 1543469 1737355 := bstep (se 1 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 1737355 = 2606033) B2606033
theorem B3474071 : Blo 1543469 3474071 := bstep (se 1 (by rfl) ⟨2605553, by rfl⟩ : syracuseStep 3474071 = 5211107) B5211107
theorem B12526231 : Blo 1543469 12526231 := bstep (se 1 (by rfl) ⟨9394673, by rfl⟩ : syracuseStep 12526231 = 18789347) B18789347
theorem B2605783 : Blo 1543469 2605783 := bstep (se 1 (by rfl) ⟨1954337, by rfl⟩ : syracuseStep 2605783 = 3908675) B3908675
theorem B40682225 : Blo 1543469 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B1737463 : Blo 1543469 1737463 := bstep (se 1 (by rfl) ⟨1303097, by rfl⟩ : syracuseStep 1737463 = 2606195) B2606195
theorem B25051949 : Blo 1543469 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B5210945 : Blo 1543469 5210945 := bstep (se 2 (by rfl) ⟨1954104, by rfl⟩ : syracuseStep 5210945 = 3908209) B3908209
theorem B3474251 : Blo 1543469 3474251 := bstep (se 1 (by rfl) ⟨2605688, by rfl⟩ : syracuseStep 3474251 = 5211377) B5211377
theorem B3474305 : Blo 1543469 3474305 := bstep (se 2 (by rfl) ⟨1302864, by rfl⟩ : syracuseStep 3474305 = 2605729) B2605729
theorem B2933633 : Blo 1543469 2933633 := bstep (se 2 (by rfl) ⟨1100112, by rfl⟩ : syracuseStep 2933633 = 2200225) B2200225
theorem B13190039 : Blo 1543469 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B1737643 : Blo 1543469 1737643 := bstep (se 1 (by rfl) ⟨1303232, by rfl⟩ : syracuseStep 1737643 = 2606465) B2606465
theorem B1737751 : Blo 1543469 1737751 := bstep (se 1 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 1737751 = 2606627) B2606627
theorem B3474521 : Blo 1543469 3474521 := bstep (se 2 (by rfl) ⟨1302945, by rfl⟩ : syracuseStep 3474521 = 2605891) B2605891
theorem B5563523 : Blo 1543469 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B5866627 : Blo 1543469 5866627 := bstep (se 1 (by rfl) ⟨4399970, by rfl⟩ : syracuseStep 5866627 = 8799941) B8799941
theorem B9397399 : Blo 1543469 9397399 := bstep (se 1 (by rfl) ⟨7048049, by rfl⟩ : syracuseStep 9397399 = 14096099) B14096099
theorem B3474611 : Blo 1543469 3474611 := bstep (se 1 (by rfl) ⟨2605958, by rfl⟩ : syracuseStep 3474611 = 5211917) B5211917
theorem B1737931 : Blo 1543469 1737931 := bstep (se 1 (by rfl) ⟨1303448, by rfl⟩ : syracuseStep 1737931 = 2606897) B2606897
theorem B3474647 : Blo 1543469 3474647 := bstep (se 1 (by rfl) ⟨2605985, by rfl⟩ : syracuseStep 3474647 = 5211971) B5211971
theorem B2933975 : Blo 1543469 2933975 := bstep (se 1 (by rfl) ⟨2200481, by rfl⟩ : syracuseStep 2933975 = 4400963) B4400963
theorem B1738039 : Blo 1543469 1738039 := bstep (se 1 (by rfl) ⟨1303529, by rfl⟩ : syracuseStep 1738039 = 2607059) B2607059
theorem B2606411 : Blo 1543469 2606411 := bstep (se 1 (by rfl) ⟨1954808, by rfl⟩ : syracuseStep 2606411 = 3909617) B3909617
theorem B5211485 : Blo 1543469 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B3474827 : Blo 1543469 3474827 := bstep (se 1 (by rfl) ⟨2606120, by rfl⟩ : syracuseStep 3474827 = 5212241) B5212241
theorem B5866931 : Blo 1543469 5866931 := bstep (se 1 (by rfl) ⟨4400198, by rfl⟩ : syracuseStep 5866931 = 8800397) B8800397
theorem B4400563 : Blo 1543469 4400563 := bstep (se 1 (by rfl) ⟨3300422, by rfl⟩ : syracuseStep 4400563 = 6600845) B6600845
theorem B3474881 : Blo 1543469 3474881 := bstep (se 2 (by rfl) ⟨1303080, by rfl⟩ : syracuseStep 3474881 = 2606161) B2606161
theorem B2606539 : Blo 1543469 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B1738219 : Blo 1543469 1738219 := bstep (se 1 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 1738219 = 2607329) B2607329
theorem B6596113 : Blo 1543469 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B11732525 : Blo 1543469 11732525 := bstep (se 3 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 11732525 = 4399697) B4399697
theorem B1738327 : Blo 1543469 1738327 := bstep (se 1 (by rfl) ⟨1303745, by rfl⟩ : syracuseStep 1738327 = 2607491) B2607491
theorem B2606681 : Blo 1543469 2606681 := bstep (se 2 (by rfl) ⟨977505, by rfl⟩ : syracuseStep 2606681 = 1955011) B1955011
theorem B5940881 : Blo 1543469 5940881 := bstep (se 2 (by rfl) ⟨2227830, by rfl⟩ : syracuseStep 5940881 = 4455661) B4455661
theorem B3475097 : Blo 1543469 3475097 := bstep (se 2 (by rfl) ⟨1303161, by rfl⟩ : syracuseStep 3475097 = 2606323) B2606323
theorem B3909323 : Blo 1543469 3909323 := bstep (se 1 (by rfl) ⟨2931992, by rfl⟩ : syracuseStep 3909323 = 5863985) B5863985
theorem B2606809 : Blo 1543469 2606809 := bstep (se 2 (by rfl) ⟨977553, by rfl⟩ : syracuseStep 2606809 = 1955107) B1955107
theorem B3475187 : Blo 1543469 3475187 := bstep (se 1 (by rfl) ⟨2606390, by rfl⟩ : syracuseStep 3475187 = 5212781) B5212781
theorem B1738507 : Blo 1543469 1738507 := bstep (se 1 (by rfl) ⟨1303880, by rfl⟩ : syracuseStep 1738507 = 2607761) B2607761
theorem B3475223 : Blo 1543469 3475223 := bstep (se 1 (by rfl) ⟨2606417, by rfl⟩ : syracuseStep 3475223 = 5212835) B5212835
theorem B8791901 : Blo 1543469 8791901 := bstep (se 3 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 8791901 = 3296963) B3296963
theorem B26388341 : Blo 1543469 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B1738615 : Blo 1543469 1738615 := bstep (se 1 (by rfl) ⟨1303961, by rfl⟩ : syracuseStep 1738615 = 2607923) B2607923
theorem B3475403 : Blo 1543469 3475403 := bstep (se 1 (by rfl) ⟨2606552, by rfl⟩ : syracuseStep 3475403 = 5213105) B5213105
theorem B11724749 : Blo 1543469 11724749 := bstep (se 3 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 11724749 = 4396781) B4396781
theorem B1648631 : Blo 1543469 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B3475457 : Blo 1543469 3475457 := bstep (se 2 (by rfl) ⟨1303296, by rfl⟩ : syracuseStep 3475457 = 2606593) B2606593
theorem B5867585 : Blo 1543469 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B13199435 : Blo 1543469 13199435 := bstep (se 1 (by rfl) ⟨9899576, by rfl⟩ : syracuseStep 13199435 = 19799153) B19799153
theorem B7817309 : Blo 1543469 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B1648759 : Blo 1543469 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B9398423 : Blo 1543469 9398423 := bstep (se 1 (by rfl) ⟨7048817, by rfl⟩ : syracuseStep 9398423 = 14097635) B14097635
theorem B4696267 : Blo 1543469 4696267 := bstep (se 1 (by rfl) ⟨3522200, by rfl⟩ : syracuseStep 4696267 = 7044401) B7044401
theorem B3475673 : Blo 1543469 3475673 := bstep (se 2 (by rfl) ⟨1303377, by rfl⟩ : syracuseStep 3475673 = 2606755) B2606755
theorem B2607383 : Blo 1543469 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B9890093 : Blo 1543469 9890093 := bstep (se 3 (by rfl) ⟨1854392, by rfl⟩ : syracuseStep 9890093 = 3708785) B3708785
theorem B3475763 : Blo 1543469 3475763 := bstep (se 1 (by rfl) ⟨2606822, by rfl⟩ : syracuseStep 3475763 = 5213645) B5213645
theorem B3475799 : Blo 1543469 3475799 := bstep (se 1 (by rfl) ⟨2606849, by rfl⟩ : syracuseStep 3475799 = 5213699) B5213699
theorem B4761949 : Blo 1543469 4761949 := bstep (se 3 (by rfl) ⟨892865, by rfl⟩ : syracuseStep 4761949 = 1785731) B1785731
theorem B2607511 : Blo 1543469 2607511 := bstep (se 1 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 2607511 = 3911267) B3911267
theorem B11725235 : Blo 1543469 11725235 := bstep (se 1 (by rfl) ⟨8793926, by rfl⟩ : syracuseStep 11725235 = 17587853) B17587853
theorem B5212619 : Blo 1543469 5212619 := bstep (se 1 (by rfl) ⟨3909464, by rfl⟩ : syracuseStep 5212619 = 7818929) B7818929
theorem B13560281 : Blo 1543469 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B3475979 : Blo 1543469 3475979 := bstep (se 1 (by rfl) ⟨2606984, by rfl⟩ : syracuseStep 3475979 = 5213969) B5213969
theorem B3476033 : Blo 1543469 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B8792651 : Blo 1543469 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B3910295 : Blo 1543469 3910295 := bstep (se 1 (by rfl) ⟨2932721, by rfl⟩ : syracuseStep 3910295 = 5865443) B5865443
theorem B1649323 : Blo 1543469 1649323 := bstep (se 1 (by rfl) ⟨1236992, by rfl⟩ : syracuseStep 1649323 = 2473985) B2473985
theorem B12528307 : Blo 1543469 12528307 := bstep (se 1 (by rfl) ⟨9396230, by rfl⟩ : syracuseStep 12528307 = 18792461) B18792461
theorem B5212889 : Blo 1543469 5212889 := bstep (se 2 (by rfl) ⟨1954833, by rfl⟩ : syracuseStep 5212889 = 3909667) B3909667
theorem B3476249 : Blo 1543469 3476249 := bstep (se 2 (by rfl) ⟨1303593, by rfl⟩ : syracuseStep 3476249 = 2607187) B2607187
theorem B3476339 : Blo 1543469 3476339 := bstep (se 1 (by rfl) ⟨2607254, by rfl⟩ : syracuseStep 3476339 = 5214509) B5214509
theorem B3476375 : Blo 1543469 3476375 := bstep (se 1 (by rfl) ⟨2607281, by rfl⟩ : syracuseStep 3476375 = 5214563) B5214563
theorem B1649579 : Blo 1543469 1649579 := bstep (se 1 (by rfl) ⟨1237184, by rfl⟩ : syracuseStep 1649579 = 2474369) B2474369
theorem B33852377 : Blo 1543469 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B2198539 : Blo 1543469 2198539 := bstep (se 1 (by rfl) ⟨1648904, by rfl⟩ : syracuseStep 2198539 = 3297809) B3297809
theorem B44559395 : Blo 1543469 44559395 := bstep (se 1 (by rfl) ⟨33419546, by rfl⟩ : syracuseStep 44559395 = 66839093) B66839093
theorem B5565485 : Blo 1543469 5565485 := bstep (se 3 (by rfl) ⟨1043528, by rfl⟩ : syracuseStep 5565485 = 2087057) B2087057
theorem B3476555 : Blo 1543469 3476555 := bstep (se 1 (by rfl) ⟨2607416, by rfl⟩ : syracuseStep 3476555 = 5214833) B5214833
theorem B3476609 : Blo 1543469 3476609 := bstep (se 2 (by rfl) ⟨1303728, by rfl⟩ : syracuseStep 3476609 = 2607457) B2607457
theorem B28183733 : Blo 1543469 28183733 := bstep (se 5 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 28183733 = 2642225) B2642225
theorem B3296459 : Blo 1543469 3296459 := bstep (se 1 (by rfl) ⟨2472344, by rfl⟩ : syracuseStep 3296459 = 4944689) B4944689
theorem B7048471 : Blo 1543469 7048471 := bstep (se 1 (by rfl) ⟨5286353, by rfl⟩ : syracuseStep 7048471 = 10572707) B10572707
theorem B3132695 : Blo 1543469 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B8801581 : Blo 1543469 8801581 := bstep (se 3 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 8801581 = 3300593) B3300593
theorem B3910963 : Blo 1543469 3910963 := bstep (se 1 (by rfl) ⟨2933222, by rfl⟩ : syracuseStep 3910963 = 5866445) B5866445
theorem B1543479 : Blo 1543469 1543479 := bstep (se 1 (by rfl) ⟨1157609, by rfl⟩ : syracuseStep 1543479 = 2315219) B2315219
theorem B1543499 : Blo 1543469 1543499 := bstep (se 1 (by rfl) ⟨1157624, by rfl⟩ : syracuseStep 1543499 = 2315249) B2315249
theorem B1543511 : Blo 1543469 1543511 := bstep (se 1 (by rfl) ⟨1157633, by rfl⟩ : syracuseStep 1543511 = 2315267) B2315267
theorem B3476825 : Blo 1543469 3476825 := bstep (se 2 (by rfl) ⟨1303809, by rfl⟩ : syracuseStep 3476825 = 2607619) B2607619
theorem B1543531 : Blo 1543469 1543531 := bstep (se 1 (by rfl) ⟨1157648, by rfl⟩ : syracuseStep 1543531 = 2315297) B2315297
theorem B1543543 : Blo 1543469 1543543 := bstep (se 1 (by rfl) ⟨1157657, by rfl⟩ : syracuseStep 1543543 = 2315315) B2315315
theorem B1543563 : Blo 1543469 1543563 := bstep (se 1 (by rfl) ⟨1157672, by rfl⟩ : syracuseStep 1543563 = 2315345) B2315345
theorem B1543575 : Blo 1543469 1543575 := bstep (se 1 (by rfl) ⟨1157681, by rfl⟩ : syracuseStep 1543575 = 2315363) B2315363
theorem B5213591 : Blo 1543469 5213591 := bstep (se 1 (by rfl) ⟨3910193, by rfl⟩ : syracuseStep 5213591 = 7820387) B7820387
theorem B1543595 : Blo 1543469 1543595 := bstep (se 1 (by rfl) ⟨1157696, by rfl⟩ : syracuseStep 1543595 = 2315393) B2315393
theorem B5860781 : Blo 1543469 5860781 := bstep (se 3 (by rfl) ⟨1098896, by rfl⟩ : syracuseStep 5860781 = 2197793) B2197793
theorem B3476915 : Blo 1543469 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B1543607 : Blo 1543469 1543607 := bstep (se 1 (by rfl) ⟨1157705, by rfl⟩ : syracuseStep 1543607 = 2315411) B2315411
theorem B3911105 : Blo 1543469 3911105 := bstep (se 2 (by rfl) ⟨1466664, by rfl⟩ : syracuseStep 3911105 = 2933329) B2933329
theorem B1543627 : Blo 1543469 1543627 := bstep (se 1 (by rfl) ⟨1157720, by rfl⟩ : syracuseStep 1543627 = 2315441) B2315441
theorem B1543639 : Blo 1543469 1543639 := bstep (se 1 (by rfl) ⟨1157729, by rfl⟩ : syracuseStep 1543639 = 2315459) B2315459
theorem B3476951 : Blo 1543469 3476951 := bstep (se 1 (by rfl) ⟨2607713, by rfl⟩ : syracuseStep 3476951 = 5215427) B5215427
theorem B3763673 : Blo 1543469 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B1543659 : Blo 1543469 1543659 := bstep (se 1 (by rfl) ⟨1157744, by rfl⟩ : syracuseStep 1543659 = 2315489) B2315489
theorem B1543671 : Blo 1543469 1543671 := bstep (se 1 (by rfl) ⟨1157753, by rfl⟩ : syracuseStep 1543671 = 2315507) B2315507
theorem B1543691 : Blo 1543469 1543691 := bstep (se 1 (by rfl) ⟨1157768, by rfl⟩ : syracuseStep 1543691 = 2315537) B2315537
theorem B1543703 : Blo 1543469 1543703 := bstep (se 1 (by rfl) ⟨1157777, by rfl⟩ : syracuseStep 1543703 = 2315555) B2315555
theorem B1543723 : Blo 1543469 1543723 := bstep (se 1 (by rfl) ⟨1157792, by rfl⟩ : syracuseStep 1543723 = 2315585) B2315585
theorem B1543735 : Blo 1543469 1543735 := bstep (se 1 (by rfl) ⟨1157801, by rfl⟩ : syracuseStep 1543735 = 2315603) B2315603
theorem B1543755 : Blo 1543469 1543755 := bstep (se 1 (by rfl) ⟨1157816, by rfl⟩ : syracuseStep 1543755 = 2315633) B2315633
theorem B1543767 : Blo 1543469 1543767 := bstep (se 1 (by rfl) ⟨1157825, by rfl⟩ : syracuseStep 1543767 = 2315651) B2315651
theorem B1543787 : Blo 1543469 1543787 := bstep (se 1 (by rfl) ⟨1157840, by rfl⟩ : syracuseStep 1543787 = 2315681) B2315681
theorem B1543799 : Blo 1543469 1543799 := bstep (se 1 (by rfl) ⟨1157849, by rfl⟩ : syracuseStep 1543799 = 2315699) B2315699
theorem B1543819 : Blo 1543469 1543819 := bstep (se 1 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 1543819 = 2315729) B2315729
theorem B3477131 : Blo 1543469 3477131 := bstep (se 1 (by rfl) ⟨2607848, by rfl⟩ : syracuseStep 3477131 = 5215697) B5215697
theorem B1543831 : Blo 1543469 1543831 := bstep (se 1 (by rfl) ⟨1157873, by rfl⟩ : syracuseStep 1543831 = 2315747) B2315747
theorem B1543851 : Blo 1543469 1543851 := bstep (se 1 (by rfl) ⟨1157888, by rfl⟩ : syracuseStep 1543851 = 2315777) B2315777
theorem B1543863 : Blo 1543469 1543863 := bstep (se 1 (by rfl) ⟨1157897, by rfl⟩ : syracuseStep 1543863 = 2315795) B2315795
theorem B3477185 : Blo 1543469 3477185 := bstep (se 2 (by rfl) ⟨1303944, by rfl⟩ : syracuseStep 3477185 = 2607889) B2607889
theorem B3296971 : Blo 1543469 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B1543883 : Blo 1543469 1543883 := bstep (se 1 (by rfl) ⟨1157912, by rfl⟩ : syracuseStep 1543883 = 2315825) B2315825
theorem B1543895 : Blo 1543469 1543895 := bstep (se 1 (by rfl) ⟨1157921, by rfl⟩ : syracuseStep 1543895 = 2315843) B2315843
theorem B1543915 : Blo 1543469 1543915 := bstep (se 1 (by rfl) ⟨1157936, by rfl⟩ : syracuseStep 1543915 = 2315873) B2315873
theorem B1543927 : Blo 1543469 1543927 := bstep (se 1 (by rfl) ⟨1157945, by rfl⟩ : syracuseStep 1543927 = 2315891) B2315891
theorem B14847749 : Blo 1543469 14847749 := bstep (se 4 (by rfl) ⟨1391976, by rfl⟩ : syracuseStep 14847749 = 2783953) B2783953
theorem B1543947 : Blo 1543469 1543947 := bstep (se 1 (by rfl) ⟨1157960, by rfl⟩ : syracuseStep 1543947 = 2315921) B2315921
theorem B1543959 : Blo 1543469 1543959 := bstep (se 1 (by rfl) ⟨1157969, by rfl⟩ : syracuseStep 1543959 = 2315939) B2315939
theorem B1543979 : Blo 1543469 1543979 := bstep (se 1 (by rfl) ⟨1157984, by rfl⟩ : syracuseStep 1543979 = 2315969) B2315969
theorem B1543991 : Blo 1543469 1543991 := bstep (se 1 (by rfl) ⟨1157993, by rfl⟩ : syracuseStep 1543991 = 2315987) B2315987
theorem B7425857 : Blo 1543469 7425857 := bstep (se 2 (by rfl) ⟨2784696, by rfl⟩ : syracuseStep 7425857 = 5569393) B5569393
theorem B1544011 : Blo 1543469 1544011 := bstep (se 1 (by rfl) ⟨1158008, by rfl⟩ : syracuseStep 1544011 = 2316017) B2316017
theorem B1544023 : Blo 1543469 1544023 := bstep (se 1 (by rfl) ⟨1158017, by rfl⟩ : syracuseStep 1544023 = 2316035) B2316035
theorem B18780005 : Blo 1543469 18780005 := bstep (se 4 (by rfl) ⟨1760625, by rfl⟩ : syracuseStep 18780005 = 3521251) B3521251
theorem B11726693 : Blo 1543469 11726693 := bstep (se 4 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 11726693 = 2198755) B2198755
theorem B1544043 : Blo 1543469 1544043 := bstep (se 1 (by rfl) ⟨1158032, by rfl⟩ : syracuseStep 1544043 = 2316065) B2316065
theorem B1544055 : Blo 1543469 1544055 := bstep (se 1 (by rfl) ⟨1158041, by rfl⟩ : syracuseStep 1544055 = 2316083) B2316083
theorem B1544075 : Blo 1543469 1544075 := bstep (se 1 (by rfl) ⟨1158056, by rfl⟩ : syracuseStep 1544075 = 2316113) B2316113
theorem B1544087 : Blo 1543469 1544087 := bstep (se 1 (by rfl) ⟨1158065, by rfl⟩ : syracuseStep 1544087 = 2316131) B2316131
theorem B1544107 : Blo 1543469 1544107 := bstep (se 1 (by rfl) ⟨1158080, by rfl⟩ : syracuseStep 1544107 = 2316161) B2316161
theorem B5214131 : Blo 1543469 5214131 := bstep (se 1 (by rfl) ⟨3910598, by rfl⟩ : syracuseStep 5214131 = 7821197) B7821197
theorem B1544119 : Blo 1543469 1544119 := bstep (se 1 (by rfl) ⟨1158089, by rfl⟩ : syracuseStep 1544119 = 2316179) B2316179
theorem B1544139 : Blo 1543469 1544139 := bstep (se 1 (by rfl) ⟨1158104, by rfl⟩ : syracuseStep 1544139 = 2316209) B2316209
theorem B1544151 : Blo 1543469 1544151 := bstep (se 1 (by rfl) ⟨1158113, by rfl⟩ : syracuseStep 1544151 = 2316227) B2316227
theorem B1544171 : Blo 1543469 1544171 := bstep (se 1 (by rfl) ⟨1158128, by rfl⟩ : syracuseStep 1544171 = 2316257) B2316257
theorem B1544183 : Blo 1543469 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B1544203 : Blo 1543469 1544203 := bstep (se 1 (by rfl) ⟨1158152, by rfl⟩ : syracuseStep 1544203 = 2316305) B2316305
theorem B1544215 : Blo 1543469 1544215 := bstep (se 1 (by rfl) ⟨1158161, by rfl⟩ : syracuseStep 1544215 = 2316323) B2316323
theorem B23777315 : Blo 1543469 23777315 := bstep (se 1 (by rfl) ⟨17832986, by rfl⟩ : syracuseStep 23777315 = 35665973) B35665973
theorem B1544235 : Blo 1543469 1544235 := bstep (se 1 (by rfl) ⟨1158176, by rfl⟩ : syracuseStep 1544235 = 2316353) B2316353
theorem B1544247 : Blo 1543469 1544247 := bstep (se 1 (by rfl) ⟨1158185, by rfl⟩ : syracuseStep 1544247 = 2316371) B2316371
theorem B1544267 : Blo 1543469 1544267 := bstep (se 1 (by rfl) ⟨1158200, by rfl⟩ : syracuseStep 1544267 = 2316401) B2316401
theorem B1544279 : Blo 1543469 1544279 := bstep (se 1 (by rfl) ⟨1158209, by rfl⟩ : syracuseStep 1544279 = 2316419) B2316419
theorem B5566553 : Blo 1543469 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B1544299 : Blo 1543469 1544299 := bstep (se 1 (by rfl) ⟨1158224, by rfl⟩ : syracuseStep 1544299 = 2316449) B2316449
theorem B1544311 : Blo 1543469 1544311 := bstep (se 1 (by rfl) ⟨1158233, by rfl⟩ : syracuseStep 1544311 = 2316467) B2316467
theorem B1544331 : Blo 1543469 1544331 := bstep (se 1 (by rfl) ⟨1158248, by rfl⟩ : syracuseStep 1544331 = 2316497) B2316497
theorem B1544343 : Blo 1543469 1544343 := bstep (se 1 (by rfl) ⟨1158257, by rfl⟩ : syracuseStep 1544343 = 2316515) B2316515
theorem B7819415 : Blo 1543469 7819415 := bstep (se 1 (by rfl) ⟨5864561, by rfl⟩ : syracuseStep 7819415 = 11729123) B11729123
theorem B1544363 : Blo 1543469 1544363 := bstep (se 1 (by rfl) ⟨1158272, by rfl⟩ : syracuseStep 1544363 = 2316545) B2316545
theorem B5861555 : Blo 1543469 5861555 := bstep (se 1 (by rfl) ⟨4396166, by rfl⟩ : syracuseStep 5861555 = 8792333) B8792333
theorem B8794291 : Blo 1543469 8794291 := bstep (se 1 (by rfl) ⟨6595718, by rfl⟩ : syracuseStep 8794291 = 13191437) B13191437
theorem B1544375 : Blo 1543469 1544375 := bstep (se 1 (by rfl) ⟨1158281, by rfl⟩ : syracuseStep 1544375 = 2316563) B2316563
theorem B5214401 : Blo 1543469 5214401 := bstep (se 2 (by rfl) ⟨1955400, by rfl⟩ : syracuseStep 5214401 = 3910801) B3910801
theorem B1544395 : Blo 1543469 1544395 := bstep (se 1 (by rfl) ⟨1158296, by rfl⟩ : syracuseStep 1544395 = 2316593) B2316593
theorem B1544407 : Blo 1543469 1544407 := bstep (se 1 (by rfl) ⟨1158305, by rfl⟩ : syracuseStep 1544407 = 2316611) B2316611
theorem B1544427 : Blo 1543469 1544427 := bstep (se 1 (by rfl) ⟨1158320, by rfl⟩ : syracuseStep 1544427 = 2316641) B2316641
theorem B1544439 : Blo 1543469 1544439 := bstep (se 1 (by rfl) ⟨1158329, by rfl⟩ : syracuseStep 1544439 = 2316659) B2316659
theorem B1544459 : Blo 1543469 1544459 := bstep (se 1 (by rfl) ⟨1158344, by rfl⟩ : syracuseStep 1544459 = 2316689) B2316689
theorem B1544471 : Blo 1543469 1544471 := bstep (se 1 (by rfl) ⟨1158353, by rfl⟩ : syracuseStep 1544471 = 2316707) B2316707
theorem B1544491 : Blo 1543469 1544491 := bstep (se 1 (by rfl) ⟨1158368, by rfl⟩ : syracuseStep 1544491 = 2316737) B2316737
theorem B1544503 : Blo 1543469 1544503 := bstep (se 1 (by rfl) ⟨1158377, by rfl⟩ : syracuseStep 1544503 = 2316755) B2316755
theorem B11727179 : Blo 1543469 11727179 := bstep (se 1 (by rfl) ⟨8795384, by rfl⟩ : syracuseStep 11727179 = 17590769) B17590769
theorem B1544523 : Blo 1543469 1544523 := bstep (se 1 (by rfl) ⟨1158392, by rfl⟩ : syracuseStep 1544523 = 2316785) B2316785
theorem B1954135 : Blo 1543469 1954135 := bstep (se 1 (by rfl) ⟨1465601, by rfl⟩ : syracuseStep 1954135 = 2931203) B2931203
theorem B1544535 : Blo 1543469 1544535 := bstep (se 1 (by rfl) ⟨1158401, by rfl⟩ : syracuseStep 1544535 = 2316803) B2316803
theorem B1544555 : Blo 1543469 1544555 := bstep (se 1 (by rfl) ⟨1158416, by rfl⟩ : syracuseStep 1544555 = 2316833) B2316833
theorem B1544567 : Blo 1543469 1544567 := bstep (se 1 (by rfl) ⟨1158425, by rfl⟩ : syracuseStep 1544567 = 2316851) B2316851
theorem B1544587 : Blo 1543469 1544587 := bstep (se 1 (by rfl) ⟨1158440, by rfl⟩ : syracuseStep 1544587 = 2316881) B2316881
theorem B7418263 : Blo 1543469 7418263 := bstep (se 1 (by rfl) ⟨5563697, by rfl⟩ : syracuseStep 7418263 = 11127395) B11127395
theorem B1544599 : Blo 1543469 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B3297689 : Blo 1543469 3297689 := bstep (se 2 (by rfl) ⟨1236633, by rfl⟩ : syracuseStep 3297689 = 2473267) B2473267
theorem B1544619 : Blo 1543469 1544619 := bstep (se 1 (by rfl) ⟨1158464, by rfl⟩ : syracuseStep 1544619 = 2316929) B2316929
theorem B11891123 : Blo 1543469 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B1544631 : Blo 1543469 1544631 := bstep (se 1 (by rfl) ⟨1158473, by rfl⟩ : syracuseStep 1544631 = 2316947) B2316947
theorem B5943745 : Blo 1543469 5943745 := bstep (se 2 (by rfl) ⟨2228904, by rfl⟩ : syracuseStep 5943745 = 4457809) B4457809
theorem B1544651 : Blo 1543469 1544651 := bstep (se 1 (by rfl) ⟨1158488, by rfl⟩ : syracuseStep 1544651 = 2316977) B2316977
theorem B1544663 : Blo 1543469 1544663 := bstep (se 1 (by rfl) ⟨1158497, by rfl⟩ : syracuseStep 1544663 = 2316995) B2316995
theorem B1544683 : Blo 1543469 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B1544695 : Blo 1543469 1544695 := bstep (se 1 (by rfl) ⟨1158521, by rfl⟩ : syracuseStep 1544695 = 2317043) B2317043
theorem B6599171 : Blo 1543469 6599171 := bstep (se 1 (by rfl) ⟨4949378, by rfl⟩ : syracuseStep 6599171 = 9898757) B9898757
theorem B1544715 : Blo 1543469 1544715 := bstep (se 1 (by rfl) ⟨1158536, by rfl⟩ : syracuseStep 1544715 = 2317073) B2317073
theorem B1544727 : Blo 1543469 1544727 := bstep (se 1 (by rfl) ⟨1158545, by rfl⟩ : syracuseStep 1544727 = 2317091) B2317091
theorem B1544747 : Blo 1543469 1544747 := bstep (se 1 (by rfl) ⟨1158560, by rfl⟩ : syracuseStep 1544747 = 2317121) B2317121
theorem B1544759 : Blo 1543469 1544759 := bstep (se 1 (by rfl) ⟨1158569, by rfl⟩ : syracuseStep 1544759 = 2317139) B2317139
theorem B10031681 : Blo 1543469 10031681 := bstep (se 2 (by rfl) ⟨3761880, by rfl⟩ : syracuseStep 10031681 = 7523761) B7523761
theorem B1544779 : Blo 1543469 1544779 := bstep (se 1 (by rfl) ⟨1158584, by rfl⟩ : syracuseStep 1544779 = 2317169) B2317169
theorem B1544791 : Blo 1543469 1544791 := bstep (se 1 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 1544791 = 2317187) B2317187
theorem B1544811 : Blo 1543469 1544811 := bstep (se 1 (by rfl) ⟨1158608, by rfl⟩ : syracuseStep 1544811 = 2317217) B2317217
theorem B1544823 : Blo 1543469 1544823 := bstep (se 1 (by rfl) ⟨1158617, by rfl⟩ : syracuseStep 1544823 = 2317235) B2317235
theorem B44511875 : Blo 1543469 44511875 := bstep (se 1 (by rfl) ⟨33383906, by rfl⟩ : syracuseStep 44511875 = 66767813) B66767813
theorem B1544843 : Blo 1543469 1544843 := bstep (se 1 (by rfl) ⟨1158632, by rfl⟩ : syracuseStep 1544843 = 2317265) B2317265
theorem B3568279 : Blo 1543469 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B1544855 : Blo 1543469 1544855 := bstep (se 1 (by rfl) ⟨1158641, by rfl⟩ : syracuseStep 1544855 = 2317283) B2317283
theorem B1544875 : Blo 1543469 1544875 := bstep (se 1 (by rfl) ⟨1158656, by rfl⟩ : syracuseStep 1544875 = 2317313) B2317313
theorem B13202099 : Blo 1543469 13202099 := bstep (se 1 (by rfl) ⟨9901574, by rfl⟩ : syracuseStep 13202099 = 19803149) B19803149
theorem B1544887 : Blo 1543469 1544887 := bstep (se 1 (by rfl) ⟨1158665, by rfl⟩ : syracuseStep 1544887 = 2317331) B2317331
theorem B1544907 : Blo 1543469 1544907 := bstep (se 1 (by rfl) ⟨1158680, by rfl⟩ : syracuseStep 1544907 = 2317361) B2317361
theorem B1544919 : Blo 1543469 1544919 := bstep (se 1 (by rfl) ⟨1158689, by rfl⟩ : syracuseStep 1544919 = 2317379) B2317379
theorem B11129561 : Blo 1543469 11129561 := bstep (se 2 (by rfl) ⟨4173585, by rfl⟩ : syracuseStep 11129561 = 8347171) B8347171
theorem B5214941 : Blo 1543469 5214941 := bstep (se 3 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 5214941 = 1955603) B1955603
theorem B1544939 : Blo 1543469 1544939 := bstep (se 1 (by rfl) ⟨1158704, by rfl⟩ : syracuseStep 1544939 = 2317409) B2317409
theorem B1544951 : Blo 1543469 1544951 := bstep (se 1 (by rfl) ⟨1158713, by rfl⟩ : syracuseStep 1544951 = 2317427) B2317427
theorem B1544971 : Blo 1543469 1544971 := bstep (se 1 (by rfl) ⟨1158728, by rfl⟩ : syracuseStep 1544971 = 2317457) B2317457
theorem B1544983 : Blo 1543469 1544983 := bstep (se 1 (by rfl) ⟨1158737, by rfl⟩ : syracuseStep 1544983 = 2317475) B2317475
theorem B1545003 : Blo 1543469 1545003 := bstep (se 1 (by rfl) ⟨1158752, by rfl⟩ : syracuseStep 1545003 = 2317505) B2317505
theorem B3298099 : Blo 1543469 3298099 := bstep (se 1 (by rfl) ⟨2473574, by rfl⟩ : syracuseStep 3298099 = 4947149) B4947149
theorem B1545015 : Blo 1543469 1545015 := bstep (se 1 (by rfl) ⟨1158761, by rfl⟩ : syracuseStep 1545015 = 2317523) B2317523
theorem B15848257 : Blo 1543469 15848257 := bstep (se 2 (by rfl) ⟨5943096, by rfl⟩ : syracuseStep 15848257 = 11886193) B11886193
theorem B3961675 : Blo 1543469 3961675 := bstep (se 1 (by rfl) ⟨2971256, by rfl⟩ : syracuseStep 3961675 = 5942513) B5942513
theorem B1545035 : Blo 1543469 1545035 := bstep (se 1 (by rfl) ⟨1158776, by rfl⟩ : syracuseStep 1545035 = 2317553) B2317553
theorem B1545047 : Blo 1543469 1545047 := bstep (se 1 (by rfl) ⟨1158785, by rfl⟩ : syracuseStep 1545047 = 2317571) B2317571
theorem B1545067 : Blo 1543469 1545067 := bstep (se 1 (by rfl) ⟨1158800, by rfl⟩ : syracuseStep 1545067 = 2317601) B2317601
theorem B1545079 : Blo 1543469 1545079 := bstep (se 1 (by rfl) ⟨1158809, by rfl⟩ : syracuseStep 1545079 = 2317619) B2317619
theorem B1545099 : Blo 1543469 1545099 := bstep (se 1 (by rfl) ⟨1158824, by rfl⟩ : syracuseStep 1545099 = 2317649) B2317649
theorem B1545111 : Blo 1543469 1545111 := bstep (se 1 (by rfl) ⟨1158833, by rfl⟩ : syracuseStep 1545111 = 2317667) B2317667
theorem B1545131 : Blo 1543469 1545131 := bstep (se 1 (by rfl) ⟨1158848, by rfl⟩ : syracuseStep 1545131 = 2317697) B2317697
theorem B1545143 : Blo 1543469 1545143 := bstep (se 1 (by rfl) ⟨1158857, by rfl⟩ : syracuseStep 1545143 = 2317715) B2317715
theorem B1545163 : Blo 1543469 1545163 := bstep (se 1 (by rfl) ⟨1158872, by rfl⟩ : syracuseStep 1545163 = 2317745) B2317745
theorem B1545175 : Blo 1543469 1545175 := bstep (se 1 (by rfl) ⟨1158881, by rfl⟩ : syracuseStep 1545175 = 2317763) B2317763
theorem B2315225 : Blo 1543469 2315225 := bstep (se 2 (by rfl) ⟨868209, by rfl⟩ : syracuseStep 2315225 = 1736419) B1736419
theorem B1545195 : Blo 1543469 1545195 := bstep (se 1 (by rfl) ⟨1158896, by rfl⟩ : syracuseStep 1545195 = 2317793) B2317793
theorem B1545207 : Blo 1543469 1545207 := bstep (se 1 (by rfl) ⟨1158905, by rfl⟩ : syracuseStep 1545207 = 2317811) B2317811
theorem B1545227 : Blo 1543469 1545227 := bstep (se 1 (by rfl) ⟨1158920, by rfl⟩ : syracuseStep 1545227 = 2317841) B2317841
theorem B1545239 : Blo 1543469 1545239 := bstep (se 1 (by rfl) ⟨1158929, by rfl⟩ : syracuseStep 1545239 = 2317859) B2317859
theorem B1545259 : Blo 1543469 1545259 := bstep (se 1 (by rfl) ⟨1158944, by rfl⟩ : syracuseStep 1545259 = 2317889) B2317889
theorem B1545271 : Blo 1543469 1545271 := bstep (se 1 (by rfl) ⟨1158953, by rfl⟩ : syracuseStep 1545271 = 2317907) B2317907
theorem B2315339 : Blo 1543469 2315339 := bstep (se 1 (by rfl) ⟨1736504, by rfl⟩ : syracuseStep 2315339 = 3473009) B3473009
theorem B1586251 : Blo 1543469 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B1545291 : Blo 1543469 1545291 := bstep (se 1 (by rfl) ⟨1158968, by rfl⟩ : syracuseStep 1545291 = 2317937) B2317937
theorem B2315351 : Blo 1543469 2315351 := bstep (se 1 (by rfl) ⟨1736513, by rfl⟩ : syracuseStep 2315351 = 3473027) B3473027
theorem B1545303 : Blo 1543469 1545303 := bstep (se 1 (by rfl) ⟨1158977, by rfl⟩ : syracuseStep 1545303 = 2317955) B2317955
theorem B1545323 : Blo 1543469 1545323 := bstep (se 1 (by rfl) ⟨1158992, by rfl⟩ : syracuseStep 1545323 = 2317985) B2317985
theorem B1545335 : Blo 1543469 1545335 := bstep (se 1 (by rfl) ⟨1159001, by rfl⟩ : syracuseStep 1545335 = 2318003) B2318003
theorem B1954955 : Blo 1543469 1954955 := bstep (se 1 (by rfl) ⟨1466216, by rfl⟩ : syracuseStep 1954955 = 2932433) B2932433
theorem B1545355 : Blo 1543469 1545355 := bstep (se 1 (by rfl) ⟨1159016, by rfl⟩ : syracuseStep 1545355 = 2318033) B2318033
theorem B1545367 : Blo 1543469 1545367 := bstep (se 1 (by rfl) ⟨1159025, by rfl⟩ : syracuseStep 1545367 = 2318051) B2318051
theorem B2315417 : Blo 1543469 2315417 := bstep (se 2 (by rfl) ⟨868281, by rfl⟩ : syracuseStep 2315417 = 1736563) B1736563
theorem B1545387 : Blo 1543469 1545387 := bstep (se 1 (by rfl) ⟨1159040, by rfl⟩ : syracuseStep 1545387 = 2318081) B2318081
theorem B1545399 : Blo 1543469 1545399 := bstep (se 1 (by rfl) ⟨1159049, by rfl⟩ : syracuseStep 1545399 = 2318099) B2318099
theorem B1545419 : Blo 1543469 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B1545431 : Blo 1543469 1545431 := bstep (se 1 (by rfl) ⟨1159073, by rfl⟩ : syracuseStep 1545431 = 2318147) B2318147
theorem B1545451 : Blo 1543469 1545451 := bstep (se 1 (by rfl) ⟨1159088, by rfl⟩ : syracuseStep 1545451 = 2318177) B2318177
theorem B1545463 : Blo 1543469 1545463 := bstep (se 1 (by rfl) ⟨1159097, by rfl⟩ : syracuseStep 1545463 = 2318195) B2318195
theorem B2315531 : Blo 1543469 2315531 := bstep (se 1 (by rfl) ⟨1736648, by rfl⟩ : syracuseStep 2315531 = 3473297) B3473297
theorem B2315543 : Blo 1543469 2315543 := bstep (se 1 (by rfl) ⟨1736657, by rfl⟩ : syracuseStep 2315543 = 3473315) B3473315
theorem B2315609 : Blo 1543469 2315609 := bstep (se 2 (by rfl) ⟨868353, by rfl⟩ : syracuseStep 2315609 = 1736707) B1736707
theorem B4945303 : Blo 1543469 4945303 := bstep (se 1 (by rfl) ⟨3708977, by rfl⟩ : syracuseStep 4945303 = 7417955) B7417955
theorem B2315723 : Blo 1543469 2315723 := bstep (se 1 (by rfl) ⟨1736792, by rfl⟩ : syracuseStep 2315723 = 3473585) B3473585
theorem B2315735 : Blo 1543469 2315735 := bstep (se 1 (by rfl) ⟨1736801, by rfl⟩ : syracuseStep 2315735 = 3473603) B3473603
theorem B2315801 : Blo 1543469 2315801 := bstep (se 2 (by rfl) ⟨868425, by rfl⟩ : syracuseStep 2315801 = 1736851) B1736851
theorem B2348633 : Blo 1543469 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B8795749 : Blo 1543469 8795749 := bstep (se 4 (by rfl) ⟨824601, by rfl⟩ : syracuseStep 8795749 = 1649203) B1649203
theorem B5863043 : Blo 1543469 5863043 := bstep (se 1 (by rfl) ⟨4397282, by rfl⟩ : syracuseStep 5863043 = 8794565) B8794565
theorem B2315915 : Blo 1543469 2315915 := bstep (se 1 (by rfl) ⟨1736936, by rfl⟩ : syracuseStep 2315915 = 3473873) B3473873
theorem B2315927 : Blo 1543469 2315927 := bstep (se 1 (by rfl) ⟨1736945, by rfl⟩ : syracuseStep 2315927 = 3473891) B3473891
theorem B2086603 : Blo 1543469 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B2315993 : Blo 1543469 2315993 := bstep (se 2 (by rfl) ⟨868497, by rfl⟩ : syracuseStep 2315993 = 1736995) B1736995
theorem B2316107 : Blo 1543469 2316107 := bstep (se 1 (by rfl) ⟨1737080, by rfl⟩ : syracuseStep 2316107 = 3474161) B3474161
theorem B1955659 : Blo 1543469 1955659 := bstep (se 1 (by rfl) ⟨1466744, by rfl⟩ : syracuseStep 1955659 = 2933489) B2933489
theorem B2930519 : Blo 1543469 2930519 := bstep (se 1 (by rfl) ⟨2197889, by rfl⟩ : syracuseStep 2930519 = 4395779) B4395779
theorem B2316119 : Blo 1543469 2316119 := bstep (se 1 (by rfl) ⟨1737089, by rfl⟩ : syracuseStep 2316119 = 3474179) B3474179
theorem B2316185 : Blo 1543469 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B35682227 : Blo 1543469 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B3299287 : Blo 1543469 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B3569665 : Blo 1543469 3569665 := bstep (se 2 (by rfl) ⟨1338624, by rfl⟩ : syracuseStep 3569665 = 2677249) B2677249
theorem B3299329 : Blo 1543469 3299329 := bstep (se 2 (by rfl) ⟨1237248, by rfl⟩ : syracuseStep 3299329 = 2474497) B2474497
theorem B2316299 : Blo 1543469 2316299 := bstep (se 1 (by rfl) ⟨1737224, by rfl⟩ : syracuseStep 2316299 = 3474449) B3474449
theorem B2316311 : Blo 1543469 2316311 := bstep (se 1 (by rfl) ⟨1737233, by rfl⟩ : syracuseStep 2316311 = 3474467) B3474467
theorem B5863499 : Blo 1543469 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B1955927 : Blo 1543469 1955927 := bstep (se 1 (by rfl) ⟨1466945, by rfl⟩ : syracuseStep 1955927 = 2933891) B2933891
theorem B2316377 : Blo 1543469 2316377 := bstep (se 2 (by rfl) ⟨868641, by rfl⟩ : syracuseStep 2316377 = 1737283) B1737283
theorem B4946123 : Blo 1543469 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B2316491 : Blo 1543469 2316491 := bstep (se 1 (by rfl) ⟨1737368, by rfl⟩ : syracuseStep 2316491 = 3474737) B3474737
theorem B14842061 : Blo 1543469 14842061 := bstep (se 3 (by rfl) ⟨2782886, by rfl⟩ : syracuseStep 14842061 = 5565773) B5565773
theorem B2316503 : Blo 1543469 2316503 := bstep (se 1 (by rfl) ⟨1737377, by rfl⟩ : syracuseStep 2316503 = 3474755) B3474755
theorem B5863697 : Blo 1543469 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B2316569 : Blo 1543469 2316569 := bstep (se 2 (by rfl) ⟨868713, by rfl⟩ : syracuseStep 2316569 = 1737427) B1737427
theorem B2931059 : Blo 1543469 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B2316683 : Blo 1543469 2316683 := bstep (se 1 (by rfl) ⟨1737512, by rfl⟩ : syracuseStep 2316683 = 3475025) B3475025
theorem B47569301 : Blo 1543469 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B2316695 : Blo 1543469 2316695 := bstep (se 1 (by rfl) ⟨1737521, by rfl⟩ : syracuseStep 2316695 = 3475043) B3475043
theorem B6592985 : Blo 1543469 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B2316761 : Blo 1543469 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B4397591 : Blo 1543469 4397591 := bstep (se 1 (by rfl) ⟨3298193, by rfl⟩ : syracuseStep 4397591 = 6596387) B6596387
theorem B13195811 : Blo 1543469 13195811 := bstep (se 1 (by rfl) ⟨9896858, by rfl⟩ : syracuseStep 13195811 = 19793717) B19793717
theorem B4176449 : Blo 1543469 4176449 := bstep (se 2 (by rfl) ⟨1566168, by rfl⟩ : syracuseStep 4176449 = 3132337) B3132337
theorem B2316875 : Blo 1543469 2316875 := bstep (se 1 (by rfl) ⟨1737656, by rfl⟩ : syracuseStep 2316875 = 3475313) B3475313
theorem B2316887 : Blo 1543469 2316887 := bstep (se 1 (by rfl) ⟨1737665, by rfl⟩ : syracuseStep 2316887 = 3475331) B3475331
theorem B11721347 : Blo 1543469 11721347 := bstep (se 1 (by rfl) ⟨8791010, by rfl⟩ : syracuseStep 11721347 = 17582021) B17582021
theorem B5569175 : Blo 1543469 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B2472601 : Blo 1543469 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B2316953 : Blo 1543469 2316953 := bstep (se 2 (by rfl) ⟨868857, by rfl⟩ : syracuseStep 2316953 = 1737715) B1737715
theorem B2317067 : Blo 1543469 2317067 := bstep (se 1 (by rfl) ⟨1737800, by rfl⟩ : syracuseStep 2317067 = 3475601) B3475601
theorem B2317079 : Blo 1543469 2317079 := bstep (se 1 (by rfl) ⟨1737809, by rfl⟩ : syracuseStep 2317079 = 3475619) B3475619
theorem B2931545 : Blo 1543469 2931545 := bstep (se 2 (by rfl) ⟨1099329, by rfl⟩ : syracuseStep 2931545 = 2198659) B2198659
theorem B2317145 : Blo 1543469 2317145 := bstep (se 2 (by rfl) ⟨868929, by rfl⟩ : syracuseStep 2317145 = 1737859) B1737859
theorem B2472857 : Blo 1543469 2472857 := bstep (se 2 (by rfl) ⟨927321, by rfl⟩ : syracuseStep 2472857 = 1854643) B1854643
theorem B2317259 : Blo 1543469 2317259 := bstep (se 1 (by rfl) ⟨1737944, by rfl⟩ : syracuseStep 2317259 = 3475889) B3475889
theorem B2317271 : Blo 1543469 2317271 := bstep (se 1 (by rfl) ⟨1737953, by rfl⟩ : syracuseStep 2317271 = 3475907) B3475907
theorem B5864471 : Blo 1543469 5864471 := bstep (se 1 (by rfl) ⟨4398353, by rfl⟩ : syracuseStep 5864471 = 8796707) B8796707
theorem B2317337 : Blo 1543469 2317337 := bstep (se 2 (by rfl) ⟨869001, by rfl⟩ : syracuseStep 2317337 = 1738003) B1738003
theorem B19307555 : Blo 1543469 19307555 := bstep (se 1 (by rfl) ⟨14480666, by rfl⟩ : syracuseStep 19307555 = 28961333) B28961333
theorem B2473049 : Blo 1543469 2473049 := bstep (se 2 (by rfl) ⟨927393, by rfl⟩ : syracuseStep 2473049 = 1854787) B1854787
theorem B5569667 : Blo 1543469 5569667 := bstep (se 1 (by rfl) ⟨4177250, by rfl⟩ : syracuseStep 5569667 = 8354501) B8354501
theorem B2317451 : Blo 1543469 2317451 := bstep (se 1 (by rfl) ⟨1738088, by rfl⟩ : syracuseStep 2317451 = 3476177) B3476177
theorem B13376663 : Blo 1543469 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B2317463 : Blo 1543469 2317463 := bstep (se 1 (by rfl) ⟨1738097, by rfl⟩ : syracuseStep 2317463 = 3476195) B3476195
theorem B19791053 : Blo 1543469 19791053 := bstep (se 3 (by rfl) ⟨3710822, by rfl⟩ : syracuseStep 19791053 = 7421645) B7421645
theorem B2317529 : Blo 1543469 2317529 := bstep (se 2 (by rfl) ⟨869073, by rfl⟩ : syracuseStep 2317529 = 1738147) B1738147
theorem B2784473 : Blo 1543469 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B5864669 : Blo 1543469 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B14081285 : Blo 1543469 14081285 := bstep (se 4 (by rfl) ⟨1320120, by rfl⟩ : syracuseStep 14081285 = 2640241) B2640241
theorem B6266135 : Blo 1543469 6266135 := bstep (se 1 (by rfl) ⟨4699601, by rfl⟩ : syracuseStep 6266135 = 9399203) B9399203
theorem B2317643 : Blo 1543469 2317643 := bstep (se 1 (by rfl) ⟨1738232, by rfl⟩ : syracuseStep 2317643 = 3476465) B3476465
theorem B2317655 : Blo 1543469 2317655 := bstep (se 1 (by rfl) ⟨1738241, by rfl⟩ : syracuseStep 2317655 = 3476483) B3476483
theorem B5209433 : Blo 1543469 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B15850853 : Blo 1543469 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B2317721 : Blo 1543469 2317721 := bstep (se 2 (by rfl) ⟨869145, by rfl⟩ : syracuseStep 2317721 = 1738291) B1738291
theorem B5430707 : Blo 1543469 5430707 := bstep (se 1 (by rfl) ⟨4073030, by rfl⟩ : syracuseStep 5430707 = 8146061) B8146061
theorem B3472883 : Blo 1543469 3472883 := bstep (se 1 (by rfl) ⟨2604662, by rfl⟩ : syracuseStep 3472883 = 5209325) B5209325
theorem B2317835 : Blo 1543469 2317835 := bstep (se 1 (by rfl) ⟨1738376, by rfl⟩ : syracuseStep 2317835 = 3476753) B3476753
theorem B3472919 : Blo 1543469 3472919 := bstep (se 1 (by rfl) ⟨2604689, by rfl⟩ : syracuseStep 3472919 = 5209379) B5209379
theorem B2317847 : Blo 1543469 2317847 := bstep (se 1 (by rfl) ⟨1738385, by rfl⟩ : syracuseStep 2317847 = 3476771) B3476771
theorem B11288099 : Blo 1543469 11288099 := bstep (se 1 (by rfl) ⟨8466074, by rfl⟩ : syracuseStep 11288099 = 16932149) B16932149
theorem B2317913 : Blo 1543469 2317913 := bstep (se 2 (by rfl) ⟨869217, by rfl⟩ : syracuseStep 2317913 = 1738435) B1738435
theorem B7822979 : Blo 1543469 7822979 := bstep (se 1 (by rfl) ⟨5867234, by rfl⟩ : syracuseStep 7822979 = 11734469) B11734469
theorem B2604683 : Blo 1543469 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B3473099 : Blo 1543469 3473099 := bstep (se 1 (by rfl) ⟨2604824, by rfl⟩ : syracuseStep 3473099 = 5209649) B5209649
theorem B2318027 : Blo 1543469 2318027 := bstep (se 1 (by rfl) ⟨1738520, by rfl⟩ : syracuseStep 2318027 = 3477041) B3477041
theorem B2318039 : Blo 1543469 2318039 := bstep (se 1 (by rfl) ⟨1738529, by rfl⟩ : syracuseStep 2318039 = 3477059) B3477059
theorem B3473153 : Blo 1543469 3473153 := bstep (se 2 (by rfl) ⟨1302432, by rfl⟩ : syracuseStep 3473153 = 2604865) B2604865
theorem B2604811 : Blo 1543469 2604811 := bstep (se 1 (by rfl) ⟨1953608, by rfl⟩ : syracuseStep 2604811 = 3907217) B3907217
theorem B2318105 : Blo 1543469 2318105 := bstep (se 2 (by rfl) ⟨869289, by rfl⟩ : syracuseStep 2318105 = 1738579) B1738579
theorem B1736491 : Blo 1543469 1736491 := bstep (se 1 (by rfl) ⟨1302368, by rfl⟩ : syracuseStep 1736491 = 2604737) B2604737
theorem B3907379 : Blo 1543469 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B3710785 : Blo 1543469 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B4398923 : Blo 1543469 4398923 := bstep (se 1 (by rfl) ⟨3299192, by rfl⟩ : syracuseStep 4398923 = 6598385) B6598385
theorem B1736599 : Blo 1543469 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B2604953 : Blo 1543469 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B4947905 : Blo 1543469 4947905 := bstep (se 2 (by rfl) ⟨1855464, by rfl⟩ : syracuseStep 4947905 = 3710929) B3710929
theorem B3473369 : Blo 1543469 3473369 := bstep (se 2 (by rfl) ⟨1302513, by rfl⟩ : syracuseStep 3473369 = 2605027) B2605027
theorem B4759553 : Blo 1543469 4759553 := bstep (se 2 (by rfl) ⟨1784832, by rfl⟩ : syracuseStep 4759553 = 3569665) B3569665
theorem B4399105 : Blo 1543469 4399105 := bstep (se 2 (by rfl) ⟨1649664, by rfl⟩ : syracuseStep 4399105 = 3299329) B3299329
theorem B3473423 : Blo 1543469 3473423 := bstep (se 1 (by rfl) ⟨2605067, by rfl⟩ : syracuseStep 3473423 = 5210135) B5210135
theorem B15851543 : Blo 1543469 15851543 := bstep (se 1 (by rfl) ⟨11888657, by rfl⟩ : syracuseStep 15851543 = 23777315) B23777315
theorem B3473441 : Blo 1543469 3473441 := bstep (se 2 (by rfl) ⟨1302540, by rfl⟩ : syracuseStep 3473441 = 2605081) B2605081
theorem B2605115 : Blo 1543469 2605115 := bstep (se 1 (by rfl) ⟨1953836, by rfl⟩ : syracuseStep 2605115 = 3907673) B3907673
theorem B3711035 : Blo 1543469 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B3907703 : Blo 1543469 3907703 := bstep (se 1 (by rfl) ⟨2930777, by rfl⟩ : syracuseStep 3907703 = 5861555) B5861555
theorem B6594797 : Blo 1543469 6594797 := bstep (se 3 (by rfl) ⟨1236524, by rfl⟩ : syracuseStep 6594797 = 2473049) B2473049
theorem B7143661 : Blo 1543469 7143661 := bstep (se 3 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 7143661 = 2678873) B2678873
theorem B4399447 : Blo 1543469 4399447 := bstep (se 1 (by rfl) ⟨3299585, by rfl⟩ : syracuseStep 4399447 = 6599171) B6599171
theorem B14836061 : Blo 1543469 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B3473783 : Blo 1543469 3473783 := bstep (se 1 (by rfl) ⟨2605337, by rfl⟩ : syracuseStep 3473783 = 5210675) B5210675
theorem B1737103 : Blo 1543469 1737103 := bstep (se 1 (by rfl) ⟨1302827, by rfl⟩ : syracuseStep 1737103 = 2605655) B2605655
theorem B2605513 : Blo 1543469 2605513 := bstep (se 2 (by rfl) ⟨977067, by rfl⟩ : syracuseStep 2605513 = 1954135) B1954135
theorem B6349265 : Blo 1543469 6349265 := bstep (se 2 (by rfl) ⟨2380974, by rfl⟩ : syracuseStep 6349265 = 4761949) B4761949
theorem B13189661 : Blo 1543469 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B3473963 : Blo 1543469 3473963 := bstep (se 1 (by rfl) ⟨2605472, by rfl⟩ : syracuseStep 3473963 = 5210945) B5210945
theorem B7930541 : Blo 1543469 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B1737607 : Blo 1543469 1737607 := bstep (se 1 (by rfl) ⟨1303205, by rfl⟩ : syracuseStep 1737607 = 2606411) B2606411
theorem B3474323 : Blo 1543469 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B16704409 : Blo 1543469 16704409 := bstep (se 2 (by rfl) ⟨6264153, by rfl⟩ : syracuseStep 16704409 = 12528307) B12528307
theorem B3474377 : Blo 1543469 3474377 := bstep (se 2 (by rfl) ⟨1302891, by rfl⟩ : syracuseStep 3474377 = 2605783) B2605783
theorem B1737787 : Blo 1543469 1737787 := bstep (se 1 (by rfl) ⟨1303340, by rfl⟩ : syracuseStep 1737787 = 2606681) B2606681
theorem B3908695 : Blo 1543469 3908695 := bstep (se 1 (by rfl) ⟨2931521, by rfl⟩ : syracuseStep 3908695 = 5863043) B5863043
theorem B2606215 : Blo 1543469 2606215 := bstep (se 1 (by rfl) ⟨1954661, by rfl⟩ : syracuseStep 2606215 = 3909323) B3909323
theorem B7816499 : Blo 1543469 7816499 := bstep (se 1 (by rfl) ⟨5862374, by rfl⟩ : syracuseStep 7816499 = 11724749) B11724749
theorem B3908999 : Blo 1543469 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B8799623 : Blo 1543469 8799623 := bstep (se 1 (by rfl) ⟨6599717, by rfl⟩ : syracuseStep 8799623 = 13199435) B13199435
theorem B5211539 : Blo 1543469 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B2115001 : Blo 1543469 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B3909131 : Blo 1543469 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B1738255 : Blo 1543469 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B31712867 : Blo 1543469 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B7816823 : Blo 1543469 7816823 := bstep (se 1 (by rfl) ⟨5862617, by rfl⟩ : syracuseStep 7816823 = 11725235) B11725235
theorem B3475079 : Blo 1543469 3475079 := bstep (se 1 (by rfl) ⟨2606309, by rfl⟩ : syracuseStep 3475079 = 5212619) B5212619
theorem B9397961 : Blo 1543469 9397961 := bstep (se 2 (by rfl) ⟨3524235, by rfl⟩ : syracuseStep 9397961 = 7048471) B7048471
theorem B2606863 : Blo 1543469 2606863 := bstep (se 1 (by rfl) ⟨1955147, by rfl⟩ : syracuseStep 2606863 = 3910295) B3910295
theorem B3475259 : Blo 1543469 3475259 := bstep (se 1 (by rfl) ⟨2606444, by rfl⟩ : syracuseStep 3475259 = 5212889) B5212889
theorem B5867417 : Blo 1543469 5867417 := bstep (se 2 (by rfl) ⟨2200281, by rfl⟩ : syracuseStep 5867417 = 4400563) B4400563
theorem B3475385 : Blo 1543469 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B1648571 : Blo 1543469 1648571 := bstep (se 1 (by rfl) ⟨1236428, by rfl⟩ : syracuseStep 1648571 = 2472857) B2472857
theorem B3909647 : Blo 1543469 3909647 := bstep (se 1 (by rfl) ⟨2932235, by rfl⟩ : syracuseStep 3909647 = 5864471) B5864471
theorem B12871703 : Blo 1543469 12871703 := bstep (se 1 (by rfl) ⟨9653777, by rfl⟩ : syracuseStep 12871703 = 19307555) B19307555
theorem B29706263 : Blo 1543469 29706263 := bstep (se 1 (by rfl) ⟨22279697, by rfl⟩ : syracuseStep 29706263 = 44559395) B44559395
theorem B3713111 : Blo 1543469 3713111 := bstep (se 1 (by rfl) ⟨2784833, by rfl⟩ : syracuseStep 3713111 = 5569667) B5569667
theorem B2197639 : Blo 1543469 2197639 := bstep (se 1 (by rfl) ⟨1648229, by rfl⟩ : syracuseStep 2197639 = 3296459) B3296459
theorem B3909779 : Blo 1543469 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B3475727 : Blo 1543469 3475727 := bstep (se 1 (by rfl) ⟨2606795, by rfl⟩ : syracuseStep 3475727 = 5213591) B5213591
theorem B3475745 : Blo 1543469 3475745 := bstep (se 2 (by rfl) ⟨1303404, by rfl⟩ : syracuseStep 3475745 = 2606809) B2606809
theorem B2607403 : Blo 1543469 2607403 := bstep (se 1 (by rfl) ⟨1955552, by rfl⟩ : syracuseStep 2607403 = 3911105) B3911105
theorem B2509115 : Blo 1543469 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B2607545 : Blo 1543469 2607545 := bstep (se 2 (by rfl) ⟨977829, by rfl⟩ : syracuseStep 2607545 = 1955659) B1955659
theorem B9898499 : Blo 1543469 9898499 := bstep (se 1 (by rfl) ⟨7423874, by rfl⟩ : syracuseStep 9898499 = 14847749) B14847749
theorem B4950571 : Blo 1543469 4950571 := bstep (se 1 (by rfl) ⟨3712928, by rfl⟩ : syracuseStep 4950571 = 7425857) B7425857
theorem B12520003 : Blo 1543469 12520003 := bstep (se 1 (by rfl) ⟨9390002, by rfl⟩ : syracuseStep 12520003 = 18780005) B18780005
theorem B7817795 : Blo 1543469 7817795 := bstep (se 1 (by rfl) ⟨5863346, by rfl⟩ : syracuseStep 7817795 = 11726693) B11726693
theorem B3476087 : Blo 1543469 3476087 := bstep (se 1 (by rfl) ⟨2607065, by rfl⟩ : syracuseStep 3476087 = 5214131) B5214131
theorem B8792833 : Blo 1543469 8792833 := bstep (se 2 (by rfl) ⟨3297312, by rfl⟩ : syracuseStep 8792833 = 6594625) B6594625
theorem B5212943 : Blo 1543469 5212943 := bstep (se 1 (by rfl) ⟨3909707, by rfl⟩ : syracuseStep 5212943 = 7819415) B7819415
theorem B3476267 : Blo 1543469 3476267 := bstep (se 1 (by rfl) ⟨2607200, by rfl⟩ : syracuseStep 3476267 = 5214401) B5214401
theorem B2198345 : Blo 1543469 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B7818119 : Blo 1543469 7818119 := bstep (se 1 (by rfl) ⟨5863589, by rfl⟩ : syracuseStep 7818119 = 11727179) B11727179
theorem B11725721 : Blo 1543469 11725721 := bstep (se 2 (by rfl) ⟨4397145, by rfl⟩ : syracuseStep 11725721 = 8794291) B8794291
theorem B6261689 : Blo 1543469 6261689 := bstep (se 2 (by rfl) ⟨2348133, by rfl⟩ : syracuseStep 6261689 = 4696267) B4696267
theorem B2198459 : Blo 1543469 2198459 := bstep (se 1 (by rfl) ⟨1648844, by rfl⟩ : syracuseStep 2198459 = 3297689) B3297689
theorem B5213213 : Blo 1543469 5213213 := bstep (se 3 (by rfl) ⟨977477, by rfl⟩ : syracuseStep 5213213 = 1954955) B1954955
theorem B6687787 : Blo 1543469 6687787 := bstep (se 1 (by rfl) ⟨5015840, by rfl⟩ : syracuseStep 6687787 = 10031681) B10031681
theorem B29674583 : Blo 1543469 29674583 := bstep (se 1 (by rfl) ⟨22255937, by rfl⟩ : syracuseStep 29674583 = 44511875) B44511875
theorem B8801399 : Blo 1543469 8801399 := bstep (se 1 (by rfl) ⟨6601049, by rfl⟩ : syracuseStep 8801399 = 13202099) B13202099
theorem B3476627 : Blo 1543469 3476627 := bstep (se 1 (by rfl) ⟨2607470, by rfl⟩ : syracuseStep 3476627 = 5214941) B5214941
theorem B9891017 : Blo 1543469 9891017 := bstep (se 2 (by rfl) ⟨3709131, by rfl⟩ : syracuseStep 9891017 = 7418263) B7418263
theorem B3476681 : Blo 1543469 3476681 := bstep (se 2 (by rfl) ⟨1303755, by rfl⟩ : syracuseStep 3476681 = 2607511) B2607511
theorem B3910913 : Blo 1543469 3910913 := bstep (se 2 (by rfl) ⟨1466592, by rfl⟩ : syracuseStep 3910913 = 2933185) B2933185
theorem B8793359 : Blo 1543469 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B1543483 : Blo 1543469 1543483 := bstep (se 1 (by rfl) ⟨1157612, by rfl⟩ : syracuseStep 1543483 = 2315225) B2315225
theorem B1543559 : Blo 1543469 1543559 := bstep (se 1 (by rfl) ⟨1157669, by rfl⟩ : syracuseStep 1543559 = 2315339) B2315339
theorem B1543567 : Blo 1543469 1543567 := bstep (se 1 (by rfl) ⟨1157675, by rfl⟩ : syracuseStep 1543567 = 2315351) B2315351
theorem B1543611 : Blo 1543469 1543611 := bstep (se 1 (by rfl) ⟨1157708, by rfl⟩ : syracuseStep 1543611 = 2315417) B2315417
theorem B1543687 : Blo 1543469 1543687 := bstep (se 1 (by rfl) ⟨1157765, by rfl⟩ : syracuseStep 1543687 = 2315531) B2315531
theorem B1543695 : Blo 1543469 1543695 := bstep (se 1 (by rfl) ⟨1157771, by rfl⟩ : syracuseStep 1543695 = 2315543) B2315543
theorem B3296801 : Blo 1543469 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2199097 : Blo 1543469 2199097 := bstep (se 2 (by rfl) ⟨824661, by rfl⟩ : syracuseStep 2199097 = 1649323) B1649323
theorem B1543739 : Blo 1543469 1543739 := bstep (se 1 (by rfl) ⟨1157804, by rfl⟩ : syracuseStep 1543739 = 2315609) B2315609
theorem B3911287 : Blo 1543469 3911287 := bstep (se 1 (by rfl) ⟨2933465, by rfl⟩ : syracuseStep 3911287 = 5866931) B5866931
theorem B1543815 : Blo 1543469 1543815 := bstep (se 1 (by rfl) ⟨1157861, by rfl⟩ : syracuseStep 1543815 = 2315723) B2315723
theorem B1543823 : Blo 1543469 1543823 := bstep (se 1 (by rfl) ⟨1157867, by rfl⟩ : syracuseStep 1543823 = 2315735) B2315735
theorem B1543867 : Blo 1543469 1543867 := bstep (se 1 (by rfl) ⟨1157900, by rfl⟩ : syracuseStep 1543867 = 2315801) B2315801
theorem B11128549 : Blo 1543469 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B21131009 : Blo 1543469 21131009 := bstep (se 2 (by rfl) ⟨7924128, by rfl⟩ : syracuseStep 21131009 = 15848257) B15848257
theorem B1543943 : Blo 1543469 1543943 := bstep (se 1 (by rfl) ⟨1157957, by rfl⟩ : syracuseStep 1543943 = 2315915) B2315915
theorem B3960587 : Blo 1543469 3960587 := bstep (se 1 (by rfl) ⟨2970440, by rfl⟩ : syracuseStep 3960587 = 5940881) B5940881
theorem B1543951 : Blo 1543469 1543951 := bstep (se 1 (by rfl) ⟨1157963, by rfl⟩ : syracuseStep 1543951 = 2315927) B2315927
theorem B1543995 : Blo 1543469 1543995 := bstep (se 1 (by rfl) ⟨1157996, by rfl⟩ : syracuseStep 1543995 = 2315993) B2315993
theorem B1544071 : Blo 1543469 1544071 := bstep (se 1 (by rfl) ⟨1158053, by rfl⟩ : syracuseStep 1544071 = 2316107) B2316107
theorem B1544079 : Blo 1543469 1544079 := bstep (se 1 (by rfl) ⟨1158059, by rfl⟩ : syracuseStep 1544079 = 2316119) B2316119
theorem B5861267 : Blo 1543469 5861267 := bstep (se 1 (by rfl) ⟨4395950, by rfl⟩ : syracuseStep 5861267 = 8791901) B8791901
theorem B17592227 : Blo 1543469 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1544123 : Blo 1543469 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B1544199 : Blo 1543469 1544199 := bstep (se 1 (by rfl) ⟨1158149, by rfl⟩ : syracuseStep 1544199 = 2316299) B2316299
theorem B1544207 : Blo 1543469 1544207 := bstep (se 1 (by rfl) ⟨1158155, by rfl⟩ : syracuseStep 1544207 = 2316311) B2316311
theorem B3911723 : Blo 1543469 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B1544251 : Blo 1543469 1544251 := bstep (se 1 (by rfl) ⟨1158188, by rfl⟩ : syracuseStep 1544251 = 2316377) B2316377
theorem B1544327 : Blo 1543469 1544327 := bstep (se 1 (by rfl) ⟨1158245, by rfl⟩ : syracuseStep 1544327 = 2316491) B2316491
theorem B1544335 : Blo 1543469 1544335 := bstep (se 1 (by rfl) ⟨1158251, by rfl⟩ : syracuseStep 1544335 = 2316503) B2316503
theorem B1544379 : Blo 1543469 1544379 := bstep (se 1 (by rfl) ⟨1158284, by rfl⟩ : syracuseStep 1544379 = 2316569) B2316569
theorem B12529865 : Blo 1543469 12529865 := bstep (se 2 (by rfl) ⟨4698699, by rfl⟩ : syracuseStep 12529865 = 9397399) B9397399
theorem B6263021 : Blo 1543469 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B17830133 : Blo 1543469 17830133 := bstep (se 5 (by rfl) ⟨835787, by rfl⟩ : syracuseStep 17830133 = 1671575) B1671575
theorem B1954039 : Blo 1543469 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B1544455 : Blo 1543469 1544455 := bstep (se 1 (by rfl) ⟨1158341, by rfl⟩ : syracuseStep 1544455 = 2316683) B2316683
theorem B1544463 : Blo 1543469 1544463 := bstep (se 1 (by rfl) ⟨1158347, by rfl⟩ : syracuseStep 1544463 = 2316695) B2316695
theorem B4395323 : Blo 1543469 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B1544507 : Blo 1543469 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B9040187 : Blo 1543469 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B5861767 : Blo 1543469 5861767 := bstep (se 1 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 5861767 = 8792651) B8792651
theorem B1544583 : Blo 1543469 1544583 := bstep (se 1 (by rfl) ⟨1158437, by rfl⟩ : syracuseStep 1544583 = 2316875) B2316875
theorem B1544591 : Blo 1543469 1544591 := bstep (se 1 (by rfl) ⟨1158443, by rfl⟩ : syracuseStep 1544591 = 2316887) B2316887
theorem B11735441 : Blo 1543469 11735441 := bstep (se 2 (by rfl) ⟨4400790, by rfl⟩ : syracuseStep 11735441 = 8801581) B8801581
theorem B5214617 : Blo 1543469 5214617 := bstep (se 2 (by rfl) ⟨1955481, by rfl⟩ : syracuseStep 5214617 = 3910963) B3910963
theorem B1544635 : Blo 1543469 1544635 := bstep (se 1 (by rfl) ⟨1158476, by rfl⟩ : syracuseStep 1544635 = 2316953) B2316953
theorem B1544711 : Blo 1543469 1544711 := bstep (se 1 (by rfl) ⟨1158533, by rfl⟩ : syracuseStep 1544711 = 2317067) B2317067
theorem B1544719 : Blo 1543469 1544719 := bstep (se 1 (by rfl) ⟨1158539, by rfl⟩ : syracuseStep 1544719 = 2317079) B2317079
theorem B1954363 : Blo 1543469 1954363 := bstep (se 1 (by rfl) ⟨1465772, by rfl⟩ : syracuseStep 1954363 = 2931545) B2931545
theorem B1544763 : Blo 1543469 1544763 := bstep (se 1 (by rfl) ⟨1158572, by rfl⟩ : syracuseStep 1544763 = 2317145) B2317145
theorem B1544839 : Blo 1543469 1544839 := bstep (se 1 (by rfl) ⟨1158629, by rfl⟩ : syracuseStep 1544839 = 2317259) B2317259
theorem B1544847 : Blo 1543469 1544847 := bstep (se 1 (by rfl) ⟨1158635, by rfl⟩ : syracuseStep 1544847 = 2317271) B2317271
theorem B1544891 : Blo 1543469 1544891 := bstep (se 1 (by rfl) ⟨1158668, by rfl⟩ : syracuseStep 1544891 = 2317337) B2317337
theorem B8794817 : Blo 1543469 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B1544967 : Blo 1543469 1544967 := bstep (se 1 (by rfl) ⟨1158725, by rfl⟩ : syracuseStep 1544967 = 2317451) B2317451
theorem B8917775 : Blo 1543469 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B1544975 : Blo 1543469 1544975 := bstep (se 1 (by rfl) ⟨1158731, by rfl⟩ : syracuseStep 1544975 = 2317463) B2317463
theorem B18789155 : Blo 1543469 18789155 := bstep (se 1 (by rfl) ⟨14091866, by rfl⟩ : syracuseStep 18789155 = 28183733) B28183733
theorem B11727665 : Blo 1543469 11727665 := bstep (se 2 (by rfl) ⟨4397874, by rfl⟩ : syracuseStep 11727665 = 8795749) B8795749
theorem B13194035 : Blo 1543469 13194035 := bstep (se 1 (by rfl) ⟨9895526, by rfl⟩ : syracuseStep 13194035 = 19791053) B19791053
theorem B1545019 : Blo 1543469 1545019 := bstep (se 1 (by rfl) ⟨1158764, by rfl⟩ : syracuseStep 1545019 = 2317529) B2317529
theorem B1856315 : Blo 1543469 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B1545095 : Blo 1543469 1545095 := bstep (se 1 (by rfl) ⟨1158821, by rfl⟩ : syracuseStep 1545095 = 2317643) B2317643
theorem B1545103 : Blo 1543469 1545103 := bstep (se 1 (by rfl) ⟨1158827, by rfl⟩ : syracuseStep 1545103 = 2317655) B2317655
theorem B4395961 : Blo 1543469 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B1545147 : Blo 1543469 1545147 := bstep (se 1 (by rfl) ⟨1158860, by rfl⟩ : syracuseStep 1545147 = 2317721) B2317721
theorem B2315255 : Blo 1543469 2315255 := bstep (se 1 (by rfl) ⟨1736441, by rfl⟩ : syracuseStep 2315255 = 3472883) B3472883
theorem B31699973 : Blo 1543469 31699973 := bstep (se 4 (by rfl) ⟨2971872, by rfl⟩ : syracuseStep 31699973 = 5943745) B5943745
theorem B1545223 : Blo 1543469 1545223 := bstep (se 1 (by rfl) ⟨1158917, by rfl⟩ : syracuseStep 1545223 = 2317835) B2317835
theorem B2315279 : Blo 1543469 2315279 := bstep (se 1 (by rfl) ⟨1736459, by rfl⟩ : syracuseStep 2315279 = 3472919) B3472919
theorem B1545231 : Blo 1543469 1545231 := bstep (se 1 (by rfl) ⟨1158923, by rfl⟩ : syracuseStep 1545231 = 2317847) B2317847
theorem B7525399 : Blo 1543469 7525399 := bstep (se 1 (by rfl) ⟨5644049, by rfl⟩ : syracuseStep 7525399 = 11288099) B11288099
theorem B2315321 : Blo 1543469 2315321 := bstep (se 2 (by rfl) ⟨868245, by rfl⟩ : syracuseStep 2315321 = 1736491) B1736491
theorem B1545275 : Blo 1543469 1545275 := bstep (se 1 (by rfl) ⟨1158956, by rfl⟩ : syracuseStep 1545275 = 2317913) B2317913
theorem B5215319 : Blo 1543469 5215319 := bstep (se 1 (by rfl) ⟨3911489, by rfl⟩ : syracuseStep 5215319 = 7822979) B7822979
theorem B2315399 : Blo 1543469 2315399 := bstep (se 1 (by rfl) ⟨1736549, by rfl⟩ : syracuseStep 2315399 = 3473099) B3473099
theorem B1545351 : Blo 1543469 1545351 := bstep (se 1 (by rfl) ⟨1159013, by rfl⟩ : syracuseStep 1545351 = 2318027) B2318027
theorem B1545359 : Blo 1543469 1545359 := bstep (se 1 (by rfl) ⟨1159019, by rfl⟩ : syracuseStep 1545359 = 2318039) B2318039
theorem B2315435 : Blo 1543469 2315435 := bstep (se 1 (by rfl) ⟨1736576, by rfl⟩ : syracuseStep 2315435 = 3473153) B3473153
theorem B13194413 : Blo 1543469 13194413 := bstep (se 3 (by rfl) ⟨2473952, by rfl⟩ : syracuseStep 13194413 = 4947905) B4947905
theorem B1545403 : Blo 1543469 1545403 := bstep (se 1 (by rfl) ⟨1159052, by rfl⟩ : syracuseStep 1545403 = 2318105) B2318105
theorem B2315465 : Blo 1543469 2315465 := bstep (se 2 (by rfl) ⟨868299, by rfl⟩ : syracuseStep 2315465 = 1736599) B1736599
theorem B90273005 : Blo 1543469 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B2315579 : Blo 1543469 2315579 := bstep (se 1 (by rfl) ⟨1736684, by rfl⟩ : syracuseStep 2315579 = 3473369) B3473369
theorem B4396349 : Blo 1543469 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B2315639 : Blo 1543469 2315639 := bstep (se 1 (by rfl) ⟨1736729, by rfl⟩ : syracuseStep 2315639 = 3473459) B3473459
theorem B2315663 : Blo 1543469 2315663 := bstep (se 1 (by rfl) ⟨1736747, by rfl⟩ : syracuseStep 2315663 = 3473495) B3473495
theorem B2315705 : Blo 1543469 2315705 := bstep (se 2 (by rfl) ⟨868389, by rfl⟩ : syracuseStep 2315705 = 1736779) B1736779
theorem B2315783 : Blo 1543469 2315783 := bstep (se 1 (by rfl) ⟨1736837, by rfl⟩ : syracuseStep 2315783 = 3473675) B3473675
theorem B1955335 : Blo 1543469 1955335 := bstep (se 1 (by rfl) ⟨1466501, by rfl⟩ : syracuseStep 1955335 = 2933003) B2933003
theorem B2315819 : Blo 1543469 2315819 := bstep (se 1 (by rfl) ⟨1736864, by rfl⟩ : syracuseStep 2315819 = 3473729) B3473729
theorem B5215805 : Blo 1543469 5215805 := bstep (se 3 (by rfl) ⟨977963, by rfl⟩ : syracuseStep 5215805 = 1955927) B1955927
theorem B2315849 : Blo 1543469 2315849 := bstep (se 2 (by rfl) ⟨868443, by rfl⟩ : syracuseStep 2315849 = 1736887) B1736887
theorem B7927415 : Blo 1543469 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B2315963 : Blo 1543469 2315963 := bstep (se 1 (by rfl) ⟨1736972, by rfl⟩ : syracuseStep 2315963 = 3473945) B3473945
theorem B2316023 : Blo 1543469 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B2316047 : Blo 1543469 2316047 := bstep (se 1 (by rfl) ⟨1737035, by rfl⟩ : syracuseStep 2316047 = 3474071) B3474071
theorem B2316089 : Blo 1543469 2316089 := bstep (se 2 (by rfl) ⟨868533, by rfl⟩ : syracuseStep 2316089 = 1737067) B1737067
theorem B7419707 : Blo 1543469 7419707 := bstep (se 1 (by rfl) ⟨5564780, by rfl⟩ : syracuseStep 7419707 = 11129561) B11129561
theorem B27121483 : Blo 1543469 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B16701299 : Blo 1543469 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B2316167 : Blo 1543469 2316167 := bstep (se 1 (by rfl) ⟨1737125, by rfl⟩ : syracuseStep 2316167 = 3474251) B3474251
theorem B2316203 : Blo 1543469 2316203 := bstep (se 1 (by rfl) ⟨1737152, by rfl⟩ : syracuseStep 2316203 = 3474305) B3474305
theorem B1955755 : Blo 1543469 1955755 := bstep (se 1 (by rfl) ⟨1466816, by rfl⟩ : syracuseStep 1955755 = 2933633) B2933633
theorem B2316233 : Blo 1543469 2316233 := bstep (se 2 (by rfl) ⟨868587, by rfl⟩ : syracuseStep 2316233 = 1737175) B1737175
theorem B2316347 : Blo 1543469 2316347 := bstep (se 1 (by rfl) ⟨1737260, by rfl⟩ : syracuseStep 2316347 = 3474521) B3474521
theorem B8353853 : Blo 1543469 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B2316407 : Blo 1543469 2316407 := bstep (se 1 (by rfl) ⟨1737305, by rfl⟩ : syracuseStep 2316407 = 3474611) B3474611
theorem B2316431 : Blo 1543469 2316431 := bstep (se 1 (by rfl) ⟨1737323, by rfl⟩ : syracuseStep 2316431 = 3474647) B3474647
theorem B1955983 : Blo 1543469 1955983 := bstep (se 1 (by rfl) ⟨1466987, by rfl⟩ : syracuseStep 1955983 = 2933975) B2933975
theorem B2316473 : Blo 1543469 2316473 := bstep (se 2 (by rfl) ⟨868677, by rfl⟩ : syracuseStep 2316473 = 1737355) B1737355
theorem B4757705 : Blo 1543469 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B16701641 : Blo 1543469 16701641 := bstep (se 2 (by rfl) ⟨6263115, by rfl⟩ : syracuseStep 16701641 = 12526231) B12526231
theorem B2316551 : Blo 1543469 2316551 := bstep (se 1 (by rfl) ⟨1737413, by rfl⟩ : syracuseStep 2316551 = 3474827) B3474827
theorem B2316587 : Blo 1543469 2316587 := bstep (se 1 (by rfl) ⟨1737440, by rfl⟩ : syracuseStep 2316587 = 3474881) B3474881
theorem B2316617 : Blo 1543469 2316617 := bstep (se 2 (by rfl) ⟨868731, by rfl⟩ : syracuseStep 2316617 = 1737463) B1737463
theorem B7821683 : Blo 1543469 7821683 := bstep (se 1 (by rfl) ⟨5866262, by rfl⟩ : syracuseStep 7821683 = 11732525) B11732525
theorem B4397465 : Blo 1543469 4397465 := bstep (se 2 (by rfl) ⟨1649049, by rfl⟩ : syracuseStep 4397465 = 3298099) B3298099
theorem B5282233 : Blo 1543469 5282233 := bstep (se 2 (by rfl) ⟨1980837, by rfl⟩ : syracuseStep 5282233 = 3961675) B3961675
theorem B2316731 : Blo 1543469 2316731 := bstep (se 1 (by rfl) ⟨1737548, by rfl⟩ : syracuseStep 2316731 = 3475097) B3475097
theorem B2316791 : Blo 1543469 2316791 := bstep (se 1 (by rfl) ⟨1737593, by rfl⟩ : syracuseStep 2316791 = 3475187) B3475187
theorem B2316815 : Blo 1543469 2316815 := bstep (se 1 (by rfl) ⟨1737611, by rfl⟩ : syracuseStep 2316815 = 3475223) B3475223
theorem B2316857 : Blo 1543469 2316857 := bstep (se 2 (by rfl) ⟨868821, by rfl⟩ : syracuseStep 2316857 = 1737643) B1737643
theorem B23788151 : Blo 1543469 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B2316935 : Blo 1543469 2316935 := bstep (se 1 (by rfl) ⟨1737701, by rfl⟩ : syracuseStep 2316935 = 3475403) B3475403
theorem B2316971 : Blo 1543469 2316971 := bstep (se 1 (by rfl) ⟨1737728, by rfl⟩ : syracuseStep 2316971 = 3475457) B3475457
theorem B2931385 : Blo 1543469 2931385 := bstep (se 2 (by rfl) ⟨1099269, by rfl⟩ : syracuseStep 2931385 = 2198539) B2198539
theorem B2317001 : Blo 1543469 2317001 := bstep (se 2 (by rfl) ⟨868875, by rfl⟩ : syracuseStep 2317001 = 1737751) B1737751
theorem B6265615 : Blo 1543469 6265615 := bstep (se 1 (by rfl) ⟨4699211, by rfl⟩ : syracuseStep 6265615 = 9398423) B9398423
theorem B9894707 : Blo 1543469 9894707 := bstep (se 1 (by rfl) ⟨7421030, by rfl⟩ : syracuseStep 9894707 = 14842061) B14842061
theorem B2317115 : Blo 1543469 2317115 := bstep (se 1 (by rfl) ⟨1737836, by rfl⟩ : syracuseStep 2317115 = 3475673) B3475673
theorem B7822169 : Blo 1543469 7822169 := bstep (se 2 (by rfl) ⟨2933313, by rfl⟩ : syracuseStep 7822169 = 5866627) B5866627
theorem B6593395 : Blo 1543469 6593395 := bstep (se 1 (by rfl) ⟨4945046, by rfl⟩ : syracuseStep 6593395 = 9890093) B9890093
theorem B2317175 : Blo 1543469 2317175 := bstep (se 1 (by rfl) ⟨1737881, by rfl⟩ : syracuseStep 2317175 = 3475763) B3475763
theorem B2317199 : Blo 1543469 2317199 := bstep (se 1 (by rfl) ⟨1737899, by rfl⟩ : syracuseStep 2317199 = 3475799) B3475799
theorem B2317241 : Blo 1543469 2317241 := bstep (se 2 (by rfl) ⟨868965, by rfl⟩ : syracuseStep 2317241 = 1737931) B1737931
theorem B2317319 : Blo 1543469 2317319 := bstep (se 1 (by rfl) ⟨1737989, by rfl⟩ : syracuseStep 2317319 = 3475979) B3475979
theorem B2931727 : Blo 1543469 2931727 := bstep (se 1 (by rfl) ⟨2198795, by rfl⟩ : syracuseStep 2931727 = 4397591) B4397591
theorem B8797207 : Blo 1543469 8797207 := bstep (se 1 (by rfl) ⟨6597905, by rfl⟩ : syracuseStep 8797207 = 13195811) B13195811
theorem B2317355 : Blo 1543469 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B2784299 : Blo 1543469 2784299 := bstep (se 1 (by rfl) ⟨2088224, by rfl⟩ : syracuseStep 2784299 = 4176449) B4176449
theorem B14851133 : Blo 1543469 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B2317385 : Blo 1543469 2317385 := bstep (se 2 (by rfl) ⟨869019, by rfl⟩ : syracuseStep 2317385 = 1738039) B1738039
theorem B7814231 : Blo 1543469 7814231 := bstep (se 1 (by rfl) ⟨5860673, by rfl⟩ : syracuseStep 7814231 = 11721347) B11721347
theorem B2317499 : Blo 1543469 2317499 := bstep (se 1 (by rfl) ⟨1738124, by rfl⟩ : syracuseStep 2317499 = 3476249) B3476249
theorem B6593737 : Blo 1543469 6593737 := bstep (se 2 (by rfl) ⟨2472651, by rfl⟩ : syracuseStep 6593737 = 4945303) B4945303
theorem B2317559 : Blo 1543469 2317559 := bstep (se 1 (by rfl) ⟨1738169, by rfl⟩ : syracuseStep 2317559 = 3476339) B3476339
theorem B2317583 : Blo 1543469 2317583 := bstep (se 1 (by rfl) ⟨1738187, by rfl⟩ : syracuseStep 2317583 = 3476375) B3476375
theorem B2317625 : Blo 1543469 2317625 := bstep (se 2 (by rfl) ⟨869109, by rfl⟩ : syracuseStep 2317625 = 1738219) B1738219
theorem B3710323 : Blo 1543469 3710323 := bstep (se 1 (by rfl) ⟨2782742, by rfl⟩ : syracuseStep 3710323 = 5565485) B5565485
theorem B2317703 : Blo 1543469 2317703 := bstep (se 1 (by rfl) ⟨1738277, by rfl⟩ : syracuseStep 2317703 = 3476555) B3476555
theorem B2317739 : Blo 1543469 2317739 := bstep (se 1 (by rfl) ⟨1738304, by rfl⟩ : syracuseStep 2317739 = 3476609) B3476609
theorem B2317769 : Blo 1543469 2317769 := bstep (se 2 (by rfl) ⟨869163, by rfl⟩ : syracuseStep 2317769 = 1738327) B1738327
theorem B9387523 : Blo 1543469 9387523 := bstep (se 1 (by rfl) ⟨7040642, by rfl⟩ : syracuseStep 9387523 = 14081285) B14081285
theorem B4177423 : Blo 1543469 4177423 := bstep (se 1 (by rfl) ⟨3133067, by rfl⟩ : syracuseStep 4177423 = 6266135) B6266135
theorem B3472955 : Blo 1543469 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B2317883 : Blo 1543469 2317883 := bstep (se 1 (by rfl) ⟨1738412, by rfl⟩ : syracuseStep 2317883 = 3476825) B3476825
theorem B7814717 : Blo 1543469 7814717 := bstep (se 3 (by rfl) ⟨1465259, by rfl⟩ : syracuseStep 7814717 = 2930519) B2930519
theorem B10567235 : Blo 1543469 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B3907187 : Blo 1543469 3907187 := bstep (se 1 (by rfl) ⟨2930390, by rfl⟩ : syracuseStep 3907187 = 5860781) B5860781
theorem B3620471 : Blo 1543469 3620471 := bstep (se 1 (by rfl) ⟨2715353, by rfl⟩ : syracuseStep 3620471 = 5430707) B5430707
theorem B2317943 : Blo 1543469 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B2317967 : Blo 1543469 2317967 := bstep (se 1 (by rfl) ⟨1738475, by rfl⟩ : syracuseStep 2317967 = 3476951) B3476951
theorem B3473081 : Blo 1543469 3473081 := bstep (se 2 (by rfl) ⟨1302405, by rfl⟩ : syracuseStep 3473081 = 2604811) B2604811
theorem B2318009 : Blo 1543469 2318009 := bstep (se 2 (by rfl) ⟨869253, by rfl⟩ : syracuseStep 2318009 = 1738507) B1738507
theorem B4947713 : Blo 1543469 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B1736455 : Blo 1543469 1736455 := bstep (se 1 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 1736455 = 2604683) B2604683
theorem B2318087 : Blo 1543469 2318087 := bstep (se 1 (by rfl) ⟨1738565, by rfl⟩ : syracuseStep 2318087 = 3477131) B3477131
theorem B4398877 : Blo 1543469 4398877 := bstep (se 3 (by rfl) ⟨824789, by rfl⟩ : syracuseStep 4398877 = 1649579) B1649579
theorem B2318123 : Blo 1543469 2318123 := bstep (se 1 (by rfl) ⟨1738592, by rfl⟩ : syracuseStep 2318123 = 3477185) B3477185
theorem B2318153 : Blo 1543469 2318153 := bstep (se 2 (by rfl) ⟨869307, by rfl⟩ : syracuseStep 2318153 = 1738615) B1738615
theorem B2604919 : Blo 1543469 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B2932615 : Blo 1543469 2932615 := bstep (se 1 (by rfl) ⟨2199461, by rfl⟩ : syracuseStep 2932615 = 4398923) B4398923
theorem B1736635 : Blo 1543469 1736635 := bstep (se 1 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 1736635 = 2604953) B2604953
theorem B4399049 : Blo 1543469 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B5865473 : Blo 1543469 5865473 := bstep (se 2 (by rfl) ⟨2199552, by rfl⟩ : syracuseStep 5865473 = 4399105) B4399105
theorem B1736743 : Blo 1543469 1736743 := bstep (se 1 (by rfl) ⟨1302557, by rfl⟩ : syracuseStep 1736743 = 2605115) B2605115
theorem B42270781 : Blo 1543469 42270781 := bstep (se 3 (by rfl) ⟨7925771, by rfl⟩ : syracuseStep 42270781 = 15851543) B15851543
theorem B2605135 : Blo 1543469 2605135 := bstep (se 1 (by rfl) ⟨1953851, by rfl⟩ : syracuseStep 2605135 = 3907703) B3907703
theorem B9896093 : Blo 1543469 9896093 := bstep (se 3 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 9896093 = 3711035) B3711035
theorem B11886755 : Blo 1543469 11886755 := bstep (se 1 (by rfl) ⟨8915066, by rfl⟩ : syracuseStep 11886755 = 17830133) B17830133
theorem B7823627 : Blo 1543469 7823627 := bstep (se 1 (by rfl) ⟨5867720, by rfl⟩ : syracuseStep 7823627 = 11735441) B11735441
theorem B2605385 : Blo 1543469 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B5865929 : Blo 1543469 5865929 := bstep (se 2 (by rfl) ⟨2199723, by rfl⟩ : syracuseStep 5865929 = 4399447) B4399447
theorem B7815689 : Blo 1543469 7815689 := bstep (se 2 (by rfl) ⟨2930883, by rfl⟩ : syracuseStep 7815689 = 5861767) B5861767
theorem B12526103 : Blo 1543469 12526103 := bstep (se 1 (by rfl) ⟨9394577, by rfl⟩ : syracuseStep 12526103 = 18789155) B18789155
theorem B3474017 : Blo 1543469 3474017 := bstep (se 2 (by rfl) ⟨1302756, by rfl⟩ : syracuseStep 3474017 = 2605513) B2605513
theorem B2605817 : Blo 1543469 2605817 := bstep (se 2 (by rfl) ⟨977181, by rfl⟩ : syracuseStep 2605817 = 1954363) B1954363
theorem B5210999 : Blo 1543469 5210999 := bstep (se 1 (by rfl) ⟨3908249, by rfl⟩ : syracuseStep 5210999 = 7816499) B7816499
theorem B3908513 : Blo 1543469 3908513 := bstep (se 2 (by rfl) ⟨1465692, by rfl⟩ : syracuseStep 3908513 = 2931385) B2931385
theorem B2605999 : Blo 1543469 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B5866415 : Blo 1543469 5866415 := bstep (se 1 (by rfl) ⟨4399811, by rfl⟩ : syracuseStep 5866415 = 8799623) B8799623
theorem B3474359 : Blo 1543469 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B11723777 : Blo 1543469 11723777 := bstep (se 2 (by rfl) ⟨4396416, by rfl⟩ : syracuseStep 11723777 = 8792833) B8792833
theorem B2606087 : Blo 1543469 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B5211215 : Blo 1543469 5211215 := bstep (se 1 (by rfl) ⟨3908411, by rfl⟩ : syracuseStep 5211215 = 7816823) B7816823
theorem B5284943 : Blo 1543469 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B8791193 : Blo 1543469 8791193 := bstep (se 2 (by rfl) ⟨3296697, by rfl⟩ : syracuseStep 8791193 = 6593395) B6593395
theorem B11134199 : Blo 1543469 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B2606431 : Blo 1543469 2606431 := bstep (se 1 (by rfl) ⟨1954823, by rfl⟩ : syracuseStep 2606431 = 3909647) B3909647
theorem B3908969 : Blo 1543469 3908969 := bstep (se 2 (by rfl) ⟨1465863, by rfl⟩ : syracuseStep 3908969 = 2931727) B2931727
theorem B2475407 : Blo 1543469 2475407 := bstep (se 1 (by rfl) ⟨1856555, by rfl⟩ : syracuseStep 2475407 = 3713111) B3713111
theorem B2606519 : Blo 1543469 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B5211593 : Blo 1543469 5211593 := bstep (se 2 (by rfl) ⟨1954347, by rfl⟩ : syracuseStep 5211593 = 3908695) B3908695
theorem B3171803 : Blo 1543469 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B11134427 : Blo 1543469 11134427 := bstep (se 1 (by rfl) ⟨8350820, by rfl⟩ : syracuseStep 11134427 = 16701641) B16701641
theorem B3474953 : Blo 1543469 3474953 := bstep (se 2 (by rfl) ⟨1303107, by rfl⟩ : syracuseStep 3474953 = 2606215) B2606215
theorem B8791649 : Blo 1543469 8791649 := bstep (se 2 (by rfl) ⟨3296868, by rfl⟩ : syracuseStep 8791649 = 6593737) B6593737
theorem B1738363 : Blo 1543469 1738363 := bstep (se 1 (by rfl) ⟨1303772, by rfl⟩ : syracuseStep 1738363 = 2607545) B2607545
theorem B5211863 : Blo 1543469 5211863 := bstep (se 1 (by rfl) ⟨3908897, by rfl⟩ : syracuseStep 5211863 = 7817795) B7817795
theorem B3475295 : Blo 1543469 3475295 := bstep (se 1 (by rfl) ⟨2606471, by rfl⟩ : syracuseStep 3475295 = 5212943) B5212943
theorem B6596471 : Blo 1543469 6596471 := bstep (se 1 (by rfl) ⟨4947353, by rfl⟩ : syracuseStep 6596471 = 9894707) B9894707
theorem B5212079 : Blo 1543469 5212079 := bstep (se 1 (by rfl) ⟨3909059, by rfl⟩ : syracuseStep 5212079 = 7818119) B7818119
theorem B7817147 : Blo 1543469 7817147 := bstep (se 1 (by rfl) ⟨5862860, by rfl⟩ : syracuseStep 7817147 = 11725721) B11725721
theorem B2607113 : Blo 1543469 2607113 := bstep (se 2 (by rfl) ⟨977667, by rfl⟩ : syracuseStep 2607113 = 1955335) B1955335
theorem B3475475 : Blo 1543469 3475475 := bstep (se 1 (by rfl) ⟨2606606, by rfl⟩ : syracuseStep 3475475 = 5213213) B5213213
theorem B10561565 : Blo 1543469 10561565 := bstep (se 3 (by rfl) ⟨1980293, by rfl⟩ : syracuseStep 10561565 = 3960587) B3960587
theorem B5867599 : Blo 1543469 5867599 := bstep (se 1 (by rfl) ⟨4400699, by rfl⟩ : syracuseStep 5867599 = 8801399) B8801399
theorem B4950173 : Blo 1543469 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B2607275 : Blo 1543469 2607275 := bstep (se 1 (by rfl) ⟨1955456, by rfl⟩ : syracuseStep 2607275 = 3910913) B3910913
theorem B14838065 : Blo 1543469 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B3475817 : Blo 1543469 3475817 := bstep (se 2 (by rfl) ⟨1303431, by rfl⟩ : syracuseStep 3475817 = 2606863) B2606863
theorem B2197867 : Blo 1543469 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B36161977 : Blo 1543469 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B3910153 : Blo 1543469 3910153 := bstep (se 2 (by rfl) ⟨1466307, by rfl⟩ : syracuseStep 3910153 = 2932615) B2932615
theorem B2607673 : Blo 1543469 2607673 := bstep (se 2 (by rfl) ⟨977877, by rfl⟩ : syracuseStep 2607673 = 1955755) B1955755
theorem B3173035 : Blo 1543469 3173035 := bstep (se 1 (by rfl) ⟨2379776, by rfl⟩ : syracuseStep 3173035 = 4759553) B4759553
theorem B2607815 : Blo 1543469 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B7424797 : Blo 1543469 7424797 := bstep (se 3 (by rfl) ⟨1392149, by rfl⟩ : syracuseStep 7424797 = 2784299) B2784299
theorem B2607977 : Blo 1543469 2607977 := bstep (se 2 (by rfl) ⟨977991, by rfl⟩ : syracuseStep 2607977 = 1955983) B1955983
theorem B3476411 : Blo 1543469 3476411 := bstep (se 1 (by rfl) ⟨2607308, by rfl⟩ : syracuseStep 3476411 = 5214617) B5214617
theorem B8793107 : Blo 1543469 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B3476537 : Blo 1543469 3476537 := bstep (se 2 (by rfl) ⟨1303701, by rfl⟩ : syracuseStep 3476537 = 2607403) B2607403
theorem B5287027 : Blo 1543469 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B7818443 : Blo 1543469 7818443 := bstep (se 1 (by rfl) ⟨5863832, by rfl⟩ : syracuseStep 7818443 = 11727665) B11727665
theorem B1543503 : Blo 1543469 1543503 := bstep (se 1 (by rfl) ⟨1157627, by rfl⟩ : syracuseStep 1543503 = 2315255) B2315255
theorem B1543519 : Blo 1543469 1543519 := bstep (se 1 (by rfl) ⟨1157639, by rfl⟩ : syracuseStep 1543519 = 2315279) B2315279
theorem B1543547 : Blo 1543469 1543547 := bstep (se 1 (by rfl) ⟨1157660, by rfl⟩ : syracuseStep 1543547 = 2315321) B2315321
theorem B3476879 : Blo 1543469 3476879 := bstep (se 1 (by rfl) ⟨2607659, by rfl⟩ : syracuseStep 3476879 = 5215319) B5215319
theorem B1543599 : Blo 1543469 1543599 := bstep (se 1 (by rfl) ⟨1157699, by rfl⟩ : syracuseStep 1543599 = 2315399) B2315399
theorem B1543623 : Blo 1543469 1543623 := bstep (se 1 (by rfl) ⟨1157717, by rfl⟩ : syracuseStep 1543623 = 2315435) B2315435
theorem B1543643 : Blo 1543469 1543643 := bstep (se 1 (by rfl) ⟨1157732, by rfl⟩ : syracuseStep 1543643 = 2315465) B2315465
theorem B60182003 : Blo 1543469 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B1543719 : Blo 1543469 1543719 := bstep (se 1 (by rfl) ⟨1157789, by rfl⟩ : syracuseStep 1543719 = 2315579) B2315579
theorem B39562829 : Blo 1543469 39562829 := bstep (se 3 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 39562829 = 14836061) B14836061
theorem B1543759 : Blo 1543469 1543759 := bstep (se 1 (by rfl) ⟨1157819, by rfl⟩ : syracuseStep 1543759 = 2315639) B2315639
theorem B1543775 : Blo 1543469 1543775 := bstep (se 1 (by rfl) ⟨1157831, by rfl⟩ : syracuseStep 1543775 = 2315663) B2315663
theorem B1543803 : Blo 1543469 1543803 := bstep (se 1 (by rfl) ⟨1157852, by rfl⟩ : syracuseStep 1543803 = 2315705) B2315705
theorem B1543855 : Blo 1543469 1543855 := bstep (se 1 (by rfl) ⟨1157891, by rfl⟩ : syracuseStep 1543855 = 2315783) B2315783
theorem B1543879 : Blo 1543469 1543879 := bstep (se 1 (by rfl) ⟨1157909, by rfl⟩ : syracuseStep 1543879 = 2315819) B2315819
theorem B3477203 : Blo 1543469 3477203 := bstep (se 1 (by rfl) ⟨2607902, by rfl⟩ : syracuseStep 3477203 = 5215805) B5215805
theorem B1543899 : Blo 1543469 1543899 := bstep (se 1 (by rfl) ⟨1157924, by rfl⟩ : syracuseStep 1543899 = 2315849) B2315849
theorem B1543975 : Blo 1543469 1543975 := bstep (se 1 (by rfl) ⟨1157981, by rfl⟩ : syracuseStep 1543975 = 2315963) B2315963
theorem B1544015 : Blo 1543469 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B1544031 : Blo 1543469 1544031 := bstep (se 1 (by rfl) ⟨1158023, by rfl⟩ : syracuseStep 1544031 = 2316047) B2316047
theorem B1544059 : Blo 1543469 1544059 := bstep (se 1 (by rfl) ⟨1158044, by rfl⟩ : syracuseStep 1544059 = 2316089) B2316089
theorem B5861281 : Blo 1543469 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B1544111 : Blo 1543469 1544111 := bstep (se 1 (by rfl) ⟨1158083, by rfl⟩ : syracuseStep 1544111 = 2316167) B2316167
theorem B3911611 : Blo 1543469 3911611 := bstep (se 1 (by rfl) ⟨2933708, by rfl⟩ : syracuseStep 3911611 = 5867417) B5867417
theorem B1544135 : Blo 1543469 1544135 := bstep (se 1 (by rfl) ⟨1158101, by rfl⟩ : syracuseStep 1544135 = 2316203) B2316203
theorem B1544155 : Blo 1543469 1544155 := bstep (se 1 (by rfl) ⟨1158116, by rfl⟩ : syracuseStep 1544155 = 2316233) B2316233
theorem B8581135 : Blo 1543469 8581135 := bstep (se 1 (by rfl) ⟨6435851, by rfl⟩ : syracuseStep 8581135 = 12871703) B12871703
theorem B19804175 : Blo 1543469 19804175 := bstep (se 1 (by rfl) ⟨14853131, by rfl⟩ : syracuseStep 19804175 = 29706263) B29706263
theorem B1544231 : Blo 1543469 1544231 := bstep (se 1 (by rfl) ⟨1158173, by rfl⟩ : syracuseStep 1544231 = 2316347) B2316347
theorem B8917049 : Blo 1543469 8917049 := bstep (se 2 (by rfl) ⟨3343893, by rfl⟩ : syracuseStep 8917049 = 6687787) B6687787
theorem B1544271 : Blo 1543469 1544271 := bstep (se 1 (by rfl) ⟨1158203, by rfl⟩ : syracuseStep 1544271 = 2316407) B2316407
theorem B1544287 : Blo 1543469 1544287 := bstep (se 1 (by rfl) ⟨1158215, by rfl⟩ : syracuseStep 1544287 = 2316431) B2316431
theorem B1544315 : Blo 1543469 1544315 := bstep (se 1 (by rfl) ⟨1158236, by rfl⟩ : syracuseStep 1544315 = 2316473) B2316473
theorem B1544367 : Blo 1543469 1544367 := bstep (se 1 (by rfl) ⟨1158275, by rfl⟩ : syracuseStep 1544367 = 2316551) B2316551
theorem B1544391 : Blo 1543469 1544391 := bstep (se 1 (by rfl) ⟨1158293, by rfl⟩ : syracuseStep 1544391 = 2316587) B2316587
theorem B1544411 : Blo 1543469 1544411 := bstep (se 1 (by rfl) ⟨1158308, by rfl⟩ : syracuseStep 1544411 = 2316617) B2316617
theorem B5214455 : Blo 1543469 5214455 := bstep (se 1 (by rfl) ⟨3910841, by rfl⟩ : syracuseStep 5214455 = 7821683) B7821683
theorem B1544487 : Blo 1543469 1544487 := bstep (se 1 (by rfl) ⟨1158365, by rfl⟩ : syracuseStep 1544487 = 2316731) B2316731
theorem B9654589 : Blo 1543469 9654589 := bstep (se 3 (by rfl) ⟨1810235, by rfl⟩ : syracuseStep 9654589 = 3620471) B3620471
theorem B1544527 : Blo 1543469 1544527 := bstep (se 1 (by rfl) ⟨1158395, by rfl⟩ : syracuseStep 1544527 = 2316791) B2316791
theorem B6598999 : Blo 1543469 6598999 := bstep (se 1 (by rfl) ⟨4949249, by rfl⟩ : syracuseStep 6598999 = 9898499) B9898499
theorem B1544543 : Blo 1543469 1544543 := bstep (se 1 (by rfl) ⟨1158407, by rfl⟩ : syracuseStep 1544543 = 2316815) B2316815
theorem B1544571 : Blo 1543469 1544571 := bstep (se 1 (by rfl) ⟨1158428, by rfl⟩ : syracuseStep 1544571 = 2316857) B2316857
theorem B1544623 : Blo 1543469 1544623 := bstep (se 1 (by rfl) ⟨1158467, by rfl⟩ : syracuseStep 1544623 = 2316935) B2316935
theorem B1544647 : Blo 1543469 1544647 := bstep (se 1 (by rfl) ⟨1158485, by rfl⟩ : syracuseStep 1544647 = 2316971) B2316971
theorem B1544667 : Blo 1543469 1544667 := bstep (se 1 (by rfl) ⟨1158500, by rfl⟩ : syracuseStep 1544667 = 2317001) B2317001
theorem B1544743 : Blo 1543469 1544743 := bstep (se 1 (by rfl) ⟨1158557, by rfl⟩ : syracuseStep 1544743 = 2317115) B2317115
theorem B5214779 : Blo 1543469 5214779 := bstep (se 1 (by rfl) ⟨3911084, by rfl⟩ : syracuseStep 5214779 = 7822169) B7822169
theorem B1544783 : Blo 1543469 1544783 := bstep (se 1 (by rfl) ⟨1158587, by rfl⟩ : syracuseStep 1544783 = 2317175) B2317175
theorem B1544799 : Blo 1543469 1544799 := bstep (se 1 (by rfl) ⟨1158599, by rfl⟩ : syracuseStep 1544799 = 2317199) B2317199
theorem B4174459 : Blo 1543469 4174459 := bstep (se 1 (by rfl) ⟨3130844, by rfl⟩ : syracuseStep 4174459 = 6261689) B6261689
theorem B1544827 : Blo 1543469 1544827 := bstep (se 1 (by rfl) ⟨1158620, by rfl⟩ : syracuseStep 1544827 = 2317241) B2317241
theorem B1544879 : Blo 1543469 1544879 := bstep (se 1 (by rfl) ⟨1158659, by rfl⟩ : syracuseStep 1544879 = 2317319) B2317319
theorem B1544903 : Blo 1543469 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B9900755 : Blo 1543469 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B1544923 : Blo 1543469 1544923 := bstep (se 1 (by rfl) ⟨1158692, by rfl⟩ : syracuseStep 1544923 = 2317385) B2317385
theorem B1544999 : Blo 1543469 1544999 := bstep (se 1 (by rfl) ⟨1158749, by rfl⟩ : syracuseStep 1544999 = 2317499) B2317499
theorem B5215049 : Blo 1543469 5215049 := bstep (se 2 (by rfl) ⟨1955643, by rfl⟩ : syracuseStep 5215049 = 3911287) B3911287
theorem B1545039 : Blo 1543469 1545039 := bstep (se 1 (by rfl) ⟨1158779, by rfl⟩ : syracuseStep 1545039 = 2317559) B2317559
theorem B5862239 : Blo 1543469 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B1545055 : Blo 1543469 1545055 := bstep (se 1 (by rfl) ⟨1158791, by rfl⟩ : syracuseStep 1545055 = 2317583) B2317583
theorem B5862253 : Blo 1543469 5862253 := bstep (se 3 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 5862253 = 2198345) B2198345
theorem B1545083 : Blo 1543469 1545083 := bstep (se 1 (by rfl) ⟨1158812, by rfl⟩ : syracuseStep 1545083 = 2317625) B2317625
theorem B1545135 : Blo 1543469 1545135 := bstep (se 1 (by rfl) ⟨1158851, by rfl⟩ : syracuseStep 1545135 = 2317703) B2317703
theorem B1545159 : Blo 1543469 1545159 := bstep (se 1 (by rfl) ⟨1158869, by rfl⟩ : syracuseStep 1545159 = 2317739) B2317739
theorem B1545179 : Blo 1543469 1545179 := bstep (se 1 (by rfl) ⟨1158884, by rfl⟩ : syracuseStep 1545179 = 2317769) B2317769
theorem B2315273 : Blo 1543469 2315273 := bstep (se 2 (by rfl) ⟨868227, by rfl⟩ : syracuseStep 2315273 = 1736455) B1736455
theorem B2315303 : Blo 1543469 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B1545255 : Blo 1543469 1545255 := bstep (se 1 (by rfl) ⟨1158941, by rfl⟩ : syracuseStep 1545255 = 2317883) B2317883
theorem B1545295 : Blo 1543469 1545295 := bstep (se 1 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 1545295 = 2317943) B2317943
theorem B1545311 : Blo 1543469 1545311 := bstep (se 1 (by rfl) ⟨1158983, by rfl⟩ : syracuseStep 1545311 = 2317967) B2317967
theorem B2315387 : Blo 1543469 2315387 := bstep (se 1 (by rfl) ⟨1736540, by rfl⟩ : syracuseStep 2315387 = 3473081) B3473081
theorem B1545339 : Blo 1543469 1545339 := bstep (se 1 (by rfl) ⟨1159004, by rfl⟩ : syracuseStep 1545339 = 2318009) B2318009
theorem B4396189 : Blo 1543469 4396189 := bstep (se 3 (by rfl) ⟨824285, by rfl⟩ : syracuseStep 4396189 = 1648571) B1648571
theorem B5862557 : Blo 1543469 5862557 := bstep (se 3 (by rfl) ⟨1099229, by rfl⟩ : syracuseStep 5862557 = 2198459) B2198459
theorem B14087339 : Blo 1543469 14087339 := bstep (se 1 (by rfl) ⟨10565504, by rfl⟩ : syracuseStep 14087339 = 21131009) B21131009
theorem B3298475 : Blo 1543469 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B1545391 : Blo 1543469 1545391 := bstep (se 1 (by rfl) ⟨1159043, by rfl⟩ : syracuseStep 1545391 = 2318087) B2318087
theorem B1545415 : Blo 1543469 1545415 := bstep (se 1 (by rfl) ⟨1159061, by rfl⟩ : syracuseStep 1545415 = 2318123) B2318123
theorem B1545435 : Blo 1543469 1545435 := bstep (se 1 (by rfl) ⟨1159076, by rfl⟩ : syracuseStep 1545435 = 2318153) B2318153
theorem B2315513 : Blo 1543469 2315513 := bstep (se 2 (by rfl) ⟨868317, by rfl⟩ : syracuseStep 2315513 = 1736635) B1736635
theorem B11728151 : Blo 1543469 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B2315615 : Blo 1543469 2315615 := bstep (se 1 (by rfl) ⟨1736711, by rfl⟩ : syracuseStep 2315615 = 3473423) B3473423
theorem B2315627 : Blo 1543469 2315627 := bstep (se 1 (by rfl) ⟨1736720, by rfl⟩ : syracuseStep 2315627 = 3473441) B3473441
theorem B8353243 : Blo 1543469 8353243 := bstep (se 1 (by rfl) ⟨6264932, by rfl⟩ : syracuseStep 8353243 = 12529865) B12529865
theorem B4396531 : Blo 1543469 4396531 := bstep (se 1 (by rfl) ⟨3297398, by rfl⟩ : syracuseStep 4396531 = 6594797) B6594797
theorem B2930185 : Blo 1543469 2930185 := bstep (se 2 (by rfl) ⟨1098819, by rfl⟩ : syracuseStep 2930185 = 2197639) B2197639
theorem B2315855 : Blo 1543469 2315855 := bstep (se 1 (by rfl) ⟨1736891, by rfl⟩ : syracuseStep 2315855 = 3473783) B3473783
theorem B4232843 : Blo 1543469 4232843 := bstep (se 1 (by rfl) ⟨3174632, by rfl⟩ : syracuseStep 4232843 = 6349265) B6349265
theorem B9524881 : Blo 1543469 9524881 := bstep (se 2 (by rfl) ⟨3571830, by rfl⟩ : syracuseStep 9524881 = 7143661) B7143661
theorem B2315975 : Blo 1543469 2315975 := bstep (se 1 (by rfl) ⟨1736981, by rfl⟩ : syracuseStep 2315975 = 3473963) B3473963
theorem B5863211 : Blo 1543469 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B5945183 : Blo 1543469 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B2316137 : Blo 1543469 2316137 := bstep (se 2 (by rfl) ⟨868551, by rfl⟩ : syracuseStep 2316137 = 1737103) B1737103
theorem B8796023 : Blo 1543469 8796023 := bstep (se 1 (by rfl) ⟨6597017, by rfl⟩ : syracuseStep 8796023 = 13194035) B13194035
theorem B2316215 : Blo 1543469 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B16701389 : Blo 1543469 16701389 := bstep (se 3 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 16701389 = 6263021) B6263021
theorem B2316251 : Blo 1543469 2316251 := bstep (se 1 (by rfl) ⟨1737188, by rfl⟩ : syracuseStep 2316251 = 3474377) B3474377
theorem B21133315 : Blo 1543469 21133315 := bstep (se 1 (by rfl) ⟨15849986, by rfl⟩ : syracuseStep 21133315 = 31699973) B31699973
theorem B6600761 : Blo 1543469 6600761 := bstep (se 2 (by rfl) ⟨2475285, by rfl⟩ : syracuseStep 6600761 = 4950571) B4950571
theorem B16693337 : Blo 1543469 16693337 := bstep (se 2 (by rfl) ⟨6260001, by rfl⟩ : syracuseStep 16693337 = 12520003) B12520003
theorem B8796275 : Blo 1543469 8796275 := bstep (se 1 (by rfl) ⟨6597206, by rfl⟩ : syracuseStep 8796275 = 13194413) B13194413
theorem B11720861 : Blo 1543469 11720861 := bstep (se 3 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 11720861 = 4395323) B4395323
theorem B24107165 : Blo 1543469 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B6690973 : Blo 1543469 6690973 := bstep (se 3 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 6690973 = 2509115) B2509115
theorem B2930899 : Blo 1543469 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B8354153 : Blo 1543469 8354153 := bstep (se 2 (by rfl) ⟨3132807, by rfl⟩ : syracuseStep 8354153 = 6265615) B6265615
theorem B21141911 : Blo 1543469 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B2316719 : Blo 1543469 2316719 := bstep (se 1 (by rfl) ⟨1737539, by rfl⟩ : syracuseStep 2316719 = 3475079) B3475079
theorem B6265307 : Blo 1543469 6265307 := bstep (se 1 (by rfl) ⟨4698980, by rfl⟩ : syracuseStep 6265307 = 9397961) B9397961
theorem B2316809 : Blo 1543469 2316809 := bstep (se 2 (by rfl) ⟨868803, by rfl⟩ : syracuseStep 2316809 = 1737607) B1737607
theorem B22272545 : Blo 1543469 22272545 := bstep (se 2 (by rfl) ⟨8352204, by rfl⟩ : syracuseStep 22272545 = 16704409) B16704409
theorem B4946471 : Blo 1543469 4946471 := bstep (se 1 (by rfl) ⟨3709853, by rfl⟩ : syracuseStep 4946471 = 7419707) B7419707
theorem B2316839 : Blo 1543469 2316839 := bstep (se 1 (by rfl) ⟨1737629, by rfl⟩ : syracuseStep 2316839 = 3475259) B3475259
theorem B2316923 : Blo 1543469 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B11729609 : Blo 1543469 11729609 := bstep (se 2 (by rfl) ⟨4398603, by rfl⟩ : syracuseStep 11729609 = 8797207) B8797207
theorem B10033865 : Blo 1543469 10033865 := bstep (se 2 (by rfl) ⟨3762699, by rfl⟩ : syracuseStep 10033865 = 7525399) B7525399
theorem B5569235 : Blo 1543469 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B2317049 : Blo 1543469 2317049 := bstep (se 2 (by rfl) ⟨868893, by rfl⟩ : syracuseStep 2317049 = 1737787) B1737787
theorem B2317151 : Blo 1543469 2317151 := bstep (se 1 (by rfl) ⟨1737863, by rfl⟩ : syracuseStep 2317151 = 3475727) B3475727
theorem B2317163 : Blo 1543469 2317163 := bstep (se 1 (by rfl) ⟨1737872, by rfl⟩ : syracuseStep 2317163 = 3475745) B3475745
theorem B2931643 : Blo 1543469 2931643 := bstep (se 1 (by rfl) ⟨2198732, by rfl⟩ : syracuseStep 2931643 = 4397465) B4397465
theorem B2317391 : Blo 1543469 2317391 := bstep (se 1 (by rfl) ⟨1738043, by rfl⟩ : syracuseStep 2317391 = 3476087) B3476087
theorem B15858767 : Blo 1543469 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B4947097 : Blo 1543469 4947097 := bstep (se 2 (by rfl) ⟨1855161, by rfl⟩ : syracuseStep 4947097 = 3710323) B3710323
theorem B2317511 : Blo 1543469 2317511 := bstep (se 1 (by rfl) ⟨1738133, by rfl⟩ : syracuseStep 2317511 = 3476267) B3476267
theorem B12516697 : Blo 1543469 12516697 := bstep (se 2 (by rfl) ⟨4693761, by rfl⟩ : syracuseStep 12516697 = 9387523) B9387523
theorem B2317673 : Blo 1543469 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B5569897 : Blo 1543469 5569897 := bstep (se 2 (by rfl) ⟨2088711, by rfl⟩ : syracuseStep 5569897 = 4177423) B4177423
theorem B5209487 : Blo 1543469 5209487 := bstep (se 1 (by rfl) ⟨3907115, by rfl⟩ : syracuseStep 5209487 = 7814231) B7814231
theorem B19783055 : Blo 1543469 19783055 := bstep (se 1 (by rfl) ⟨14837291, by rfl⟩ : syracuseStep 19783055 = 29674583) B29674583
theorem B2932129 : Blo 1543469 2932129 := bstep (se 2 (by rfl) ⟨1099548, by rfl⟩ : syracuseStep 2932129 = 2199097) B2199097
theorem B2317751 : Blo 1543469 2317751 := bstep (se 1 (by rfl) ⟨1738313, by rfl⟩ : syracuseStep 2317751 = 3476627) B3476627
theorem B6594011 : Blo 1543469 6594011 := bstep (se 1 (by rfl) ⟨4945508, by rfl⟩ : syracuseStep 6594011 = 9891017) B9891017
theorem B2317787 : Blo 1543469 2317787 := bstep (se 1 (by rfl) ⟨1738340, by rfl⟩ : syracuseStep 2317787 = 3476681) B3476681
theorem B11280005 : Blo 1543469 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B28171909 : Blo 1543469 28171909 := bstep (se 4 (by rfl) ⟨2641116, by rfl⟩ : syracuseStep 28171909 = 5282233) B5282233
theorem B5865169 : Blo 1543469 5865169 := bstep (se 2 (by rfl) ⟨2199438, by rfl⟩ : syracuseStep 5865169 = 4398877) B4398877
theorem B5209811 : Blo 1543469 5209811 := bstep (se 1 (by rfl) ⟨3907358, by rfl⟩ : syracuseStep 5209811 = 7814717) B7814717
theorem B7044823 : Blo 1543469 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B2604791 : Blo 1543469 2604791 := bstep (se 1 (by rfl) ⟨1953593, by rfl⟩ : syracuseStep 2604791 = 3907187) B3907187
theorem B3473225 : Blo 1543469 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B3907511 : Blo 1543469 3907511 := bstep (se 1 (by rfl) ⟨2930633, by rfl⟩ : syracuseStep 3907511 = 5861267) B5861267
theorem B2932699 : Blo 1543469 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B56361041 : Blo 1543469 56361041 := bstep (se 2 (by rfl) ⟨21135390, by rfl⟩ : syracuseStep 56361041 = 42270781) B42270781
theorem B3473513 : Blo 1543469 3473513 := bstep (se 2 (by rfl) ⟨1302567, by rfl⟩ : syracuseStep 3473513 = 2605135) B2605135
theorem B7823465 : Blo 1543469 7823465 := bstep (se 2 (by rfl) ⟨2933799, by rfl⟩ : syracuseStep 7823465 = 5867599) B5867599
theorem B8921297 : Blo 1543469 8921297 := bstep (se 2 (by rfl) ⟨3345486, by rfl⟩ : syracuseStep 8921297 = 6690973) B6690973
theorem B1736923 : Blo 1543469 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B44515565 : Blo 1543469 44515565 := bstep (se 3 (by rfl) ⟨8346668, by rfl⟩ : syracuseStep 44515565 = 16693337) B16693337
theorem B3907865 : Blo 1543469 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B5210459 : Blo 1543469 5210459 := bstep (se 1 (by rfl) ⟨3907844, by rfl⟩ : syracuseStep 5210459 = 7815689) B7815689
theorem B8798665 : Blo 1543469 8798665 := bstep (se 2 (by rfl) ⟨3299499, by rfl⟩ : syracuseStep 8798665 = 6598999) B6598999
theorem B1737211 : Blo 1543469 1737211 := bstep (se 1 (by rfl) ⟨1302908, by rfl⟩ : syracuseStep 1737211 = 2605817) B2605817
theorem B3908159 : Blo 1543469 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B3473999 : Blo 1543469 3473999 := bstep (se 1 (by rfl) ⟨2605499, by rfl⟩ : syracuseStep 3473999 = 5210999) B5210999
theorem B2605675 : Blo 1543469 2605675 := bstep (se 1 (by rfl) ⟨1954256, by rfl⟩ : syracuseStep 2605675 = 3908513) B3908513
theorem B7815851 : Blo 1543469 7815851 := bstep (se 1 (by rfl) ⟨5861888, by rfl⟩ : syracuseStep 7815851 = 11723777) B11723777
theorem B1737391 : Blo 1543469 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B3474143 : Blo 1543469 3474143 := bstep (se 1 (by rfl) ⟨2605607, by rfl⟩ : syracuseStep 3474143 = 5211215) B5211215
theorem B3523295 : Blo 1543469 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B3908371 : Blo 1543469 3908371 := bstep (se 1 (by rfl) ⟨2931278, by rfl⟩ : syracuseStep 3908371 = 5862557) B5862557
theorem B7422799 : Blo 1543469 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B2605979 : Blo 1543469 2605979 := bstep (se 1 (by rfl) ⟨1954484, by rfl⟩ : syracuseStep 2605979 = 3908969) B3908969
theorem B1737679 : Blo 1543469 1737679 := bstep (se 1 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 1737679 = 2606519) B2606519
theorem B3474395 : Blo 1543469 3474395 := bstep (se 1 (by rfl) ⟨2605796, by rfl⟩ : syracuseStep 3474395 = 5211593) B5211593
theorem B3474575 : Blo 1543469 3474575 := bstep (se 1 (by rfl) ⟨2605931, by rfl⟩ : syracuseStep 3474575 = 5211863) B5211863
theorem B7816337 : Blo 1543469 7816337 := bstep (se 2 (by rfl) ⟨2931126, by rfl⟩ : syracuseStep 7816337 = 5862253) B5862253
theorem B3908807 : Blo 1543469 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B3474665 : Blo 1543469 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B3908857 : Blo 1543469 3908857 := bstep (se 2 (by rfl) ⟨1465821, by rfl⟩ : syracuseStep 3908857 = 2931643) B2931643
theorem B3474719 : Blo 1543469 3474719 := bstep (se 1 (by rfl) ⟨2606039, by rfl⟩ : syracuseStep 3474719 = 5212079) B5212079
theorem B5211431 : Blo 1543469 5211431 := bstep (se 1 (by rfl) ⟨3908573, by rfl⟩ : syracuseStep 5211431 = 7817147) B7817147
theorem B11134259 : Blo 1543469 11134259 := bstep (se 1 (by rfl) ⟨8350694, by rfl⟩ : syracuseStep 11134259 = 16701389) B16701389
theorem B1738075 : Blo 1543469 1738075 := bstep (se 1 (by rfl) ⟨1303556, by rfl⟩ : syracuseStep 1738075 = 2607113) B2607113
theorem B4400507 : Blo 1543469 4400507 := bstep (se 1 (by rfl) ⟨3300380, by rfl⟩ : syracuseStep 4400507 = 6600761) B6600761
theorem B1738183 : Blo 1543469 1738183 := bstep (se 1 (by rfl) ⟨1303637, by rfl⟩ : syracuseStep 1738183 = 2607275) B2607275
theorem B6596129 : Blo 1543469 6596129 := bstep (se 2 (by rfl) ⟨2473548, by rfl⟩ : syracuseStep 6596129 = 4947097) B4947097
theorem B16688929 : Blo 1543469 16688929 := bstep (se 2 (by rfl) ⟨6258348, by rfl⟩ : syracuseStep 16688929 = 12516697) B12516697
theorem B3475241 : Blo 1543469 3475241 := bstep (se 2 (by rfl) ⟨1303215, by rfl⟩ : syracuseStep 3475241 = 2606431) B2606431
theorem B1738543 : Blo 1543469 1738543 := bstep (se 1 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 1738543 = 2607815) B2607815
theorem B3712823 : Blo 1543469 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B3909505 : Blo 1543469 3909505 := bstep (se 2 (by rfl) ⟨1466064, by rfl⟩ : syracuseStep 3909505 = 2932129) B2932129
theorem B1738651 : Blo 1543469 1738651 := bstep (se 1 (by rfl) ⟨1303988, by rfl⟩ : syracuseStep 1738651 = 2607977) B2607977
theorem B5212295 : Blo 1543469 5212295 := bstep (se 1 (by rfl) ⟨3909221, by rfl⟩ : syracuseStep 5212295 = 7818443) B7818443
theorem B37562545 : Blo 1543469 37562545 := bstep (se 2 (by rfl) ⟨14085954, by rfl⟩ : syracuseStep 37562545 = 28171909) B28171909
theorem B12699841 : Blo 1543469 12699841 := bstep (se 2 (by rfl) ⟨4762440, by rfl⟩ : syracuseStep 12699841 = 9524881) B9524881
theorem B3910265 : Blo 1543469 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B3910315 : Blo 1543469 3910315 := bstep (se 1 (by rfl) ⟨2932736, by rfl⟩ : syracuseStep 3910315 = 5865473) B5865473
theorem B6597395 : Blo 1543469 6597395 := bstep (se 1 (by rfl) ⟨4948046, by rfl⟩ : syracuseStep 6597395 = 9896093) B9896093
theorem B3476303 : Blo 1543469 3476303 := bstep (se 1 (by rfl) ⟨2607227, by rfl⟩ : syracuseStep 3476303 = 5214455) B5214455
theorem B3910619 : Blo 1543469 3910619 := bstep (se 1 (by rfl) ⟨2932964, by rfl⟩ : syracuseStep 3910619 = 5865929) B5865929
theorem B3476519 : Blo 1543469 3476519 := bstep (se 1 (by rfl) ⟨2607389, by rfl⟩ : syracuseStep 3476519 = 5214779) B5214779
theorem B12872785 : Blo 1543469 12872785 := bstep (se 2 (by rfl) ⟨4827294, by rfl⟩ : syracuseStep 12872785 = 9654589) B9654589
theorem B31698013 : Blo 1543469 31698013 := bstep (se 3 (by rfl) ⟨5943377, by rfl⟩ : syracuseStep 31698013 = 11886755) B11886755
theorem B3476699 : Blo 1543469 3476699 := bstep (se 1 (by rfl) ⟨2607524, by rfl⟩ : syracuseStep 3476699 = 5215049) B5215049
theorem B3910943 : Blo 1543469 3910943 := bstep (se 1 (by rfl) ⟨2933207, by rfl⟩ : syracuseStep 3910943 = 5866415) B5866415
theorem B1543515 : Blo 1543469 1543515 := bstep (se 1 (by rfl) ⟨1157636, by rfl⟩ : syracuseStep 1543515 = 2315273) B2315273
theorem B5213537 : Blo 1543469 5213537 := bstep (se 2 (by rfl) ⟨1955076, by rfl⟩ : syracuseStep 5213537 = 3910153) B3910153
theorem B1543535 : Blo 1543469 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B3476897 : Blo 1543469 3476897 := bstep (se 2 (by rfl) ⟨1303836, by rfl⟩ : syracuseStep 3476897 = 2607673) B2607673
theorem B1543591 : Blo 1543469 1543591 := bstep (se 1 (by rfl) ⟨1157693, by rfl⟩ : syracuseStep 1543591 = 2315387) B2315387
theorem B5860795 : Blo 1543469 5860795 := bstep (se 1 (by rfl) ⟨4395596, by rfl⟩ : syracuseStep 5860795 = 8791193) B8791193
theorem B9391559 : Blo 1543469 9391559 := bstep (se 1 (by rfl) ⟨7043669, by rfl⟩ : syracuseStep 9391559 = 14087339) B14087339
theorem B2198983 : Blo 1543469 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B1543675 : Blo 1543469 1543675 := bstep (se 1 (by rfl) ⟨1157756, by rfl⟩ : syracuseStep 1543675 = 2315513) B2315513
theorem B7818767 : Blo 1543469 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B4230713 : Blo 1543469 4230713 := bstep (se 2 (by rfl) ⟨1586517, by rfl⟩ : syracuseStep 4230713 = 3173035) B3173035
theorem B1543743 : Blo 1543469 1543743 := bstep (se 1 (by rfl) ⟨1157807, by rfl⟩ : syracuseStep 1543743 = 2315615) B2315615
theorem B1543751 : Blo 1543469 1543751 := bstep (se 1 (by rfl) ⟨1157813, by rfl⟩ : syracuseStep 1543751 = 2315627) B2315627
theorem B9899729 : Blo 1543469 9899729 := bstep (se 2 (by rfl) ⟨3712398, by rfl⟩ : syracuseStep 9899729 = 7424797) B7424797
theorem B1543903 : Blo 1543469 1543903 := bstep (se 1 (by rfl) ⟨1157927, by rfl⟩ : syracuseStep 1543903 = 2315855) B2315855
theorem B5861099 : Blo 1543469 5861099 := bstep (se 1 (by rfl) ⟨4395824, by rfl⟩ : syracuseStep 5861099 = 8791649) B8791649
theorem B2821895 : Blo 1543469 2821895 := bstep (se 1 (by rfl) ⟨2116421, by rfl⟩ : syracuseStep 2821895 = 4232843) B4232843
theorem B1543983 : Blo 1543469 1543983 := bstep (se 1 (by rfl) ⟨1157987, by rfl⟩ : syracuseStep 1543983 = 2315975) B2315975
theorem B1544091 : Blo 1543469 1544091 := bstep (se 1 (by rfl) ⟨1158068, by rfl⟩ : syracuseStep 1544091 = 2316137) B2316137
theorem B8458141 : Blo 1543469 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B29691805 : Blo 1543469 29691805 := bstep (se 3 (by rfl) ⟨5567213, by rfl⟩ : syracuseStep 29691805 = 11134427) B11134427
theorem B16707485 : Blo 1543469 16707485 := bstep (se 3 (by rfl) ⟨3132653, by rfl⟩ : syracuseStep 16707485 = 6265307) B6265307
theorem B1544143 : Blo 1543469 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B1544167 : Blo 1543469 1544167 := bstep (se 1 (by rfl) ⟨1158125, by rfl⟩ : syracuseStep 1544167 = 2316251) B2316251
theorem B7041043 : Blo 1543469 7041043 := bstep (se 1 (by rfl) ⟨5280782, by rfl⟩ : syracuseStep 7041043 = 10561565) B10561565
theorem B33402941 : Blo 1543469 33402941 := bstep (se 3 (by rfl) ⟨6263051, by rfl⟩ : syracuseStep 33402941 = 12526103) B12526103
theorem B7049369 : Blo 1543469 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B9892043 : Blo 1543469 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B5861585 : Blo 1543469 5861585 := bstep (se 2 (by rfl) ⟨2198094, by rfl⟩ : syracuseStep 5861585 = 4396189) B4396189
theorem B14094607 : Blo 1543469 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B1544479 : Blo 1543469 1544479 := bstep (se 1 (by rfl) ⟨1158359, by rfl⟩ : syracuseStep 1544479 = 2316719) B2316719
theorem B1544539 : Blo 1543469 1544539 := bstep (se 1 (by rfl) ⟨1158404, by rfl⟩ : syracuseStep 1544539 = 2316809) B2316809
theorem B14848363 : Blo 1543469 14848363 := bstep (se 1 (by rfl) ⟨11136272, by rfl⟩ : syracuseStep 14848363 = 22272545) B22272545
theorem B3297647 : Blo 1543469 3297647 := bstep (se 1 (by rfl) ⟨2473235, by rfl⟩ : syracuseStep 3297647 = 4946471) B4946471
theorem B1544559 : Blo 1543469 1544559 := bstep (se 1 (by rfl) ⟨1158419, by rfl⟩ : syracuseStep 1544559 = 2316839) B2316839
theorem B1544615 : Blo 1543469 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B7819739 : Blo 1543469 7819739 := bstep (se 1 (by rfl) ⟨5864804, by rfl⟩ : syracuseStep 7819739 = 11729609) B11729609
theorem B6689243 : Blo 1543469 6689243 := bstep (se 1 (by rfl) ⟨5016932, by rfl⟩ : syracuseStep 6689243 = 10033865) B10033865
theorem B7426529 : Blo 1543469 7426529 := bstep (se 2 (by rfl) ⟨2784948, by rfl⟩ : syracuseStep 7426529 = 5569897) B5569897
theorem B1544699 : Blo 1543469 1544699 := bstep (se 1 (by rfl) ⟨1158524, by rfl⟩ : syracuseStep 1544699 = 2317049) B2317049
theorem B1544767 : Blo 1543469 1544767 := bstep (se 1 (by rfl) ⟨1158575, by rfl⟩ : syracuseStep 1544767 = 2317151) B2317151
theorem B1544775 : Blo 1543469 1544775 := bstep (se 1 (by rfl) ⟨1158581, by rfl⟩ : syracuseStep 1544775 = 2317163) B2317163
theorem B11137657 : Blo 1543469 11137657 := bstep (se 2 (by rfl) ⟨4176621, by rfl⟩ : syracuseStep 11137657 = 8353243) B8353243
theorem B5862041 : Blo 1543469 5862041 := bstep (se 2 (by rfl) ⟨2198265, by rfl⟩ : syracuseStep 5862041 = 4396531) B4396531
theorem B5862071 : Blo 1543469 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B1544927 : Blo 1543469 1544927 := bstep (se 1 (by rfl) ⟨1158695, by rfl⟩ : syracuseStep 1544927 = 2317391) B2317391
theorem B10572511 : Blo 1543469 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B1545007 : Blo 1543469 1545007 := bstep (se 1 (by rfl) ⟨1158755, by rfl⟩ : syracuseStep 1545007 = 2317511) B2317511
theorem B1545115 : Blo 1543469 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B7820225 : Blo 1543469 7820225 := bstep (se 2 (by rfl) ⟨2932584, by rfl⟩ : syracuseStep 7820225 = 5865169) B5865169
theorem B9393097 : Blo 1543469 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B1545167 : Blo 1543469 1545167 := bstep (se 1 (by rfl) ⟨1158875, by rfl⟩ : syracuseStep 1545167 = 2317751) B2317751
theorem B4396007 : Blo 1543469 4396007 := bstep (se 1 (by rfl) ⟨3297005, by rfl⟩ : syracuseStep 4396007 = 6594011) B6594011
theorem B1545191 : Blo 1543469 1545191 := bstep (se 1 (by rfl) ⟨1158893, by rfl⟩ : syracuseStep 1545191 = 2317787) B2317787
theorem B40121335 : Blo 1543469 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B26375219 : Blo 1543469 26375219 := bstep (se 1 (by rfl) ⟨19781414, by rfl⟩ : syracuseStep 26375219 = 39562829) B39562829
theorem B2315483 : Blo 1543469 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B5215481 : Blo 1543469 5215481 := bstep (se 2 (by rfl) ⟨1955805, by rfl⟩ : syracuseStep 5215481 = 3911611) B3911611
theorem B28177753 : Blo 1543469 28177753 := bstep (se 2 (by rfl) ⟨10566657, by rfl⟩ : syracuseStep 28177753 = 21133315) B21133315
theorem B13202783 : Blo 1543469 13202783 := bstep (se 1 (by rfl) ⟨9902087, by rfl⟩ : syracuseStep 13202783 = 19804175) B19804175
theorem B11441513 : Blo 1543469 11441513 := bstep (se 2 (by rfl) ⟨4290567, by rfl⟩ : syracuseStep 11441513 = 8581135) B8581135
theorem B5944699 : Blo 1543469 5944699 := bstep (se 1 (by rfl) ⟨4458524, by rfl⟩ : syracuseStep 5944699 = 8917049) B8917049
theorem B2315657 : Blo 1543469 2315657 := bstep (se 2 (by rfl) ⟨868371, by rfl⟩ : syracuseStep 2315657 = 1736743) B1736743
theorem B5215751 : Blo 1543469 5215751 := bstep (se 1 (by rfl) ⟨3911813, by rfl⟩ : syracuseStep 5215751 = 7823627) B7823627
theorem B2316011 : Blo 1543469 2316011 := bstep (se 1 (by rfl) ⟨1737008, by rfl⟩ : syracuseStep 2316011 = 3474017) B3474017
theorem B6600503 : Blo 1543469 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B2930489 : Blo 1543469 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B48215969 : Blo 1543469 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B2316239 : Blo 1543469 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B22263781 : Blo 1543469 22263781 := bstep (se 4 (by rfl) ⟨2087229, by rfl⟩ : syracuseStep 22263781 = 4174459) B4174459
theorem B2316635 : Blo 1543469 2316635 := bstep (se 1 (by rfl) ⟨1737476, by rfl⟩ : syracuseStep 2316635 = 3474953) B3474953
theorem B6601085 : Blo 1543469 6601085 := bstep (se 3 (by rfl) ⟨1237703, by rfl⟩ : syracuseStep 6601085 = 2475407) B2475407
theorem B2316863 : Blo 1543469 2316863 := bstep (se 1 (by rfl) ⟨1737647, by rfl⟩ : syracuseStep 2316863 = 3475295) B3475295
theorem B3963455 : Blo 1543469 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B4397647 : Blo 1543469 4397647 := bstep (se 1 (by rfl) ⟨3298235, by rfl⟩ : syracuseStep 4397647 = 6596471) B6596471
theorem B5864015 : Blo 1543469 5864015 := bstep (se 1 (by rfl) ⟨4398011, by rfl⟩ : syracuseStep 5864015 = 8796023) B8796023
theorem B2316983 : Blo 1543469 2316983 := bstep (se 1 (by rfl) ⟨1737737, by rfl⟩ : syracuseStep 2316983 = 3475475) B3475475
theorem B5864183 : Blo 1543469 5864183 := bstep (se 1 (by rfl) ⟨4398137, by rfl⟩ : syracuseStep 5864183 = 8796275) B8796275
theorem B7813907 : Blo 1543469 7813907 := bstep (se 1 (by rfl) ⟨5860430, by rfl⟩ : syracuseStep 7813907 = 11720861) B11720861
theorem B16071443 : Blo 1543469 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B3300115 : Blo 1543469 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B2317211 : Blo 1543469 2317211 := bstep (se 1 (by rfl) ⟨1737908, by rfl⟩ : syracuseStep 2317211 = 3475817) B3475817
theorem B5569435 : Blo 1543469 5569435 := bstep (se 1 (by rfl) ⟨4177076, by rfl⟩ : syracuseStep 5569435 = 8354153) B8354153
theorem B2317607 : Blo 1543469 2317607 := bstep (se 1 (by rfl) ⟨1738205, by rfl⟩ : syracuseStep 2317607 = 3476411) B3476411
theorem B3906913 : Blo 1543469 3906913 := bstep (se 2 (by rfl) ⟨1465092, by rfl⟩ : syracuseStep 3906913 = 2930185) B2930185
theorem B2317691 : Blo 1543469 2317691 := bstep (se 1 (by rfl) ⟨1738268, by rfl⟩ : syracuseStep 2317691 = 3476537) B3476537
theorem B2317817 : Blo 1543469 2317817 := bstep (se 2 (by rfl) ⟨869181, by rfl⟩ : syracuseStep 2317817 = 1738363) B1738363
theorem B3472991 : Blo 1543469 3472991 := bstep (se 1 (by rfl) ⟨2604743, by rfl⟩ : syracuseStep 3472991 = 5209487) B5209487
theorem B13188703 : Blo 1543469 13188703 := bstep (se 1 (by rfl) ⟨9891527, by rfl⟩ : syracuseStep 13188703 = 19783055) B19783055
theorem B2317919 : Blo 1543469 2317919 := bstep (se 1 (by rfl) ⟨1738439, by rfl⟩ : syracuseStep 2317919 = 3476879) B3476879
theorem B7520003 : Blo 1543469 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B3473207 : Blo 1543469 3473207 := bstep (se 1 (by rfl) ⟨2604905, by rfl⟩ : syracuseStep 3473207 = 5209811) B5209811
theorem B2318135 : Blo 1543469 2318135 := bstep (se 1 (by rfl) ⟨1738601, by rfl⟩ : syracuseStep 2318135 = 3477203) B3477203
theorem B1736527 : Blo 1543469 1736527 := bstep (se 1 (by rfl) ⟨1302395, by rfl⟩ : syracuseStep 1736527 = 2604791) B2604791
theorem B7815041 : Blo 1543469 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B2605007 : Blo 1543469 2605007 := bstep (se 1 (by rfl) ⟨1953755, by rfl⟩ : syracuseStep 2605007 = 3907511) B3907511
theorem B9388057 : Blo 1543469 9388057 := bstep (se 2 (by rfl) ⟨3520521, by rfl⟩ : syracuseStep 9388057 = 7041043) B7041043
theorem B6594695 : Blo 1543469 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B3907723 : Blo 1543469 3907723 := bstep (se 1 (by rfl) ⟨2930792, by rfl⟩ : syracuseStep 3907723 = 5861585) B5861585
theorem B2605243 : Blo 1543469 2605243 := bstep (se 1 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 2605243 = 3907865) B3907865
theorem B3473639 : Blo 1543469 3473639 := bstep (se 1 (by rfl) ⟨2605229, by rfl⟩ : syracuseStep 3473639 = 5210459) B5210459
theorem B16933121 : Blo 1543469 16933121 := bstep (se 2 (by rfl) ⟨6349920, by rfl⟩ : syracuseStep 16933121 = 12699841) B12699841
theorem B18792809 : Blo 1543469 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B2605439 : Blo 1543469 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B3908027 : Blo 1543469 3908027 := bstep (se 1 (by rfl) ⟨2931020, by rfl⟩ : syracuseStep 3908027 = 5862041) B5862041
theorem B5210567 : Blo 1543469 5210567 := bstep (se 1 (by rfl) ⟨3907925, by rfl⟩ : syracuseStep 5210567 = 7815851) B7815851
theorem B3908047 : Blo 1543469 3908047 := bstep (se 1 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 3908047 = 5862071) B5862071
theorem B23790125 : Blo 1543469 23790125 := bstep (se 3 (by rfl) ⟨4460648, by rfl⟩ : syracuseStep 23790125 = 8921297) B8921297
theorem B11731553 : Blo 1543469 11731553 := bstep (se 2 (by rfl) ⟨4399332, by rfl⟩ : syracuseStep 11731553 = 8798665) B8798665
theorem B1737319 : Blo 1543469 1737319 := bstep (se 1 (by rfl) ⟨1302989, by rfl⟩ : syracuseStep 1737319 = 2605979) B2605979
theorem B5210891 : Blo 1543469 5210891 := bstep (se 1 (by rfl) ⟨3908168, by rfl⟩ : syracuseStep 5210891 = 7816337) B7816337
theorem B2605871 : Blo 1543469 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B3474233 : Blo 1543469 3474233 := bstep (se 2 (by rfl) ⟨1302837, by rfl⟩ : syracuseStep 3474233 = 2605675) B2605675
theorem B3474287 : Blo 1543469 3474287 := bstep (se 1 (by rfl) ⟨2605715, by rfl⟩ : syracuseStep 3474287 = 5211431) B5211431
theorem B7422839 : Blo 1543469 7422839 := bstep (se 1 (by rfl) ⟨5567129, by rfl⟩ : syracuseStep 7422839 = 11134259) B11134259
theorem B2933671 : Blo 1543469 2933671 := bstep (se 1 (by rfl) ⟨2200253, by rfl⟩ : syracuseStep 2933671 = 4400507) B4400507
theorem B5211161 : Blo 1543469 5211161 := bstep (se 2 (by rfl) ⟨1954185, by rfl⟩ : syracuseStep 5211161 = 3908371) B3908371
theorem B4400153 : Blo 1543469 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B9897065 : Blo 1543469 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B25044157 : Blo 1543469 25044157 := bstep (se 3 (by rfl) ⟨4695779, by rfl⟩ : syracuseStep 25044157 = 9391559) B9391559
theorem B4400335 : Blo 1543469 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B2475215 : Blo 1543469 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B53495113 : Blo 1543469 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B3474863 : Blo 1543469 3474863 := bstep (se 1 (by rfl) ⟨2606147, by rfl⟩ : syracuseStep 3474863 = 5212295) B5212295
theorem B17163713 : Blo 1543469 17163713 := bstep (se 2 (by rfl) ⟨6436392, by rfl⟩ : syracuseStep 17163713 = 12872785) B12872785
theorem B42264017 : Blo 1543469 42264017 := bstep (se 2 (by rfl) ⟨15849006, by rfl⟩ : syracuseStep 42264017 = 31698013) B31698013
theorem B4400723 : Blo 1543469 4400723 := bstep (se 1 (by rfl) ⟨3300542, by rfl⟩ : syracuseStep 4400723 = 6601085) B6601085
theorem B5211809 : Blo 1543469 5211809 := bstep (se 2 (by rfl) ⟨1954428, by rfl⟩ : syracuseStep 5211809 = 3908857) B3908857
theorem B3909343 : Blo 1543469 3909343 := bstep (se 1 (by rfl) ⟨2932007, by rfl⟩ : syracuseStep 3909343 = 5864015) B5864015
theorem B2606843 : Blo 1543469 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B37570337 : Blo 1543469 37570337 := bstep (se 2 (by rfl) ⟨14088876, by rfl⟩ : syracuseStep 37570337 = 28177753) B28177753
theorem B3909455 : Blo 1543469 3909455 := bstep (se 1 (by rfl) ⟨2932091, by rfl⟩ : syracuseStep 3909455 = 5864183) B5864183
theorem B2607079 : Blo 1543469 2607079 := bstep (se 1 (by rfl) ⟨1955309, by rfl⟩ : syracuseStep 2607079 = 3910619) B3910619
theorem B2607295 : Blo 1543469 2607295 := bstep (se 1 (by rfl) ⟨1955471, by rfl⟩ : syracuseStep 2607295 = 3910943) B3910943
theorem B3475691 : Blo 1543469 3475691 := bstep (se 1 (by rfl) ⟨2606768, by rfl⟩ : syracuseStep 3475691 = 5213537) B5213537
theorem B5212511 : Blo 1543469 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B2820475 : Blo 1543469 2820475 := bstep (se 1 (by rfl) ⟨2115356, by rfl⟩ : syracuseStep 2820475 = 4230713) B4230713
theorem B22251905 : Blo 1543469 22251905 := bstep (se 2 (by rfl) ⟨8344464, by rfl⟩ : syracuseStep 22251905 = 16688929) B16688929
theorem B5212673 : Blo 1543469 5212673 := bstep (se 2 (by rfl) ⟨1954752, by rfl⟩ : syracuseStep 5212673 = 3909505) B3909505
theorem B22268627 : Blo 1543469 22268627 := bstep (se 1 (by rfl) ⟨16701470, by rfl⟩ : syracuseStep 22268627 = 33402941) B33402941
theorem B2198431 : Blo 1543469 2198431 := bstep (se 1 (by rfl) ⟨1648823, by rfl⟩ : syracuseStep 2198431 = 3297647) B3297647
theorem B5213159 : Blo 1543469 5213159 := bstep (se 1 (by rfl) ⟨3909869, by rfl⟩ : syracuseStep 5213159 = 7819739) B7819739
theorem B4459495 : Blo 1543469 4459495 := bstep (se 1 (by rfl) ⟨3344621, by rfl⟩ : syracuseStep 4459495 = 6689243) B6689243
theorem B4951019 : Blo 1543469 4951019 := bstep (se 1 (by rfl) ⟨3713264, by rfl⟩ : syracuseStep 4951019 = 7426529) B7426529
theorem B5213483 : Blo 1543469 5213483 := bstep (se 1 (by rfl) ⟨3910112, by rfl⟩ : syracuseStep 5213483 = 7820225) B7820225
theorem B17583479 : Blo 1543469 17583479 := bstep (se 1 (by rfl) ⟨13187609, by rfl⟩ : syracuseStep 17583479 = 26375219) B26375219
theorem B1543655 : Blo 1543469 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B3476987 : Blo 1543469 3476987 := bstep (se 1 (by rfl) ⟨2607740, by rfl⟩ : syracuseStep 3476987 = 5215481) B5215481
theorem B5213753 : Blo 1543469 5213753 := bstep (se 2 (by rfl) ⟨1955157, by rfl⟩ : syracuseStep 5213753 = 3910315) B3910315
theorem B8801855 : Blo 1543469 8801855 := bstep (se 1 (by rfl) ⟨6601391, by rfl⟩ : syracuseStep 8801855 = 13202783) B13202783
theorem B1543771 : Blo 1543469 1543771 := bstep (se 1 (by rfl) ⟨1157828, by rfl⟩ : syracuseStep 1543771 = 2315657) B2315657
theorem B30510701 : Blo 1543469 30510701 := bstep (se 3 (by rfl) ⟨5720756, by rfl⟩ : syracuseStep 30510701 = 11441513) B11441513
theorem B3477167 : Blo 1543469 3477167 := bstep (se 1 (by rfl) ⟨2607875, by rfl⟩ : syracuseStep 3477167 = 5215751) B5215751
theorem B1544007 : Blo 1543469 1544007 := bstep (se 1 (by rfl) ⟨1158005, by rfl⟩ : syracuseStep 1544007 = 2316011) B2316011
theorem B7425913 : Blo 1543469 7425913 := bstep (se 2 (by rfl) ⟨2784717, by rfl⟩ : syracuseStep 7425913 = 5569435) B5569435
theorem B1953659 : Blo 1543469 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B1544159 : Blo 1543469 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B1544423 : Blo 1543469 1544423 := bstep (se 1 (by rfl) ⟨1158317, by rfl⟩ : syracuseStep 1544423 = 2316635) B2316635
theorem B1544575 : Blo 1543469 1544575 := bstep (se 1 (by rfl) ⟨1158431, by rfl⟩ : syracuseStep 1544575 = 2316863) B2316863
theorem B2642303 : Blo 1543469 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B1544655 : Blo 1543469 1544655 := bstep (se 1 (by rfl) ⟨1158491, by rfl⟩ : syracuseStep 1544655 = 2316983) B2316983
theorem B7926265 : Blo 1543469 7926265 := bstep (se 2 (by rfl) ⟨2972349, by rfl⟩ : syracuseStep 7926265 = 5944699) B5944699
theorem B1544807 : Blo 1543469 1544807 := bstep (se 1 (by rfl) ⟨1158605, by rfl⟩ : syracuseStep 1544807 = 2317211) B2317211
theorem B17584937 : Blo 1543469 17584937 := bstep (se 2 (by rfl) ⟨6594351, by rfl⟩ : syracuseStep 17584937 = 13188703) B13188703
theorem B1545071 : Blo 1543469 1545071 := bstep (se 1 (by rfl) ⟨1158803, by rfl⟩ : syracuseStep 1545071 = 2317607) B2317607
theorem B1545127 : Blo 1543469 1545127 := bstep (se 1 (by rfl) ⟨1158845, by rfl⟩ : syracuseStep 1545127 = 2317691) B2317691
theorem B1545211 : Blo 1543469 1545211 := bstep (se 1 (by rfl) ⟨1158908, by rfl⟩ : syracuseStep 1545211 = 2317817) B2317817
theorem B2315327 : Blo 1543469 2315327 := bstep (se 1 (by rfl) ⟨1736495, by rfl⟩ : syracuseStep 2315327 = 3472991) B3472991
theorem B1545279 : Blo 1543469 1545279 := bstep (se 1 (by rfl) ⟨1158959, by rfl⟩ : syracuseStep 1545279 = 2317919) B2317919
theorem B2315369 : Blo 1543469 2315369 := bstep (se 2 (by rfl) ⟨868263, by rfl⟩ : syracuseStep 2315369 = 1736527) B1736527
theorem B6599819 : Blo 1543469 6599819 := bstep (se 1 (by rfl) ⟨4949864, by rfl⟩ : syracuseStep 6599819 = 9899729) B9899729
theorem B1881263 : Blo 1543469 1881263 := bstep (se 1 (by rfl) ⟨1410947, by rfl⟩ : syracuseStep 1881263 = 2821895) B2821895
theorem B2315471 : Blo 1543469 2315471 := bstep (se 1 (by rfl) ⟨1736603, by rfl⟩ : syracuseStep 2315471 = 3473207) B3473207
theorem B1545423 : Blo 1543469 1545423 := bstep (se 1 (by rfl) ⟨1159067, by rfl⟩ : syracuseStep 1545423 = 2318135) B2318135
theorem B11277521 : Blo 1543469 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B39589073 : Blo 1543469 39589073 := bstep (se 2 (by rfl) ⟨14845902, by rfl⟩ : syracuseStep 39589073 = 29691805) B29691805
theorem B11138323 : Blo 1543469 11138323 := bstep (se 1 (by rfl) ⟨8353742, by rfl⟩ : syracuseStep 11138323 = 16707485) B16707485
theorem B29685041 : Blo 1543469 29685041 := bstep (se 2 (by rfl) ⟨11131890, by rfl⟩ : syracuseStep 29685041 = 22263781) B22263781
theorem B37574027 : Blo 1543469 37574027 := bstep (se 1 (by rfl) ⟨28180520, by rfl⟩ : syracuseStep 37574027 = 56361041) B56361041
theorem B2315675 : Blo 1543469 2315675 := bstep (se 1 (by rfl) ⟨1736756, by rfl⟩ : syracuseStep 2315675 = 3473513) B3473513
theorem B5215643 : Blo 1543469 5215643 := bstep (se 1 (by rfl) ⟨3911732, by rfl⟩ : syracuseStep 5215643 = 7823465) B7823465
theorem B4699579 : Blo 1543469 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B29677043 : Blo 1543469 29677043 := bstep (se 1 (by rfl) ⟨22257782, by rfl⟩ : syracuseStep 29677043 = 44515565) B44515565
theorem B50083393 : Blo 1543469 50083393 := bstep (se 2 (by rfl) ⟨18781272, by rfl⟩ : syracuseStep 50083393 = 37562545) B37562545
theorem B2315897 : Blo 1543469 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B2315999 : Blo 1543469 2315999 := bstep (se 1 (by rfl) ⟨1736999, by rfl⟩ : syracuseStep 2315999 = 3473999) B3473999
theorem B19797817 : Blo 1543469 19797817 := bstep (se 2 (by rfl) ⟨7424181, by rfl⟩ : syracuseStep 19797817 = 14848363) B14848363
theorem B2316095 : Blo 1543469 2316095 := bstep (se 1 (by rfl) ⟨1737071, by rfl⟩ : syracuseStep 2316095 = 3474143) B3474143
theorem B2316263 : Blo 1543469 2316263 := bstep (se 1 (by rfl) ⟨1737197, by rfl⟩ : syracuseStep 2316263 = 3474395) B3474395
theorem B2930671 : Blo 1543469 2930671 := bstep (se 1 (by rfl) ⟨2198003, by rfl⟩ : syracuseStep 2930671 = 4396007) B4396007
theorem B2316281 : Blo 1543469 2316281 := bstep (se 2 (by rfl) ⟨868605, by rfl⟩ : syracuseStep 2316281 = 1737211) B1737211
theorem B2316383 : Blo 1543469 2316383 := bstep (se 1 (by rfl) ⟨1737287, by rfl⟩ : syracuseStep 2316383 = 3474575) B3474575
theorem B5863529 : Blo 1543469 5863529 := bstep (se 2 (by rfl) ⟨2198823, by rfl⟩ : syracuseStep 5863529 = 4397647) B4397647
theorem B2316443 : Blo 1543469 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B14850209 : Blo 1543469 14850209 := bstep (se 2 (by rfl) ⟨5568828, by rfl⟩ : syracuseStep 14850209 = 11137657) B11137657
theorem B2316479 : Blo 1543469 2316479 := bstep (se 1 (by rfl) ⟨1737359, by rfl⟩ : syracuseStep 2316479 = 3474719) B3474719
theorem B2316521 : Blo 1543469 2316521 := bstep (se 2 (by rfl) ⟨868695, by rfl⟩ : syracuseStep 2316521 = 1737391) B1737391
theorem B14096681 : Blo 1543469 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B4397419 : Blo 1543469 4397419 := bstep (se 1 (by rfl) ⟨3298064, by rfl⟩ : syracuseStep 4397419 = 6596129) B6596129
theorem B2316827 : Blo 1543469 2316827 := bstep (se 1 (by rfl) ⟨1737620, by rfl⟩ : syracuseStep 2316827 = 3475241) B3475241
theorem B12524129 : Blo 1543469 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B2316905 : Blo 1543469 2316905 := bstep (se 2 (by rfl) ⟨868839, by rfl⟩ : syracuseStep 2316905 = 1737679) B1737679
theorem B32143979 : Blo 1543469 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B2317433 : Blo 1543469 2317433 := bstep (se 2 (by rfl) ⟨869037, by rfl⟩ : syracuseStep 2317433 = 1738075) B1738075
theorem B5209217 : Blo 1543469 5209217 := bstep (se 2 (by rfl) ⟨1953456, by rfl⟩ : syracuseStep 5209217 = 3906913) B3906913
theorem B5209271 : Blo 1543469 5209271 := bstep (se 1 (by rfl) ⟨3906953, by rfl⟩ : syracuseStep 5209271 = 7813907) B7813907
theorem B4398263 : Blo 1543469 4398263 := bstep (se 1 (by rfl) ⟨3298697, by rfl⟩ : syracuseStep 4398263 = 6597395) B6597395
theorem B10714295 : Blo 1543469 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B2317535 : Blo 1543469 2317535 := bstep (se 1 (by rfl) ⟨1738151, by rfl⟩ : syracuseStep 2317535 = 3476303) B3476303
theorem B7814393 : Blo 1543469 7814393 := bstep (se 2 (by rfl) ⟨2930397, by rfl⟩ : syracuseStep 7814393 = 5860795) B5860795
theorem B9395453 : Blo 1543469 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B2931977 : Blo 1543469 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B2317577 : Blo 1543469 2317577 := bstep (se 2 (by rfl) ⟨869091, by rfl⟩ : syracuseStep 2317577 = 1738183) B1738183
theorem B2317679 : Blo 1543469 2317679 := bstep (se 1 (by rfl) ⟨1738259, by rfl⟩ : syracuseStep 2317679 = 3476519) B3476519
theorem B2317799 : Blo 1543469 2317799 := bstep (se 1 (by rfl) ⟨1738349, by rfl⟩ : syracuseStep 2317799 = 3476699) B3476699
theorem B2317931 : Blo 1543469 2317931 := bstep (se 1 (by rfl) ⟨1738448, by rfl⟩ : syracuseStep 2317931 = 3476897) B3476897
theorem B2318057 : Blo 1543469 2318057 := bstep (se 2 (by rfl) ⟨869271, by rfl⟩ : syracuseStep 2318057 = 1738543) B1738543
theorem B3907399 : Blo 1543469 3907399 := bstep (se 1 (by rfl) ⟨2930549, by rfl⟩ : syracuseStep 3907399 = 5861099) B5861099
theorem B5013335 : Blo 1543469 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B2318201 : Blo 1543469 2318201 := bstep (se 2 (by rfl) ⟨869325, by rfl⟩ : syracuseStep 2318201 = 1738651) B1738651
theorem B5210027 : Blo 1543469 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B1736671 : Blo 1543469 1736671 := bstep (se 1 (by rfl) ⟨1302503, by rfl⟩ : syracuseStep 1736671 = 2605007) B2605007
theorem B12517409 : Blo 1543469 12517409 := bstep (se 2 (by rfl) ⟨4694028, by rfl⟩ : syracuseStep 12517409 = 9388057) B9388057
theorem B11288747 : Blo 1543469 11288747 := bstep (se 1 (by rfl) ⟨8466560, by rfl⟩ : syracuseStep 11288747 = 16933121) B16933121
theorem B5210297 : Blo 1543469 5210297 := bstep (se 2 (by rfl) ⟨1953861, by rfl⟩ : syracuseStep 5210297 = 3907723) B3907723
theorem B3473657 : Blo 1543469 3473657 := bstep (se 2 (by rfl) ⟨1302621, by rfl⟩ : syracuseStep 3473657 = 2605243) B2605243
theorem B1736959 : Blo 1543469 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B1761535 : Blo 1543469 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B2605351 : Blo 1543469 2605351 := bstep (se 1 (by rfl) ⟨1954013, by rfl⟩ : syracuseStep 2605351 = 3908027) B3908027
theorem B3473711 : Blo 1543469 3473711 := bstep (se 1 (by rfl) ⟨2605283, by rfl⟩ : syracuseStep 3473711 = 5210567) B5210567
theorem B15860083 : Blo 1543469 15860083 := bstep (se 1 (by rfl) ⟨11895062, by rfl⟩ : syracuseStep 15860083 = 23790125) B23790125
theorem B3760633 : Blo 1543469 3760633 := bstep (se 2 (by rfl) ⟨1410237, by rfl⟩ : syracuseStep 3760633 = 2820475) B2820475
theorem B3473927 : Blo 1543469 3473927 := bstep (se 1 (by rfl) ⟨2605445, by rfl⟩ : syracuseStep 3473927 = 5210891) B5210891
theorem B11723291 : Blo 1543469 11723291 := bstep (se 1 (by rfl) ⟨8792468, by rfl⟩ : syracuseStep 11723291 = 17584937) B17584937
theorem B1737247 : Blo 1543469 1737247 := bstep (se 1 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 1737247 = 2605871) B2605871
theorem B4948559 : Blo 1543469 4948559 := bstep (se 1 (by rfl) ⟨3711419, by rfl⟩ : syracuseStep 4948559 = 7422839) B7422839
theorem B5210729 : Blo 1543469 5210729 := bstep (se 2 (by rfl) ⟨1954023, by rfl⟩ : syracuseStep 5210729 = 3908047) B3908047
theorem B3474107 : Blo 1543469 3474107 := bstep (se 1 (by rfl) ⟨2605580, by rfl⟩ : syracuseStep 3474107 = 5211161) B5211161
theorem B2933435 : Blo 1543469 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B19784695 : Blo 1543469 19784695 := bstep (se 1 (by rfl) ⟨14838521, by rfl⟩ : syracuseStep 19784695 = 29677043) B29677043
theorem B2933815 : Blo 1543469 2933815 := bstep (se 1 (by rfl) ⟨2200361, by rfl⟩ : syracuseStep 2933815 = 4400723) B4400723
theorem B3474539 : Blo 1543469 3474539 := bstep (se 1 (by rfl) ⟨2605904, by rfl⟩ : syracuseStep 3474539 = 5211809) B5211809
theorem B1737895 : Blo 1543469 1737895 := bstep (se 1 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 1737895 = 2606843) B2606843
theorem B2606303 : Blo 1543469 2606303 := bstep (se 1 (by rfl) ⟨1954727, by rfl⟩ : syracuseStep 2606303 = 3909455) B3909455
theorem B3909019 : Blo 1543469 3909019 := bstep (se 1 (by rfl) ⟨2931764, by rfl⟩ : syracuseStep 3909019 = 5863529) B5863529
theorem B9397787 : Blo 1543469 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B3475007 : Blo 1543469 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B5867113 : Blo 1543469 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B3475115 : Blo 1543469 3475115 := bstep (se 1 (by rfl) ⟨2606336, by rfl⟩ : syracuseStep 3475115 = 5212673) B5212673
theorem B8349419 : Blo 1543469 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B14845751 : Blo 1543469 14845751 := bstep (se 1 (by rfl) ⟨11134313, by rfl⟩ : syracuseStep 14845751 = 22268627) B22268627
theorem B3475439 : Blo 1543469 3475439 := bstep (se 1 (by rfl) ⟨2606579, by rfl⟩ : syracuseStep 3475439 = 5213159) B5213159
theorem B3475655 : Blo 1543469 3475655 := bstep (se 1 (by rfl) ⟨2606741, by rfl⟩ : syracuseStep 3475655 = 5213483) B5213483
theorem B5212457 : Blo 1543469 5212457 := bstep (se 2 (by rfl) ⟨1954671, by rfl⟩ : syracuseStep 5212457 = 3909343) B3909343
theorem B3475835 : Blo 1543469 3475835 := bstep (se 1 (by rfl) ⟨2606876, by rfl⟩ : syracuseStep 3475835 = 5213753) B5213753
theorem B5867903 : Blo 1543469 5867903 := bstep (se 1 (by rfl) ⟨4400927, by rfl⟩ : syracuseStep 5867903 = 8801855) B8801855
theorem B26397089 : Blo 1543469 26397089 := bstep (se 2 (by rfl) ⟨9898908, by rfl⟩ : syracuseStep 26397089 = 19797817) B19797817
theorem B42273413 : Blo 1543469 42273413 := bstep (se 4 (by rfl) ⟨3963132, by rfl⟩ : syracuseStep 42273413 = 7926265) B7926265
theorem B3476105 : Blo 1543469 3476105 := bstep (se 2 (by rfl) ⟨1303539, by rfl⟩ : syracuseStep 3476105 = 2607079) B2607079
theorem B12528539 : Blo 1543469 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B3476393 : Blo 1543469 3476393 := bstep (se 2 (by rfl) ⟨1303647, by rfl⟩ : syracuseStep 3476393 = 2607295) B2607295
theorem B17599517 : Blo 1543469 17599517 := bstep (se 3 (by rfl) ⟨3299909, by rfl⟩ : syracuseStep 17599517 = 6599819) B6599819
theorem B5016701 : Blo 1543469 5016701 := bstep (se 3 (by rfl) ⟨940631, by rfl⟩ : syracuseStep 5016701 = 1881263) B1881263
theorem B7818605 : Blo 1543469 7818605 := bstep (se 3 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 7818605 = 2931977) B2931977
theorem B1543551 : Blo 1543469 1543551 := bstep (se 1 (by rfl) ⟨1157663, by rfl⟩ : syracuseStep 1543551 = 2315327) B2315327
theorem B1543579 : Blo 1543469 1543579 := bstep (se 1 (by rfl) ⟨1157684, by rfl⟩ : syracuseStep 1543579 = 2315369) B2315369
theorem B6598043 : Blo 1543469 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B1543647 : Blo 1543469 1543647 := bstep (se 1 (by rfl) ⟨1157735, by rfl⟩ : syracuseStep 1543647 = 2315471) B2315471
theorem B1650143 : Blo 1543469 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B1543783 : Blo 1543469 1543783 := bstep (se 1 (by rfl) ⟨1157837, by rfl⟩ : syracuseStep 1543783 = 2315675) B2315675
theorem B3477095 : Blo 1543469 3477095 := bstep (se 1 (by rfl) ⟨2607821, by rfl⟩ : syracuseStep 3477095 = 5215643) B5215643
theorem B28176011 : Blo 1543469 28176011 := bstep (se 1 (by rfl) ⟨21132008, by rfl⟩ : syracuseStep 28176011 = 42264017) B42264017
theorem B1543931 : Blo 1543469 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B1543999 : Blo 1543469 1543999 := bstep (se 1 (by rfl) ⟨1157999, by rfl⟩ : syracuseStep 1543999 = 2315999) B2315999
theorem B25046891 : Blo 1543469 25046891 := bstep (se 1 (by rfl) ⟨18785168, by rfl⟩ : syracuseStep 25046891 = 37570337) B37570337
theorem B1544063 : Blo 1543469 1544063 := bstep (se 1 (by rfl) ⟨1158047, by rfl⟩ : syracuseStep 1544063 = 2316095) B2316095
theorem B3911561 : Blo 1543469 3911561 := bstep (se 2 (by rfl) ⟨1466835, by rfl⟩ : syracuseStep 3911561 = 2933671) B2933671
theorem B1544175 : Blo 1543469 1544175 := bstep (se 1 (by rfl) ⟨1158131, by rfl⟩ : syracuseStep 1544175 = 2316263) B2316263
theorem B1544187 : Blo 1543469 1544187 := bstep (se 1 (by rfl) ⟨1158140, by rfl⟩ : syracuseStep 1544187 = 2316281) B2316281
theorem B1544255 : Blo 1543469 1544255 := bstep (se 1 (by rfl) ⟨1158191, by rfl⟩ : syracuseStep 1544255 = 2316383) B2316383
theorem B1544295 : Blo 1543469 1544295 := bstep (se 1 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 1544295 = 2316443) B2316443
theorem B9900139 : Blo 1543469 9900139 := bstep (se 1 (by rfl) ⟨7425104, by rfl⟩ : syracuseStep 9900139 = 14850209) B14850209
theorem B1544319 : Blo 1543469 1544319 := bstep (se 1 (by rfl) ⟨1158239, by rfl⟩ : syracuseStep 1544319 = 2316479) B2316479
theorem B1544347 : Blo 1543469 1544347 := bstep (se 1 (by rfl) ⟨1158260, by rfl⟩ : syracuseStep 1544347 = 2316521) B2316521
theorem B1544551 : Blo 1543469 1544551 := bstep (se 1 (by rfl) ⟨1158413, by rfl⟩ : syracuseStep 1544551 = 2316827) B2316827
theorem B1544603 : Blo 1543469 1544603 := bstep (se 1 (by rfl) ⟨1158452, by rfl⟩ : syracuseStep 1544603 = 2316905) B2316905
theorem B1544955 : Blo 1543469 1544955 := bstep (se 1 (by rfl) ⟨1158716, by rfl⟩ : syracuseStep 1544955 = 2317433) B2317433
theorem B66777857 : Blo 1543469 66777857 := bstep (se 2 (by rfl) ⟨25041696, by rfl⟩ : syracuseStep 66777857 = 50083393) B50083393
theorem B1545023 : Blo 1543469 1545023 := bstep (se 1 (by rfl) ⟨1158767, by rfl⟩ : syracuseStep 1545023 = 2317535) B2317535
theorem B6263635 : Blo 1543469 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B1545051 : Blo 1543469 1545051 := bstep (se 1 (by rfl) ⟨1158788, by rfl⟩ : syracuseStep 1545051 = 2317577) B2317577
theorem B1545119 : Blo 1543469 1545119 := bstep (se 1 (by rfl) ⟨1158839, by rfl⟩ : syracuseStep 1545119 = 2317679) B2317679
theorem B1545199 : Blo 1543469 1545199 := bstep (se 1 (by rfl) ⟨1158899, by rfl⟩ : syracuseStep 1545199 = 2317799) B2317799
theorem B1545287 : Blo 1543469 1545287 := bstep (se 1 (by rfl) ⟨1158965, by rfl⟩ : syracuseStep 1545287 = 2317931) B2317931
theorem B1545371 : Blo 1543469 1545371 := bstep (se 1 (by rfl) ⟨1159028, by rfl⟩ : syracuseStep 1545371 = 2318057) B2318057
theorem B9901217 : Blo 1543469 9901217 := bstep (se 2 (by rfl) ⟨3712956, by rfl⟩ : syracuseStep 9901217 = 7425913) B7425913
theorem B1545467 : Blo 1543469 1545467 := bstep (se 1 (by rfl) ⟨1159100, by rfl⟩ : syracuseStep 1545467 = 2318201) B2318201
theorem B2315561 : Blo 1543469 2315561 := bstep (se 2 (by rfl) ⟨868335, by rfl⟩ : syracuseStep 2315561 = 1736671) B1736671
theorem B4396463 : Blo 1543469 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B2315759 : Blo 1543469 2315759 := bstep (se 1 (by rfl) ⟨1736819, by rfl⟩ : syracuseStep 2315759 = 3473639) B3473639
theorem B7821035 : Blo 1543469 7821035 := bstep (se 1 (by rfl) ⟨5865776, by rfl⟩ : syracuseStep 7821035 = 11731553) B11731553
theorem B5863225 : Blo 1543469 5863225 := bstep (se 2 (by rfl) ⟨2198709, by rfl⟩ : syracuseStep 5863225 = 4397419) B4397419
theorem B2316155 : Blo 1543469 2316155 := bstep (se 1 (by rfl) ⟨1737116, by rfl⟩ : syracuseStep 2316155 = 3474233) B3474233
theorem B2316191 : Blo 1543469 2316191 := bstep (se 1 (by rfl) ⟨1737143, by rfl⟩ : syracuseStep 2316191 = 3474287) B3474287
theorem B2316425 : Blo 1543469 2316425 := bstep (se 2 (by rfl) ⟨868659, by rfl⟩ : syracuseStep 2316425 = 1737319) B1737319
theorem B7518347 : Blo 1543469 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B26392715 : Blo 1543469 26392715 := bstep (se 1 (by rfl) ⟨19794536, by rfl⟩ : syracuseStep 26392715 = 39589073) B39589073
theorem B19790027 : Blo 1543469 19790027 := bstep (se 1 (by rfl) ⟨14842520, by rfl⟩ : syracuseStep 19790027 = 29685041) B29685041
theorem B25049351 : Blo 1543469 25049351 := bstep (se 1 (by rfl) ⟨18787013, by rfl⟩ : syracuseStep 25049351 = 37574027) B37574027
theorem B2316575 : Blo 1543469 2316575 := bstep (se 1 (by rfl) ⟨1737431, by rfl⟩ : syracuseStep 2316575 = 3474863) B3474863
theorem B11442475 : Blo 1543469 11442475 := bstep (se 1 (by rfl) ⟨8581856, by rfl⟩ : syracuseStep 11442475 = 17163713) B17163713
theorem B133568837 : Blo 1543469 133568837 := bstep (se 4 (by rfl) ⟨12522078, by rfl⟩ : syracuseStep 133568837 = 25044157) B25044157
theorem B2931241 : Blo 1543469 2931241 := bstep (se 2 (by rfl) ⟨1099215, by rfl⟩ : syracuseStep 2931241 = 2198431) B2198431
theorem B5945993 : Blo 1543469 5945993 := bstep (se 2 (by rfl) ⟨2229747, by rfl⟩ : syracuseStep 5945993 = 4459495) B4459495
theorem B2317127 : Blo 1543469 2317127 := bstep (se 1 (by rfl) ⟨1737845, by rfl⟩ : syracuseStep 2317127 = 3475691) B3475691
theorem B14834603 : Blo 1543469 14834603 := bstep (se 1 (by rfl) ⟨11125952, by rfl⟩ : syracuseStep 14834603 = 22251905) B22251905
theorem B14851097 : Blo 1543469 14851097 := bstep (se 2 (by rfl) ⟨5569161, by rfl⟩ : syracuseStep 14851097 = 11138323) B11138323
theorem B21429319 : Blo 1543469 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B71326817 : Blo 1543469 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B6266105 : Blo 1543469 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B3300679 : Blo 1543469 3300679 := bstep (se 1 (by rfl) ⟨2475509, by rfl⟩ : syracuseStep 3300679 = 4951019) B4951019
theorem B3472811 : Blo 1543469 3472811 := bstep (se 1 (by rfl) ⟨2604608, by rfl⟩ : syracuseStep 3472811 = 5209217) B5209217
theorem B3472847 : Blo 1543469 3472847 := bstep (se 1 (by rfl) ⟨2604635, by rfl⟩ : syracuseStep 3472847 = 5209271) B5209271
theorem B2932175 : Blo 1543469 2932175 := bstep (se 1 (by rfl) ⟨2199131, by rfl⟩ : syracuseStep 2932175 = 4398263) B4398263
theorem B7142863 : Blo 1543469 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B5209595 : Blo 1543469 5209595 := bstep (se 1 (by rfl) ⟨3907196, by rfl⟩ : syracuseStep 5209595 = 7814393) B7814393
theorem B11722319 : Blo 1543469 11722319 := bstep (se 1 (by rfl) ⟨8791739, by rfl⟩ : syracuseStep 11722319 = 17583479) B17583479
theorem B5209757 : Blo 1543469 5209757 := bstep (se 3 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 5209757 = 1953659) B1953659
theorem B2317991 : Blo 1543469 2317991 := bstep (se 1 (by rfl) ⟨1738493, by rfl⟩ : syracuseStep 2317991 = 3476987) B3476987
theorem B20340467 : Blo 1543469 20340467 := bstep (se 1 (by rfl) ⟨15255350, by rfl⟩ : syracuseStep 20340467 = 30510701) B30510701
theorem B5209865 : Blo 1543469 5209865 := bstep (se 2 (by rfl) ⟨1953699, by rfl⟩ : syracuseStep 5209865 = 3907399) B3907399
theorem B2318111 : Blo 1543469 2318111 := bstep (se 1 (by rfl) ⟨1738583, by rfl⟩ : syracuseStep 2318111 = 3477167) B3477167
theorem B3342223 : Blo 1543469 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B3473351 : Blo 1543469 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B3907561 : Blo 1543469 3907561 := bstep (se 2 (by rfl) ⟨1465335, by rfl⟩ : syracuseStep 3907561 = 2930671) B2930671
theorem B3473531 : Blo 1543469 3473531 := bstep (se 1 (by rfl) ⟨2605148, by rfl⟩ : syracuseStep 3473531 = 5210297) B5210297
theorem B13377869 : Blo 1543469 13377869 := bstep (se 3 (by rfl) ⟨2508350, by rfl⟩ : syracuseStep 13377869 = 5016701) B5016701
theorem B7815527 : Blo 1543469 7815527 := bstep (se 1 (by rfl) ⟨5861645, by rfl⟩ : syracuseStep 7815527 = 11723291) B11723291
theorem B3473801 : Blo 1543469 3473801 := bstep (se 2 (by rfl) ⟨1302675, by rfl⟩ : syracuseStep 3473801 = 2605351) B2605351
theorem B3473819 : Blo 1543469 3473819 := bstep (se 1 (by rfl) ⟨2605364, by rfl⟩ : syracuseStep 3473819 = 5210729) B5210729
theorem B3908321 : Blo 1543469 3908321 := bstep (se 2 (by rfl) ⟨1465620, by rfl⟩ : syracuseStep 3908321 = 2931241) B2931241
theorem B1737535 : Blo 1543469 1737535 := bstep (se 1 (by rfl) ⟨1303151, by rfl⟩ : syracuseStep 1737535 = 2606303) B2606303
theorem B9897167 : Blo 1543469 9897167 := bstep (se 1 (by rfl) ⟨7422875, by rfl⟩ : syracuseStep 9897167 = 14845751) B14845751
theorem B4400381 : Blo 1543469 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B26379593 : Blo 1543469 26379593 := bstep (se 2 (by rfl) ⟨9892347, by rfl⟩ : syracuseStep 26379593 = 19784695) B19784695
theorem B25060765 : Blo 1543469 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B3474971 : Blo 1543469 3474971 := bstep (se 1 (by rfl) ⟨2606228, by rfl⟩ : syracuseStep 3474971 = 5212457) B5212457
theorem B17598059 : Blo 1543469 17598059 := bstep (se 1 (by rfl) ⟨13198544, by rfl⟩ : syracuseStep 17598059 = 26397089) B26397089
theorem B28182275 : Blo 1543469 28182275 := bstep (se 1 (by rfl) ⟨21136706, by rfl⟩ : syracuseStep 28182275 = 42273413) B42273413
theorem B4400905 : Blo 1543469 4400905 := bstep (se 2 (by rfl) ⟨1650339, by rfl⟩ : syracuseStep 4400905 = 3300679) B3300679
theorem B5212025 : Blo 1543469 5212025 := bstep (se 2 (by rfl) ⟨1954509, by rfl⟩ : syracuseStep 5212025 = 3909019) B3909019
theorem B9889735 : Blo 1543469 9889735 := bstep (se 1 (by rfl) ⟨7417301, by rfl⟩ : syracuseStep 9889735 = 14834603) B14834603
theorem B11733011 : Blo 1543469 11733011 := bstep (se 1 (by rfl) ⟨8799758, by rfl⟩ : syracuseStep 11733011 = 17599517) B17599517
theorem B5212403 : Blo 1543469 5212403 := bstep (se 1 (by rfl) ⟨3909302, by rfl⟩ : syracuseStep 5212403 = 7818605) B7818605
theorem B7817633 : Blo 1543469 7817633 := bstep (se 2 (by rfl) ⟨2931612, by rfl⟩ : syracuseStep 7817633 = 5863225) B5863225
theorem B13560311 : Blo 1543469 13560311 := bstep (se 1 (by rfl) ⟨10170233, by rfl⟩ : syracuseStep 13560311 = 20340467) B20340467
theorem B16697927 : Blo 1543469 16697927 := bstep (se 1 (by rfl) ⟨12523445, by rfl⟩ : syracuseStep 16697927 = 25046891) B25046891
theorem B2607707 : Blo 1543469 2607707 := bstep (se 1 (by rfl) ⟨1955780, by rfl⟩ : syracuseStep 2607707 = 3911561) B3911561
theorem B20056709 : Blo 1543469 20056709 := bstep (se 4 (by rfl) ⟨1880316, by rfl⟩ : syracuseStep 20056709 = 3760633) B3760633
theorem B13200185 : Blo 1543469 13200185 := bstep (se 2 (by rfl) ⟨4950069, by rfl⟩ : syracuseStep 13200185 = 9900139) B9900139
theorem B15256633 : Blo 1543469 15256633 := bstep (se 2 (by rfl) ⟨5721237, by rfl⟩ : syracuseStep 15256633 = 11442475) B11442475
theorem B21146777 : Blo 1543469 21146777 := bstep (se 2 (by rfl) ⟨7930041, by rfl⟩ : syracuseStep 21146777 = 15860083) B15860083
theorem B44518571 : Blo 1543469 44518571 := bstep (se 1 (by rfl) ⟨33388928, by rfl⟩ : syracuseStep 44518571 = 66777857) B66777857
theorem B1543707 : Blo 1543469 1543707 := bstep (se 1 (by rfl) ⟨1157780, by rfl⟩ : syracuseStep 1543707 = 2315561) B2315561
theorem B1543839 : Blo 1543469 1543839 := bstep (se 1 (by rfl) ⟨1157879, by rfl⟩ : syracuseStep 1543839 = 2315759) B2315759
theorem B8351513 : Blo 1543469 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B5214023 : Blo 1543469 5214023 := bstep (se 1 (by rfl) ⟨3910517, by rfl⟩ : syracuseStep 5214023 = 7821035) B7821035
theorem B1544103 : Blo 1543469 1544103 := bstep (se 1 (by rfl) ⟨1158077, by rfl⟩ : syracuseStep 1544103 = 2316155) B2316155
theorem B1544127 : Blo 1543469 1544127 := bstep (se 1 (by rfl) ⟨1158095, by rfl⟩ : syracuseStep 1544127 = 2316191) B2316191
theorem B3911753 : Blo 1543469 3911753 := bstep (se 2 (by rfl) ⟨1466907, by rfl⟩ : syracuseStep 3911753 = 2933815) B2933815
theorem B1544283 : Blo 1543469 1544283 := bstep (se 1 (by rfl) ⟨1158212, by rfl⟩ : syracuseStep 1544283 = 2316425) B2316425
theorem B13193351 : Blo 1543469 13193351 := bstep (se 1 (by rfl) ⟨9895013, by rfl⟩ : syracuseStep 13193351 = 19790027) B19790027
theorem B16699567 : Blo 1543469 16699567 := bstep (se 1 (by rfl) ⟨12524675, by rfl⟩ : syracuseStep 16699567 = 25049351) B25049351
theorem B1544383 : Blo 1543469 1544383 := bstep (se 1 (by rfl) ⟨1158287, by rfl⟩ : syracuseStep 1544383 = 2316575) B2316575
theorem B3911935 : Blo 1543469 3911935 := bstep (se 1 (by rfl) ⟨2933951, by rfl⟩ : syracuseStep 3911935 = 5867903) B5867903
theorem B1544751 : Blo 1543469 1544751 := bstep (se 1 (by rfl) ⟨1158563, by rfl⟩ : syracuseStep 1544751 = 2317127) B2317127
theorem B8352359 : Blo 1543469 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B9523817 : Blo 1543469 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B9900731 : Blo 1543469 9900731 := bstep (se 1 (by rfl) ⟨7425548, by rfl⟩ : syracuseStep 9900731 = 14851097) B14851097
theorem B47551211 : Blo 1543469 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B2315207 : Blo 1543469 2315207 := bstep (se 1 (by rfl) ⟨1736405, by rfl⟩ : syracuseStep 2315207 = 3472811) B3472811
theorem B2315231 : Blo 1543469 2315231 := bstep (se 1 (by rfl) ⟨1736423, by rfl⟩ : syracuseStep 2315231 = 3472847) B3472847
theorem B1954783 : Blo 1543469 1954783 := bstep (se 1 (by rfl) ⟨1466087, by rfl⟩ : syracuseStep 1954783 = 2932175) B2932175
theorem B1545327 : Blo 1543469 1545327 := bstep (se 1 (by rfl) ⟨1158995, by rfl⟩ : syracuseStep 1545327 = 2317991) B2317991
theorem B1545407 : Blo 1543469 1545407 := bstep (se 1 (by rfl) ⟨1159055, by rfl⟩ : syracuseStep 1545407 = 2318111) B2318111
theorem B2315567 : Blo 1543469 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B8344939 : Blo 1543469 8344939 := bstep (se 1 (by rfl) ⟨6258704, by rfl⟩ : syracuseStep 8344939 = 12517409) B12517409
theorem B2315771 : Blo 1543469 2315771 := bstep (se 1 (by rfl) ⟨1736828, by rfl⟩ : syracuseStep 2315771 = 3473657) B3473657
theorem B2315807 : Blo 1543469 2315807 := bstep (se 1 (by rfl) ⟨1736855, by rfl⟩ : syracuseStep 2315807 = 3473711) B3473711
theorem B2315945 : Blo 1543469 2315945 := bstep (se 2 (by rfl) ⟨868479, by rfl⟩ : syracuseStep 2315945 = 1736959) B1736959
theorem B2348713 : Blo 1543469 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B2315951 : Blo 1543469 2315951 := bstep (se 1 (by rfl) ⟨1736963, by rfl⟩ : syracuseStep 2315951 = 3473927) B3473927
theorem B3299039 : Blo 1543469 3299039 := bstep (se 1 (by rfl) ⟨2474279, by rfl⟩ : syracuseStep 3299039 = 4948559) B4948559
theorem B30103325 : Blo 1543469 30103325 := bstep (se 3 (by rfl) ⟨5644373, by rfl⟩ : syracuseStep 30103325 = 11288747) B11288747
theorem B2316071 : Blo 1543469 2316071 := bstep (se 1 (by rfl) ⟨1737053, by rfl⟩ : syracuseStep 2316071 = 3474107) B3474107
theorem B2316329 : Blo 1543469 2316329 := bstep (se 2 (by rfl) ⟨868623, by rfl⟩ : syracuseStep 2316329 = 1737247) B1737247
theorem B2316359 : Blo 1543469 2316359 := bstep (se 1 (by rfl) ⟨1737269, by rfl⟩ : syracuseStep 2316359 = 3474539) B3474539
theorem B6600811 : Blo 1543469 6600811 := bstep (se 1 (by rfl) ⟨4950608, by rfl⟩ : syracuseStep 6600811 = 9901217) B9901217
theorem B2930975 : Blo 1543469 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B2316671 : Blo 1543469 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B2316743 : Blo 1543469 2316743 := bstep (se 1 (by rfl) ⟨1737557, by rfl⟩ : syracuseStep 2316743 = 3475115) B3475115
theorem B2316959 : Blo 1543469 2316959 := bstep (se 1 (by rfl) ⟨1737719, by rfl⟩ : syracuseStep 2316959 = 3475439) B3475439
theorem B5012231 : Blo 1543469 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B17595143 : Blo 1543469 17595143 := bstep (se 1 (by rfl) ⟨13196357, by rfl⟩ : syracuseStep 17595143 = 26392715) B26392715
theorem B28572425 : Blo 1543469 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B2317103 : Blo 1543469 2317103 := bstep (se 1 (by rfl) ⟨1737827, by rfl⟩ : syracuseStep 2317103 = 3475655) B3475655
theorem B89045891 : Blo 1543469 89045891 := bstep (se 1 (by rfl) ⟨66784418, by rfl⟩ : syracuseStep 89045891 = 133568837) B133568837
theorem B2317193 : Blo 1543469 2317193 := bstep (se 2 (by rfl) ⟨868947, by rfl⟩ : syracuseStep 2317193 = 1737895) B1737895
theorem B2317223 : Blo 1543469 2317223 := bstep (se 1 (by rfl) ⟨1737917, by rfl⟩ : syracuseStep 2317223 = 3475835) B3475835
theorem B2317403 : Blo 1543469 2317403 := bstep (se 1 (by rfl) ⟨1738052, by rfl⟩ : syracuseStep 2317403 = 3476105) B3476105
theorem B3963995 : Blo 1543469 3963995 := bstep (se 1 (by rfl) ⟨2972996, by rfl⟩ : syracuseStep 3963995 = 5945993) B5945993
theorem B7822493 : Blo 1543469 7822493 := bstep (se 3 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 7822493 = 2933435) B2933435
theorem B2317595 : Blo 1543469 2317595 := bstep (se 1 (by rfl) ⟨1738196, by rfl⟩ : syracuseStep 2317595 = 3476393) B3476393
theorem B22265117 : Blo 1543469 22265117 := bstep (se 3 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 22265117 = 8349419) B8349419
theorem B7822817 : Blo 1543469 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B4177403 : Blo 1543469 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B4398695 : Blo 1543469 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B3473063 : Blo 1543469 3473063 := bstep (se 1 (by rfl) ⟨2604797, by rfl⟩ : syracuseStep 3473063 = 5209595) B5209595
theorem B7814879 : Blo 1543469 7814879 := bstep (se 1 (by rfl) ⟨5861159, by rfl⟩ : syracuseStep 7814879 = 11722319) B11722319
theorem B2318063 : Blo 1543469 2318063 := bstep (se 1 (by rfl) ⟨1738547, by rfl⟩ : syracuseStep 2318063 = 3477095) B3477095
theorem B18784007 : Blo 1543469 18784007 := bstep (se 1 (by rfl) ⟨14088005, by rfl⟩ : syracuseStep 18784007 = 28176011) B28176011
theorem B3473171 : Blo 1543469 3473171 := bstep (se 1 (by rfl) ⟨2604878, by rfl⟩ : syracuseStep 3473171 = 5209757) B5209757
theorem B3473243 : Blo 1543469 3473243 := bstep (se 1 (by rfl) ⟨2604932, by rfl⟩ : syracuseStep 3473243 = 5209865) B5209865
theorem B4456297 : Blo 1543469 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B5210081 : Blo 1543469 5210081 := bstep (se 2 (by rfl) ⟨1953780, by rfl⟩ : syracuseStep 5210081 = 3907561) B3907561
theorem B22266089 : Blo 1543469 22266089 := bstep (se 2 (by rfl) ⟨8349783, by rfl⟩ : syracuseStep 22266089 = 16699567) B16699567
theorem B5210351 : Blo 1543469 5210351 := bstep (se 1 (by rfl) ⟨3907763, by rfl⟩ : syracuseStep 5210351 = 7815527) B7815527
theorem B6349211 : Blo 1543469 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B2605547 : Blo 1543469 2605547 := bstep (se 1 (by rfl) ⟨1954160, by rfl⟩ : syracuseStep 2605547 = 3908321) B3908321
theorem B2933587 : Blo 1543469 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B11732039 : Blo 1543469 11732039 := bstep (se 1 (by rfl) ⟨8799029, by rfl⟩ : syracuseStep 11732039 = 17598059) B17598059
theorem B3474683 : Blo 1543469 3474683 := bstep (se 1 (by rfl) ⟨2606012, by rfl⟩ : syracuseStep 3474683 = 5212025) B5212025
theorem B2606377 : Blo 1543469 2606377 := bstep (se 2 (by rfl) ⟨977391, by rfl⟩ : syracuseStep 2606377 = 1954783) B1954783
theorem B20342177 : Blo 1543469 20342177 := bstep (se 2 (by rfl) ⟨7628316, by rfl⟩ : syracuseStep 20342177 = 15256633) B15256633
theorem B3474935 : Blo 1543469 3474935 := bstep (se 1 (by rfl) ⟨2606201, by rfl⟩ : syracuseStep 3474935 = 5212403) B5212403
theorem B5211755 : Blo 1543469 5211755 := bstep (se 1 (by rfl) ⟨3908816, by rfl⟩ : syracuseStep 5211755 = 7817633) B7817633
theorem B1738471 : Blo 1543469 1738471 := bstep (se 1 (by rfl) ⟨1303853, by rfl⟩ : syracuseStep 1738471 = 2607707) B2607707
theorem B13371139 : Blo 1543469 13371139 := bstep (se 1 (by rfl) ⟨10028354, by rfl⟩ : syracuseStep 13371139 = 20056709) B20056709
theorem B11126585 : Blo 1543469 11126585 := bstep (se 2 (by rfl) ⟨4172469, by rfl⟩ : syracuseStep 11126585 = 8344939) B8344939
theorem B19048283 : Blo 1543469 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B8800123 : Blo 1543469 8800123 := bstep (se 1 (by rfl) ⟨6600092, by rfl⟩ : syracuseStep 8800123 = 13200185) B13200185
theorem B3131617 : Blo 1543469 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B5867873 : Blo 1543469 5867873 := bstep (se 2 (by rfl) ⟨2200452, by rfl⟩ : syracuseStep 5867873 = 4400905) B4400905
theorem B5941729 : Blo 1543469 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B3476015 : Blo 1543469 3476015 := bstep (se 1 (by rfl) ⟨2607011, by rfl⟩ : syracuseStep 3476015 = 5214023) B5214023
theorem B2607835 : Blo 1543469 2607835 := bstep (se 1 (by rfl) ⟨1955876, by rfl⟩ : syracuseStep 2607835 = 3911753) B3911753
theorem B53463797 : Blo 1543469 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B8801081 : Blo 1543469 8801081 := bstep (se 2 (by rfl) ⟨3300405, by rfl⟩ : syracuseStep 8801081 = 6600811) B6600811
theorem B1543471 : Blo 1543469 1543471 := bstep (se 1 (by rfl) ⟨1157603, by rfl⟩ : syracuseStep 1543471 = 2315207) B2315207
theorem B1543487 : Blo 1543469 1543487 := bstep (se 1 (by rfl) ⟨1157615, by rfl⟩ : syracuseStep 1543487 = 2315231) B2315231
theorem B6598111 : Blo 1543469 6598111 := bstep (se 1 (by rfl) ⟨4948583, by rfl⟩ : syracuseStep 6598111 = 9897167) B9897167
theorem B1543711 : Blo 1543469 1543711 := bstep (se 1 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 1543711 = 2315567) B2315567
theorem B1543847 : Blo 1543469 1543847 := bstep (se 1 (by rfl) ⟨1157885, by rfl⟩ : syracuseStep 1543847 = 2315771) B2315771
theorem B1543871 : Blo 1543469 1543871 := bstep (se 1 (by rfl) ⟨1157903, by rfl⟩ : syracuseStep 1543871 = 2315807) B2315807
theorem B1543963 : Blo 1543469 1543963 := bstep (se 1 (by rfl) ⟨1157972, by rfl⟩ : syracuseStep 1543963 = 2315945) B2315945
theorem B1543967 : Blo 1543469 1543967 := bstep (se 1 (by rfl) ⟨1157975, by rfl⟩ : syracuseStep 1543967 = 2315951) B2315951
theorem B2199359 : Blo 1543469 2199359 := bstep (se 1 (by rfl) ⟨1649519, by rfl⟩ : syracuseStep 2199359 = 3299039) B3299039
theorem B18788183 : Blo 1543469 18788183 := bstep (se 1 (by rfl) ⟨14091137, by rfl⟩ : syracuseStep 18788183 = 28182275) B28182275
theorem B1544047 : Blo 1543469 1544047 := bstep (se 1 (by rfl) ⟨1158035, by rfl⟩ : syracuseStep 1544047 = 2316071) B2316071
theorem B1544219 : Blo 1543469 1544219 := bstep (se 1 (by rfl) ⟨1158164, by rfl⟩ : syracuseStep 1544219 = 2316329) B2316329
theorem B1544239 : Blo 1543469 1544239 := bstep (se 1 (by rfl) ⟨1158179, by rfl⟩ : syracuseStep 1544239 = 2316359) B2316359
theorem B1953983 : Blo 1543469 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B1544447 : Blo 1543469 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1544495 : Blo 1543469 1544495 := bstep (se 1 (by rfl) ⟨1158371, by rfl⟩ : syracuseStep 1544495 = 2316743) B2316743
theorem B9040207 : Blo 1543469 9040207 := bstep (se 1 (by rfl) ⟨6780155, by rfl⟩ : syracuseStep 9040207 = 13560311) B13560311
theorem B1544639 : Blo 1543469 1544639 := bstep (se 1 (by rfl) ⟨1158479, by rfl⟩ : syracuseStep 1544639 = 2316959) B2316959
theorem B1544735 : Blo 1543469 1544735 := bstep (se 1 (by rfl) ⟨1158551, by rfl⟩ : syracuseStep 1544735 = 2317103) B2317103
theorem B59363927 : Blo 1543469 59363927 := bstep (se 1 (by rfl) ⟨44522945, by rfl⟩ : syracuseStep 59363927 = 89045891) B89045891
theorem B1544795 : Blo 1543469 1544795 := bstep (se 1 (by rfl) ⟨1158596, by rfl⟩ : syracuseStep 1544795 = 2317193) B2317193
theorem B1544815 : Blo 1543469 1544815 := bstep (se 1 (by rfl) ⟨1158611, by rfl⟩ : syracuseStep 1544815 = 2317223) B2317223
theorem B1544935 : Blo 1543469 1544935 := bstep (se 1 (by rfl) ⟨1158701, by rfl⟩ : syracuseStep 1544935 = 2317403) B2317403
theorem B2642663 : Blo 1543469 2642663 := bstep (se 1 (by rfl) ⟨1981997, by rfl⟩ : syracuseStep 2642663 = 3963995) B3963995
theorem B5214995 : Blo 1543469 5214995 := bstep (se 1 (by rfl) ⟨3911246, by rfl⟩ : syracuseStep 5214995 = 7822493) B7822493
theorem B1545063 : Blo 1543469 1545063 := bstep (se 1 (by rfl) ⟨1158797, by rfl⟩ : syracuseStep 1545063 = 2317595) B2317595
theorem B5215211 : Blo 1543469 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B2315375 : Blo 1543469 2315375 := bstep (se 1 (by rfl) ⟨1736531, by rfl⟩ : syracuseStep 2315375 = 3473063) B3473063
theorem B1545375 : Blo 1543469 1545375 := bstep (se 1 (by rfl) ⟨1159031, by rfl⟩ : syracuseStep 1545375 = 2318063) B2318063
theorem B12522671 : Blo 1543469 12522671 := bstep (se 1 (by rfl) ⟨9392003, by rfl⟩ : syracuseStep 12522671 = 18784007) B18784007
theorem B2315447 : Blo 1543469 2315447 := bstep (se 1 (by rfl) ⟨1736585, by rfl⟩ : syracuseStep 2315447 = 3473171) B3473171
theorem B5567675 : Blo 1543469 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B2315495 : Blo 1543469 2315495 := bstep (se 1 (by rfl) ⟨1736621, by rfl⟩ : syracuseStep 2315495 = 3473243) B3473243
theorem B13186313 : Blo 1543469 13186313 := bstep (se 2 (by rfl) ⟨4944867, by rfl⟩ : syracuseStep 13186313 = 9889735) B9889735
theorem B2315687 : Blo 1543469 2315687 := bstep (se 1 (by rfl) ⟨1736765, by rfl⟩ : syracuseStep 2315687 = 3473531) B3473531
theorem B8795567 : Blo 1543469 8795567 := bstep (se 1 (by rfl) ⟨6596675, by rfl⟩ : syracuseStep 8795567 = 13193351) B13193351
theorem B8918579 : Blo 1543469 8918579 := bstep (se 1 (by rfl) ⟨6688934, by rfl⟩ : syracuseStep 8918579 = 13377869) B13377869
theorem B2315867 : Blo 1543469 2315867 := bstep (se 1 (by rfl) ⟨1736900, by rfl⟩ : syracuseStep 2315867 = 3473801) B3473801
theorem B2315879 : Blo 1543469 2315879 := bstep (se 1 (by rfl) ⟨1736909, by rfl⟩ : syracuseStep 2315879 = 3473819) B3473819
theorem B5215913 : Blo 1543469 5215913 := bstep (se 2 (by rfl) ⟨1955967, by rfl⟩ : syracuseStep 5215913 = 3911935) B3911935
theorem B5568239 : Blo 1543469 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B6600487 : Blo 1543469 6600487 := bstep (se 1 (by rfl) ⟨4950365, by rfl⟩ : syracuseStep 6600487 = 9900731) B9900731
theorem B31700807 : Blo 1543469 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B17586395 : Blo 1543469 17586395 := bstep (se 1 (by rfl) ⟨13189796, by rfl⟩ : syracuseStep 17586395 = 26379593) B26379593
theorem B2316647 : Blo 1543469 2316647 := bstep (se 1 (by rfl) ⟨1737485, by rfl⟩ : syracuseStep 2316647 = 3474971) B3474971
theorem B2316713 : Blo 1543469 2316713 := bstep (se 2 (by rfl) ⟨868767, by rfl⟩ : syracuseStep 2316713 = 1737535) B1737535
theorem B20068883 : Blo 1543469 20068883 := bstep (se 1 (by rfl) ⟨15051662, by rfl⟩ : syracuseStep 20068883 = 30103325) B30103325
theorem B7822007 : Blo 1543469 7822007 := bstep (se 1 (by rfl) ⟨5866505, by rfl⟩ : syracuseStep 7822007 = 11733011) B11733011
theorem B11131951 : Blo 1543469 11131951 := bstep (se 1 (by rfl) ⟨8348963, by rfl⟩ : syracuseStep 11131951 = 16697927) B16697927
theorem B11730095 : Blo 1543469 11730095 := bstep (se 1 (by rfl) ⟨8797571, by rfl⟩ : syracuseStep 11730095 = 17595143) B17595143
theorem B33414353 : Blo 1543469 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B14097851 : Blo 1543469 14097851 := bstep (se 1 (by rfl) ⟨10573388, by rfl⟩ : syracuseStep 14097851 = 21146777) B21146777
theorem B29679047 : Blo 1543469 29679047 := bstep (se 1 (by rfl) ⟨22259285, by rfl⟩ : syracuseStep 29679047 = 44518571) B44518571
theorem B14843411 : Blo 1543469 14843411 := bstep (se 1 (by rfl) ⟨11132558, by rfl⟩ : syracuseStep 14843411 = 22265117) B22265117
theorem B2784935 : Blo 1543469 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B2932463 : Blo 1543469 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B5209919 : Blo 1543469 5209919 := bstep (se 1 (by rfl) ⟨3907439, by rfl⟩ : syracuseStep 5209919 = 7814879) B7814879
theorem B3473387 : Blo 1543469 3473387 := bstep (se 1 (by rfl) ⟨2605040, by rfl⟩ : syracuseStep 3473387 = 5210081) B5210081
theorem B14844059 : Blo 1543469 14844059 := bstep (se 1 (by rfl) ⟨11133044, by rfl⟩ : syracuseStep 14844059 = 22266089) B22266089
theorem B3473567 : Blo 1543469 3473567 := bstep (se 1 (by rfl) ⟨2605175, by rfl⟩ : syracuseStep 3473567 = 5210351) B5210351
theorem B1737031 : Blo 1543469 1737031 := bstep (se 1 (by rfl) ⟨1302773, by rfl⟩ : syracuseStep 1737031 = 2605547) B2605547
theorem B39575951 : Blo 1543469 39575951 := bstep (se 1 (by rfl) ⟨29681963, by rfl⟩ : syracuseStep 39575951 = 59363927) B59363927
theorem B5210621 : Blo 1543469 5210621 := bstep (se 3 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 5210621 = 1953983) B1953983
theorem B7922305 : Blo 1543469 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B8348447 : Blo 1543469 8348447 := bstep (se 1 (by rfl) ⟨6261335, by rfl⟩ : syracuseStep 8348447 = 12522671) B12522671
theorem B8790875 : Blo 1543469 8790875 := bstep (se 1 (by rfl) ⟨6593156, by rfl⟩ : syracuseStep 8790875 = 13186313) B13186313
theorem B3474503 : Blo 1543469 3474503 := bstep (se 1 (by rfl) ⟨2605877, by rfl⟩ : syracuseStep 3474503 = 5211755) B5211755
theorem B3712159 : Blo 1543469 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B12698855 : Blo 1543469 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B11724263 : Blo 1543469 11724263 := bstep (se 1 (by rfl) ⟨8793197, by rfl⟩ : syracuseStep 11724263 = 17586395) B17586395
theorem B13379255 : Blo 1543469 13379255 := bstep (se 1 (by rfl) ⟨10034441, by rfl⟩ : syracuseStep 13379255 = 20068883) B20068883
theorem B3475169 : Blo 1543469 3475169 := bstep (se 2 (by rfl) ⟨1303188, by rfl⟩ : syracuseStep 3475169 = 2606377) B2606377
theorem B5867387 : Blo 1543469 5867387 := bstep (se 1 (by rfl) ⟨4400540, by rfl⟩ : syracuseStep 5867387 = 8801081) B8801081
theorem B7047101 : Blo 1543469 7047101 := bstep (se 3 (by rfl) ⟨1321331, by rfl⟩ : syracuseStep 7047101 = 2642663) B2642663
theorem B22276235 : Blo 1543469 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B9398567 : Blo 1543469 9398567 := bstep (se 1 (by rfl) ⟨7048925, by rfl⟩ : syracuseStep 9398567 = 14097851) B14097851
theorem B19786031 : Blo 1543469 19786031 := bstep (se 1 (by rfl) ⟨14839523, by rfl⟩ : syracuseStep 19786031 = 29679047) B29679047
theorem B17828185 : Blo 1543469 17828185 := bstep (se 2 (by rfl) ⟨6685569, by rfl⟩ : syracuseStep 17828185 = 13371139) B13371139
theorem B8800649 : Blo 1543469 8800649 := bstep (se 2 (by rfl) ⟨3300243, by rfl⟩ : syracuseStep 8800649 = 6600487) B6600487
theorem B11733497 : Blo 1543469 11733497 := bstep (se 2 (by rfl) ⟨4400061, by rfl⟩ : syracuseStep 11733497 = 8800123) B8800123
theorem B12053609 : Blo 1543469 12053609 := bstep (se 2 (by rfl) ⟨4520103, by rfl⟩ : syracuseStep 12053609 = 9040207) B9040207
theorem B14847133 : Blo 1543469 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B3476663 : Blo 1543469 3476663 := bstep (se 1 (by rfl) ⟨2607497, by rfl⟩ : syracuseStep 3476663 = 5214995) B5214995
theorem B3476807 : Blo 1543469 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B1543583 : Blo 1543469 1543583 := bstep (se 1 (by rfl) ⟨1157687, by rfl⟩ : syracuseStep 1543583 = 2315375) B2315375
theorem B1543631 : Blo 1543469 1543631 := bstep (se 1 (by rfl) ⟨1157723, by rfl⟩ : syracuseStep 1543631 = 2315447) B2315447
theorem B1543663 : Blo 1543469 1543663 := bstep (se 1 (by rfl) ⟨1157747, by rfl⟩ : syracuseStep 1543663 = 2315495) B2315495
theorem B13561451 : Blo 1543469 13561451 := bstep (se 1 (by rfl) ⟨10171088, by rfl⟩ : syracuseStep 13561451 = 20342177) B20342177
theorem B1543791 : Blo 1543469 1543791 := bstep (se 1 (by rfl) ⟨1157843, by rfl⟩ : syracuseStep 1543791 = 2315687) B2315687
theorem B3477113 : Blo 1543469 3477113 := bstep (se 2 (by rfl) ⟨1303917, by rfl⟩ : syracuseStep 3477113 = 2607835) B2607835
theorem B1543911 : Blo 1543469 1543911 := bstep (se 1 (by rfl) ⟨1157933, by rfl⟩ : syracuseStep 1543911 = 2315867) B2315867
theorem B1543919 : Blo 1543469 1543919 := bstep (se 1 (by rfl) ⟨1157939, by rfl⟩ : syracuseStep 1543919 = 2315879) B2315879
theorem B3911449 : Blo 1543469 3911449 := bstep (se 2 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 3911449 = 2933587) B2933587
theorem B3477275 : Blo 1543469 3477275 := bstep (se 1 (by rfl) ⟨2607956, by rfl⟩ : syracuseStep 3477275 = 5215913) B5215913
theorem B3911915 : Blo 1543469 3911915 := bstep (se 1 (by rfl) ⟨2933936, by rfl⟩ : syracuseStep 3911915 = 5867873) B5867873
theorem B1544431 : Blo 1543469 1544431 := bstep (se 1 (by rfl) ⟨1158323, by rfl⟩ : syracuseStep 1544431 = 2316647) B2316647
theorem B1544475 : Blo 1543469 1544475 := bstep (se 1 (by rfl) ⟨1158356, by rfl⟩ : syracuseStep 1544475 = 2316713) B2316713
theorem B5214671 : Blo 1543469 5214671 := bstep (se 1 (by rfl) ⟨3911003, by rfl⟩ : syracuseStep 5214671 = 7822007) B7822007
theorem B7819901 : Blo 1543469 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B7820063 : Blo 1543469 7820063 := bstep (se 1 (by rfl) ⟨5865047, by rfl⟩ : syracuseStep 7820063 = 11730095) B11730095
theorem B1856623 : Blo 1543469 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B2315591 : Blo 1543469 2315591 := bstep (se 1 (by rfl) ⟨1736693, by rfl⟩ : syracuseStep 2315591 = 3473387) B3473387
theorem B4232807 : Blo 1543469 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B4175489 : Blo 1543469 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B7821359 : Blo 1543469 7821359 := bstep (se 1 (by rfl) ⟨5866019, by rfl⟩ : syracuseStep 7821359 = 11732039) B11732039
theorem B2316455 : Blo 1543469 2316455 := bstep (se 1 (by rfl) ⟨1737341, by rfl⟩ : syracuseStep 2316455 = 3474683) B3474683
theorem B5863711 : Blo 1543469 5863711 := bstep (se 1 (by rfl) ⟨4397783, by rfl⟩ : syracuseStep 5863711 = 8795567) B8795567
theorem B2316623 : Blo 1543469 2316623 := bstep (se 1 (by rfl) ⟨1737467, by rfl⟩ : syracuseStep 2316623 = 3474935) B3474935
theorem B5945719 : Blo 1543469 5945719 := bstep (se 1 (by rfl) ⟨4459289, by rfl⟩ : syracuseStep 5945719 = 8918579) B8918579
theorem B21133871 : Blo 1543469 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B14842601 : Blo 1543469 14842601 := bstep (se 2 (by rfl) ⟨5565975, by rfl⟩ : syracuseStep 14842601 = 11131951) B11131951
theorem B2317343 : Blo 1543469 2317343 := bstep (se 1 (by rfl) ⟨1738007, by rfl⟩ : syracuseStep 2317343 = 3476015) B3476015
theorem B35642531 : Blo 1543469 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B8797481 : Blo 1543469 8797481 := bstep (se 2 (by rfl) ⟨3299055, by rfl⟩ : syracuseStep 8797481 = 6598111) B6598111
theorem B29670893 : Blo 1543469 29670893 := bstep (se 3 (by rfl) ⟨5563292, by rfl⟩ : syracuseStep 29670893 = 11126585) B11126585
theorem B5864957 : Blo 1543469 5864957 := bstep (se 3 (by rfl) ⟨1099679, by rfl⟩ : syracuseStep 5864957 = 2199359) B2199359
theorem B2317961 : Blo 1543469 2317961 := bstep (se 2 (by rfl) ⟨869235, by rfl⟩ : syracuseStep 2317961 = 1738471) B1738471
theorem B9895607 : Blo 1543469 9895607 := bstep (se 1 (by rfl) ⟨7421705, by rfl⟩ : syracuseStep 9895607 = 14843411) B14843411
theorem B3473279 : Blo 1543469 3473279 := bstep (se 1 (by rfl) ⟨2604959, by rfl⟩ : syracuseStep 3473279 = 5209919) B5209919
theorem B12525455 : Blo 1543469 12525455 := bstep (se 1 (by rfl) ⟨9394091, by rfl⟩ : syracuseStep 12525455 = 18788183) B18788183
theorem B9896039 : Blo 1543469 9896039 := bstep (se 1 (by rfl) ⟨7422029, by rfl⟩ : syracuseStep 9896039 = 14844059) B14844059
theorem B3473747 : Blo 1543469 3473747 := bstep (se 1 (by rfl) ⟨2605310, by rfl⟩ : syracuseStep 3473747 = 5210621) B5210621
theorem B7816175 : Blo 1543469 7816175 := bstep (se 1 (by rfl) ⟨5862131, by rfl⟩ : syracuseStep 7816175 = 11724263) B11724263
theorem B2475497 : Blo 1543469 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B13190687 : Blo 1543469 13190687 := bstep (se 1 (by rfl) ⟨9893015, by rfl⟩ : syracuseStep 13190687 = 19786031) B19786031
theorem B5867099 : Blo 1543469 5867099 := bstep (se 1 (by rfl) ⟨4400324, by rfl⟩ : syracuseStep 5867099 = 8800649) B8800649
theorem B3909971 : Blo 1543469 3909971 := bstep (se 1 (by rfl) ⟨2932478, by rfl⟩ : syracuseStep 3909971 = 5864957) B5864957
theorem B6597071 : Blo 1543469 6597071 := bstep (se 1 (by rfl) ⟨4947803, by rfl⟩ : syracuseStep 6597071 = 9895607) B9895607
theorem B8350303 : Blo 1543469 8350303 := bstep (se 1 (by rfl) ⟨6262727, by rfl⟩ : syracuseStep 8350303 = 12525455) B12525455
theorem B2607943 : Blo 1543469 2607943 := bstep (se 1 (by rfl) ⟨1955957, by rfl⟩ : syracuseStep 2607943 = 3911915) B3911915
theorem B3476447 : Blo 1543469 3476447 := bstep (se 1 (by rfl) ⟨2607335, by rfl⟩ : syracuseStep 3476447 = 5214671) B5214671
theorem B59403293 : Blo 1543469 59403293 := bstep (se 3 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 59403293 = 22276235) B22276235
theorem B7818281 : Blo 1543469 7818281 := bstep (se 2 (by rfl) ⟨2931855, by rfl⟩ : syracuseStep 7818281 = 5863711) B5863711
theorem B5213267 : Blo 1543469 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B5565631 : Blo 1543469 5565631 := bstep (se 1 (by rfl) ⟨4174223, by rfl⟩ : syracuseStep 5565631 = 8348447) B8348447
theorem B5213375 : Blo 1543469 5213375 := bstep (se 1 (by rfl) ⟨3910031, by rfl⟩ : syracuseStep 5213375 = 7820063) B7820063
theorem B5860583 : Blo 1543469 5860583 := bstep (se 1 (by rfl) ⟨4395437, by rfl⟩ : syracuseStep 5860583 = 8790875) B8790875
theorem B8465903 : Blo 1543469 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B1543727 : Blo 1543469 1543727 := bstep (se 1 (by rfl) ⟨1157795, by rfl⟩ : syracuseStep 1543727 = 2315591) B2315591
theorem B2821871 : Blo 1543469 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B3911591 : Blo 1543469 3911591 := bstep (se 1 (by rfl) ⟨2933693, by rfl⟩ : syracuseStep 3911591 = 5867387) B5867387
theorem B5214239 : Blo 1543469 5214239 := bstep (se 1 (by rfl) ⟨3910679, by rfl⟩ : syracuseStep 5214239 = 7821359) B7821359
theorem B1544303 : Blo 1543469 1544303 := bstep (se 1 (by rfl) ⟨1158227, by rfl⟩ : syracuseStep 1544303 = 2316455) B2316455
theorem B19796177 : Blo 1543469 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B1544415 : Blo 1543469 1544415 := bstep (se 1 (by rfl) ⟨1158311, by rfl⟩ : syracuseStep 1544415 = 2316623) B2316623
theorem B1544895 : Blo 1543469 1544895 := bstep (se 1 (by rfl) ⟨1158671, by rfl⟩ : syracuseStep 1544895 = 2317343) B2317343
theorem B23761687 : Blo 1543469 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B19780595 : Blo 1543469 19780595 := bstep (se 1 (by rfl) ⟨14835446, by rfl⟩ : syracuseStep 19780595 = 29670893) B29670893
theorem B5215265 : Blo 1543469 5215265 := bstep (se 2 (by rfl) ⟨1955724, by rfl⟩ : syracuseStep 5215265 = 3911449) B3911449
theorem B9040967 : Blo 1543469 9040967 := bstep (se 1 (by rfl) ⟨6780725, by rfl⟩ : syracuseStep 9040967 = 13561451) B13561451
theorem B1545307 : Blo 1543469 1545307 := bstep (se 1 (by rfl) ⟨1158980, by rfl⟩ : syracuseStep 1545307 = 2317961) B2317961
theorem B2315519 : Blo 1543469 2315519 := bstep (se 1 (by rfl) ⟨1736639, by rfl⟩ : syracuseStep 2315519 = 3473279) B3473279
theorem B2315711 : Blo 1543469 2315711 := bstep (se 1 (by rfl) ⟨1736783, by rfl⟩ : syracuseStep 2315711 = 3473567) B3473567
theorem B26383967 : Blo 1543469 26383967 := bstep (se 1 (by rfl) ⟨19787975, by rfl⟩ : syracuseStep 26383967 = 39575951) B39575951
theorem B2316041 : Blo 1543469 2316041 := bstep (se 2 (by rfl) ⟨868515, by rfl⟩ : syracuseStep 2316041 = 1737031) B1737031
theorem B23770913 : Blo 1543469 23770913 := bstep (se 2 (by rfl) ⟨8914092, by rfl⟩ : syracuseStep 23770913 = 17828185) B17828185
theorem B7927625 : Blo 1543469 7927625 := bstep (se 2 (by rfl) ⟨2972859, by rfl⟩ : syracuseStep 7927625 = 5945719) B5945719
theorem B42252293 : Blo 1543469 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B2316335 : Blo 1543469 2316335 := bstep (se 1 (by rfl) ⟨1737251, by rfl⟩ : syracuseStep 2316335 = 3474503) B3474503
theorem B19798181 : Blo 1543469 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B2783659 : Blo 1543469 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B8919503 : Blo 1543469 8919503 := bstep (se 1 (by rfl) ⟨6689627, by rfl⟩ : syracuseStep 8919503 = 13379255) B13379255
theorem B2316779 : Blo 1543469 2316779 := bstep (se 1 (by rfl) ⟨1737584, by rfl⟩ : syracuseStep 2316779 = 3475169) B3475169
theorem B6265711 : Blo 1543469 6265711 := bstep (se 1 (by rfl) ⟨4699283, by rfl⟩ : syracuseStep 6265711 = 9398567) B9398567
theorem B7822331 : Blo 1543469 7822331 := bstep (se 1 (by rfl) ⟨5866748, by rfl⟩ : syracuseStep 7822331 = 11733497) B11733497
theorem B14089247 : Blo 1543469 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B9895067 : Blo 1543469 9895067 := bstep (se 1 (by rfl) ⟨7421300, by rfl⟩ : syracuseStep 9895067 = 14842601) B14842601
theorem B8035739 : Blo 1543469 8035739 := bstep (se 1 (by rfl) ⟨6026804, by rfl⟩ : syracuseStep 8035739 = 12053609) B12053609
theorem B2317775 : Blo 1543469 2317775 := bstep (se 1 (by rfl) ⟨1738331, by rfl⟩ : syracuseStep 2317775 = 3476663) B3476663
theorem B5864987 : Blo 1543469 5864987 := bstep (se 1 (by rfl) ⟨4398740, by rfl⟩ : syracuseStep 5864987 = 8797481) B8797481
theorem B2317871 : Blo 1543469 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B2318075 : Blo 1543469 2318075 := bstep (se 1 (by rfl) ⟨1738556, by rfl⟩ : syracuseStep 2318075 = 3477113) B3477113
theorem B18792269 : Blo 1543469 18792269 := bstep (se 3 (by rfl) ⟨3523550, by rfl⟩ : syracuseStep 18792269 = 7047101) B7047101
theorem B2318183 : Blo 1543469 2318183 := bstep (se 1 (by rfl) ⟨1738637, by rfl⟩ : syracuseStep 2318183 = 3477275) B3477275
theorem B13197451 : Blo 1543469 13197451 := bstep (se 1 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 13197451 = 19796177) B19796177
theorem B3711545 : Blo 1543469 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B5210783 : Blo 1543469 5210783 := bstep (se 1 (by rfl) ⟨3908087, by rfl⟩ : syracuseStep 5210783 = 7816175) B7816175
theorem B11133737 : Blo 1543469 11133737 := bstep (se 2 (by rfl) ⟨4175151, by rfl⟩ : syracuseStep 11133737 = 8350303) B8350303
theorem B17589311 : Blo 1543469 17589311 := bstep (se 1 (by rfl) ⟨13191983, by rfl⟩ : syracuseStep 17589311 = 26383967) B26383967
theorem B5285083 : Blo 1543469 5285083 := bstep (se 1 (by rfl) ⟨3963812, by rfl⟩ : syracuseStep 5285083 = 7927625) B7927625
theorem B13198787 : Blo 1543469 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B2606647 : Blo 1543469 2606647 := bstep (se 1 (by rfl) ⟨1954985, by rfl⟩ : syracuseStep 2606647 = 3909971) B3909971
theorem B39602195 : Blo 1543469 39602195 := bstep (se 1 (by rfl) ⟨29701646, by rfl⟩ : syracuseStep 39602195 = 59403293) B59403293
theorem B5212187 : Blo 1543469 5212187 := bstep (se 1 (by rfl) ⟨3909140, by rfl⟩ : syracuseStep 5212187 = 7818281) B7818281
theorem B3475511 : Blo 1543469 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B6596711 : Blo 1543469 6596711 := bstep (se 1 (by rfl) ⟨4947533, by rfl⟩ : syracuseStep 6596711 = 9895067) B9895067
theorem B3475583 : Blo 1543469 3475583 := bstep (se 1 (by rfl) ⟨2606687, by rfl⟩ : syracuseStep 3475583 = 5213375) B5213375
theorem B3909991 : Blo 1543469 3909991 := bstep (se 1 (by rfl) ⟨2932493, by rfl⟩ : syracuseStep 3909991 = 5864987) B5864987
theorem B12528179 : Blo 1543469 12528179 := bstep (se 1 (by rfl) ⟨9396134, by rfl⟩ : syracuseStep 12528179 = 18792269) B18792269
theorem B2607727 : Blo 1543469 2607727 := bstep (se 1 (by rfl) ⟨1955795, by rfl⟩ : syracuseStep 2607727 = 3911591) B3911591
theorem B3476159 : Blo 1543469 3476159 := bstep (se 1 (by rfl) ⟨2607119, by rfl⟩ : syracuseStep 3476159 = 5214239) B5214239
theorem B6597359 : Blo 1543469 6597359 := bstep (se 1 (by rfl) ⟨4948019, by rfl⟩ : syracuseStep 6597359 = 9896039) B9896039
theorem B3476843 : Blo 1543469 3476843 := bstep (se 1 (by rfl) ⟨2607632, by rfl⟩ : syracuseStep 3476843 = 5215265) B5215265
theorem B1543679 : Blo 1543469 1543679 := bstep (se 1 (by rfl) ⟨1157759, by rfl⟩ : syracuseStep 1543679 = 2315519) B2315519
theorem B1543807 : Blo 1543469 1543807 := bstep (se 1 (by rfl) ⟨1157855, by rfl⟩ : syracuseStep 1543807 = 2315711) B2315711
theorem B1650331 : Blo 1543469 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B8793791 : Blo 1543469 8793791 := bstep (se 1 (by rfl) ⟨6595343, by rfl⟩ : syracuseStep 8793791 = 13190687) B13190687
theorem B31682249 : Blo 1543469 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B3911399 : Blo 1543469 3911399 := bstep (se 1 (by rfl) ⟨2933549, by rfl⟩ : syracuseStep 3911399 = 5867099) B5867099
theorem B3477257 : Blo 1543469 3477257 := bstep (se 2 (by rfl) ⟨1303971, by rfl⟩ : syracuseStep 3477257 = 2607943) B2607943
theorem B1544027 : Blo 1543469 1544027 := bstep (se 1 (by rfl) ⟨1158020, by rfl⟩ : syracuseStep 1544027 = 2316041) B2316041
theorem B28168195 : Blo 1543469 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B1544223 : Blo 1543469 1544223 := bstep (se 1 (by rfl) ⟨1158167, by rfl⟩ : syracuseStep 1544223 = 2316335) B2316335
theorem B1544519 : Blo 1543469 1544519 := bstep (se 1 (by rfl) ⟨1158389, by rfl⟩ : syracuseStep 1544519 = 2316779) B2316779
theorem B7524989 : Blo 1543469 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B5214887 : Blo 1543469 5214887 := bstep (se 1 (by rfl) ⟨3911165, by rfl⟩ : syracuseStep 5214887 = 7822331) B7822331
theorem B9392831 : Blo 1543469 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B1545183 : Blo 1543469 1545183 := bstep (se 1 (by rfl) ⟨1158887, by rfl⟩ : syracuseStep 1545183 = 2317775) B2317775
theorem B1545247 : Blo 1543469 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B1545383 : Blo 1543469 1545383 := bstep (se 1 (by rfl) ⟨1159037, by rfl⟩ : syracuseStep 1545383 = 2318075) B2318075
theorem B1545455 : Blo 1543469 1545455 := bstep (se 1 (by rfl) ⟨1159091, by rfl⟩ : syracuseStep 1545455 = 2318183) B2318183
theorem B2315831 : Blo 1543469 2315831 := bstep (se 1 (by rfl) ⟨1736873, by rfl⟩ : syracuseStep 2315831 = 3473747) B3473747
theorem B13187063 : Blo 1543469 13187063 := bstep (se 1 (by rfl) ⟨9890297, by rfl⟩ : syracuseStep 13187063 = 19780595) B19780595
theorem B6027311 : Blo 1543469 6027311 := bstep (se 1 (by rfl) ⟨4520483, by rfl⟩ : syracuseStep 6027311 = 9040967) B9040967
theorem B8354281 : Blo 1543469 8354281 := bstep (se 2 (by rfl) ⟨3132855, by rfl⟩ : syracuseStep 8354281 = 6265711) B6265711
theorem B7420841 : Blo 1543469 7420841 := bstep (se 2 (by rfl) ⟨2782815, by rfl⟩ : syracuseStep 7420841 = 5565631) B5565631
theorem B4398047 : Blo 1543469 4398047 := bstep (se 1 (by rfl) ⟨3298535, by rfl⟩ : syracuseStep 4398047 = 6597071) B6597071
theorem B5946335 : Blo 1543469 5946335 := bstep (se 1 (by rfl) ⟨4459751, by rfl⟩ : syracuseStep 5946335 = 8919503) B8919503
theorem B2317631 : Blo 1543469 2317631 := bstep (se 1 (by rfl) ⟨1738223, by rfl⟩ : syracuseStep 2317631 = 3476447) B3476447
theorem B63389101 : Blo 1543469 63389101 := bstep (se 3 (by rfl) ⟨11885456, by rfl⟩ : syracuseStep 63389101 = 23770913) B23770913
theorem B3907055 : Blo 1543469 3907055 := bstep (se 1 (by rfl) ⟨2930291, by rfl⟩ : syracuseStep 3907055 = 5860583) B5860583
theorem B5357159 : Blo 1543469 5357159 := bstep (se 1 (by rfl) ⟨4017869, by rfl⟩ : syracuseStep 5357159 = 8035739) B8035739
theorem B5643935 : Blo 1543469 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B17596601 : Blo 1543469 17596601 := bstep (se 2 (by rfl) ⟨6598725, by rfl⟩ : syracuseStep 17596601 = 13197451) B13197451
theorem B2474363 : Blo 1543469 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B3473855 : Blo 1543469 3473855 := bstep (se 1 (by rfl) ⟨2605391, by rfl⟩ : syracuseStep 3473855 = 5210783) B5210783
theorem B7422491 : Blo 1543469 7422491 := bstep (se 1 (by rfl) ⟨5566868, by rfl⟩ : syracuseStep 7422491 = 11133737) B11133737
theorem B8799191 : Blo 1543469 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B8791375 : Blo 1543469 8791375 := bstep (se 1 (by rfl) ⟨6593531, by rfl⟩ : syracuseStep 8791375 = 13187063) B13187063
theorem B3474791 : Blo 1543469 3474791 := bstep (se 1 (by rfl) ⟨2606093, by rfl⟩ : syracuseStep 3474791 = 5212187) B5212187
theorem B7046777 : Blo 1543469 7046777 := bstep (se 2 (by rfl) ⟨2642541, by rfl⟩ : syracuseStep 7046777 = 5285083) B5285083
theorem B84518801 : Blo 1543469 84518801 := bstep (se 2 (by rfl) ⟨31694550, by rfl⟩ : syracuseStep 84518801 = 63389101) B63389101
theorem B3475529 : Blo 1543469 3475529 := bstep (se 2 (by rfl) ⟨1303323, by rfl⟩ : syracuseStep 3475529 = 2606647) B2606647
theorem B3762623 : Blo 1543469 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B21121499 : Blo 1543469 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B2607599 : Blo 1543469 2607599 := bstep (se 1 (by rfl) ⟨1955699, by rfl⟩ : syracuseStep 2607599 = 3911399) B3911399
theorem B5016659 : Blo 1543469 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B3476591 : Blo 1543469 3476591 := bstep (se 1 (by rfl) ⟨2607443, by rfl⟩ : syracuseStep 3476591 = 5214887) B5214887
theorem B6261887 : Blo 1543469 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B5213321 : Blo 1543469 5213321 := bstep (se 2 (by rfl) ⟨1954995, by rfl⟩ : syracuseStep 5213321 = 3909991) B3909991
theorem B11726207 : Blo 1543469 11726207 := bstep (se 1 (by rfl) ⟨8794655, by rfl⟩ : syracuseStep 11726207 = 17589311) B17589311
theorem B3476969 : Blo 1543469 3476969 := bstep (se 2 (by rfl) ⟨1303863, by rfl⟩ : syracuseStep 3476969 = 2607727) B2607727
theorem B1543887 : Blo 1543469 1543887 := bstep (se 1 (by rfl) ⟨1157915, by rfl⟩ : syracuseStep 1543887 = 2315831) B2315831
theorem B4018207 : Blo 1543469 4018207 := bstep (se 1 (by rfl) ⟨3013655, by rfl⟩ : syracuseStep 4018207 = 6027311) B6027311
theorem B8352119 : Blo 1543469 8352119 := bstep (se 1 (by rfl) ⟨6264089, by rfl⟩ : syracuseStep 8352119 = 12528179) B12528179
theorem B2200441 : Blo 1543469 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B1545087 : Blo 1543469 1545087 := bstep (se 1 (by rfl) ⟨1158815, by rfl⟩ : syracuseStep 1545087 = 2317631) B2317631
theorem B5862527 : Blo 1543469 5862527 := bstep (se 1 (by rfl) ⟨4396895, by rfl⟩ : syracuseStep 5862527 = 8793791) B8793791
theorem B37557593 : Blo 1543469 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B11139041 : Blo 1543469 11139041 := bstep (se 2 (by rfl) ⟨4177140, by rfl⟩ : syracuseStep 11139041 = 8354281) B8354281
theorem B26401463 : Blo 1543469 26401463 := bstep (se 1 (by rfl) ⟨19801097, by rfl⟩ : syracuseStep 26401463 = 39602195) B39602195
theorem B2317007 : Blo 1543469 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B4397807 : Blo 1543469 4397807 := bstep (se 1 (by rfl) ⟨3298355, by rfl⟩ : syracuseStep 4397807 = 6596711) B6596711
theorem B2317055 : Blo 1543469 2317055 := bstep (se 1 (by rfl) ⟨1737791, by rfl⟩ : syracuseStep 2317055 = 3475583) B3475583
theorem B228572117 : Blo 1543469 228572117 := bstep (se 7 (by rfl) ⟨2678579, by rfl⟩ : syracuseStep 228572117 = 5357159) B5357159
theorem B2317439 : Blo 1543469 2317439 := bstep (se 1 (by rfl) ⟨1738079, by rfl⟩ : syracuseStep 2317439 = 3476159) B3476159
theorem B4398239 : Blo 1543469 4398239 := bstep (se 1 (by rfl) ⟨3298679, by rfl⟩ : syracuseStep 4398239 = 6597359) B6597359
theorem B4947227 : Blo 1543469 4947227 := bstep (se 1 (by rfl) ⟨3710420, by rfl⟩ : syracuseStep 4947227 = 7420841) B7420841
theorem B2932031 : Blo 1543469 2932031 := bstep (se 1 (by rfl) ⟨2199023, by rfl⟩ : syracuseStep 2932031 = 4398047) B4398047
theorem B3964223 : Blo 1543469 3964223 := bstep (se 1 (by rfl) ⟨2973167, by rfl⟩ : syracuseStep 3964223 = 5946335) B5946335
theorem B2317895 : Blo 1543469 2317895 := bstep (se 1 (by rfl) ⟨1738421, by rfl⟩ : syracuseStep 2317895 = 3476843) B3476843
theorem B2604703 : Blo 1543469 2604703 := bstep (se 1 (by rfl) ⟨1953527, by rfl⟩ : syracuseStep 2604703 = 3907055) B3907055
theorem B2318171 : Blo 1543469 2318171 := bstep (se 1 (by rfl) ⟨1738628, by rfl⟩ : syracuseStep 2318171 = 3477257) B3477257
theorem B5357609 : Blo 1543469 5357609 := bstep (se 2 (by rfl) ⟨2009103, by rfl⟩ : syracuseStep 5357609 = 4018207) B4018207
theorem B11731067 : Blo 1543469 11731067 := bstep (se 1 (by rfl) ⟨8798300, by rfl⟩ : syracuseStep 11731067 = 17596601) B17596601
theorem B4948327 : Blo 1543469 4948327 := bstep (se 1 (by rfl) ⟨3711245, by rfl⟩ : syracuseStep 4948327 = 7422491) B7422491
theorem B5866127 : Blo 1543469 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B3908351 : Blo 1543469 3908351 := bstep (se 1 (by rfl) ⟨2931263, by rfl⟩ : syracuseStep 3908351 = 5862527) B5862527
theorem B53511029 : Blo 1543469 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B2933921 : Blo 1543469 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B56345867 : Blo 1543469 56345867 := bstep (se 1 (by rfl) ⟨42259400, by rfl⟩ : syracuseStep 56345867 = 84518801) B84518801
theorem B2508415 : Blo 1543469 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B1738399 : Blo 1543469 1738399 := bstep (se 1 (by rfl) ⟨1303799, by rfl⟩ : syracuseStep 1738399 = 2607599) B2607599
theorem B152381411 : Blo 1543469 152381411 := bstep (se 1 (by rfl) ⟨114286058, by rfl⟩ : syracuseStep 152381411 = 228572117) B228572117
theorem B3475547 : Blo 1543469 3475547 := bstep (se 1 (by rfl) ⟨2606660, by rfl⟩ : syracuseStep 3475547 = 5213321) B5213321
theorem B7817471 : Blo 1543469 7817471 := bstep (se 1 (by rfl) ⟨5863103, by rfl⟩ : syracuseStep 7817471 = 11726207) B11726207
theorem B1649575 : Blo 1543469 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B25038395 : Blo 1543469 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B4697851 : Blo 1543469 4697851 := bstep (se 1 (by rfl) ⟨3523388, by rfl⟩ : syracuseStep 4697851 = 7046777) B7046777
theorem B7426027 : Blo 1543469 7426027 := bstep (se 1 (by rfl) ⟨5569520, by rfl⟩ : syracuseStep 7426027 = 11139041) B11139041
theorem B17600975 : Blo 1543469 17600975 := bstep (se 1 (by rfl) ⟨13200731, by rfl⟩ : syracuseStep 17600975 = 26401463) B26401463
theorem B1544671 : Blo 1543469 1544671 := bstep (se 1 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 1544671 = 2317007) B2317007
theorem B1544703 : Blo 1543469 1544703 := bstep (se 1 (by rfl) ⟨1158527, by rfl⟩ : syracuseStep 1544703 = 2317055) B2317055
theorem B4174591 : Blo 1543469 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1544959 : Blo 1543469 1544959 := bstep (se 1 (by rfl) ⟨1158719, by rfl⟩ : syracuseStep 1544959 = 2317439) B2317439
theorem B3298151 : Blo 1543469 3298151 := bstep (se 1 (by rfl) ⟨2473613, by rfl⟩ : syracuseStep 3298151 = 4947227) B4947227
theorem B1954687 : Blo 1543469 1954687 := bstep (se 1 (by rfl) ⟨1466015, by rfl⟩ : syracuseStep 1954687 = 2932031) B2932031
theorem B2642815 : Blo 1543469 2642815 := bstep (se 1 (by rfl) ⟨1982111, by rfl⟩ : syracuseStep 2642815 = 3964223) B3964223
theorem B1545263 : Blo 1543469 1545263 := bstep (se 1 (by rfl) ⟨1158947, by rfl⟩ : syracuseStep 1545263 = 2317895) B2317895
theorem B1545447 : Blo 1543469 1545447 := bstep (se 1 (by rfl) ⟨1159085, by rfl⟩ : syracuseStep 1545447 = 2318171) B2318171
theorem B2315903 : Blo 1543469 2315903 := bstep (se 1 (by rfl) ⟨1736927, by rfl⟩ : syracuseStep 2315903 = 3473855) B3473855
theorem B11728637 : Blo 1543469 11728637 := bstep (se 3 (by rfl) ⟨2199119, by rfl⟩ : syracuseStep 11728637 = 4398239) B4398239
theorem B2316527 : Blo 1543469 2316527 := bstep (se 1 (by rfl) ⟨1737395, by rfl⟩ : syracuseStep 2316527 = 3474791) B3474791
theorem B22272317 : Blo 1543469 22272317 := bstep (se 3 (by rfl) ⟨4176059, by rfl⟩ : syracuseStep 22272317 = 8352119) B8352119
theorem B2317019 : Blo 1543469 2317019 := bstep (se 1 (by rfl) ⟨1737764, by rfl⟩ : syracuseStep 2317019 = 3475529) B3475529
theorem B14080999 : Blo 1543469 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B11721833 : Blo 1543469 11721833 := bstep (se 2 (by rfl) ⟨4395687, by rfl⟩ : syracuseStep 11721833 = 8791375) B8791375
theorem B2931871 : Blo 1543469 2931871 := bstep (se 1 (by rfl) ⟨2198903, by rfl⟩ : syracuseStep 2931871 = 4397807) B4397807
theorem B2317727 : Blo 1543469 2317727 := bstep (se 1 (by rfl) ⟨1738295, by rfl⟩ : syracuseStep 2317727 = 3476591) B3476591
theorem B3472937 : Blo 1543469 3472937 := bstep (se 2 (by rfl) ⟨1302351, by rfl⟩ : syracuseStep 3472937 = 2604703) B2604703
theorem B2317979 : Blo 1543469 2317979 := bstep (se 1 (by rfl) ⟨1738484, by rfl⟩ : syracuseStep 2317979 = 3476969) B3476969
theorem B3571739 : Blo 1543469 3571739 := bstep (se 1 (by rfl) ⟨2678804, by rfl⟩ : syracuseStep 3571739 = 5357609) B5357609
theorem B7823789 : Blo 1543469 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B2605567 : Blo 1543469 2605567 := bstep (se 1 (by rfl) ⟨1954175, by rfl⟩ : syracuseStep 2605567 = 3908351) B3908351
theorem B13378213 : Blo 1543469 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B2606249 : Blo 1543469 2606249 := bstep (se 2 (by rfl) ⟨977343, by rfl⟩ : syracuseStep 2606249 = 1954687) B1954687
theorem B3523753 : Blo 1543469 3523753 := bstep (se 2 (by rfl) ⟨1321407, by rfl⟩ : syracuseStep 3523753 = 2642815) B2642815
theorem B5211647 : Blo 1543469 5211647 := bstep (se 1 (by rfl) ⟨3908735, by rfl⟩ : syracuseStep 5211647 = 7817471) B7817471
theorem B3909161 : Blo 1543469 3909161 := bstep (se 2 (by rfl) ⟨1465935, by rfl⟩ : syracuseStep 3909161 = 2931871) B2931871
theorem B11733983 : Blo 1543469 11733983 := bstep (se 1 (by rfl) ⟨8800487, by rfl⟩ : syracuseStep 11733983 = 17600975) B17600975
theorem B3910751 : Blo 1543469 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B6597769 : Blo 1543469 6597769 := bstep (se 2 (by rfl) ⟨2474163, by rfl⟩ : syracuseStep 6597769 = 4948327) B4948327
theorem B2198767 : Blo 1543469 2198767 := bstep (se 1 (by rfl) ⟨1649075, by rfl⟩ : syracuseStep 2198767 = 3298151) B3298151
theorem B37563911 : Blo 1543469 37563911 := bstep (se 1 (by rfl) ⟨28172933, by rfl⟩ : syracuseStep 37563911 = 56345867) B56345867
theorem B5566121 : Blo 1543469 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B1543935 : Blo 1543469 1543935 := bstep (se 1 (by rfl) ⟨1157951, by rfl⟩ : syracuseStep 1543935 = 2315903) B2315903
theorem B7819091 : Blo 1543469 7819091 := bstep (se 1 (by rfl) ⟨5864318, by rfl⟩ : syracuseStep 7819091 = 11728637) B11728637
theorem B1544351 : Blo 1543469 1544351 := bstep (se 1 (by rfl) ⟨1158263, by rfl⟩ : syracuseStep 1544351 = 2316527) B2316527
theorem B14848211 : Blo 1543469 14848211 := bstep (se 1 (by rfl) ⟨11136158, by rfl⟩ : syracuseStep 14848211 = 22272317) B22272317
theorem B1544679 : Blo 1543469 1544679 := bstep (se 1 (by rfl) ⟨1158509, by rfl⟩ : syracuseStep 1544679 = 2317019) B2317019
theorem B1545151 : Blo 1543469 1545151 := bstep (se 1 (by rfl) ⟨1158863, by rfl⟩ : syracuseStep 1545151 = 2317727) B2317727
theorem B6263801 : Blo 1543469 6263801 := bstep (se 2 (by rfl) ⟨2348925, by rfl⟩ : syracuseStep 6263801 = 4697851) B4697851
theorem B2315291 : Blo 1543469 2315291 := bstep (se 1 (by rfl) ⟨1736468, by rfl⟩ : syracuseStep 2315291 = 3472937) B3472937
theorem B16692263 : Blo 1543469 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B1545319 : Blo 1543469 1545319 := bstep (se 1 (by rfl) ⟨1158989, by rfl⟩ : syracuseStep 1545319 = 2317979) B2317979
theorem B9901369 : Blo 1543469 9901369 := bstep (se 2 (by rfl) ⟨3713013, by rfl⟩ : syracuseStep 9901369 = 7426027) B7426027
theorem B7820711 : Blo 1543469 7820711 := bstep (se 1 (by rfl) ⟨5865533, by rfl⟩ : syracuseStep 7820711 = 11731067) B11731067
theorem B35674019 : Blo 1543469 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B18774665 : Blo 1543469 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B101587607 : Blo 1543469 101587607 := bstep (se 1 (by rfl) ⟨76190705, by rfl⟩ : syracuseStep 101587607 = 152381411) B152381411
theorem B2317031 : Blo 1543469 2317031 := bstep (se 1 (by rfl) ⟨1737773, by rfl⟩ : syracuseStep 2317031 = 3475547) B3475547
theorem B7814555 : Blo 1543469 7814555 := bstep (se 1 (by rfl) ⟨5860916, by rfl⟩ : syracuseStep 7814555 = 11721833) B11721833
theorem B8797733 : Blo 1543469 8797733 := bstep (se 4 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 8797733 = 1649575) B1649575
theorem B2317865 : Blo 1543469 2317865 := bstep (se 2 (by rfl) ⟨869199, by rfl⟩ : syracuseStep 2317865 = 1738399) B1738399
theorem B3474089 : Blo 1543469 3474089 := bstep (se 2 (by rfl) ⟨1302783, by rfl⟩ : syracuseStep 3474089 = 2605567) B2605567
theorem B1737499 : Blo 1543469 1737499 := bstep (se 1 (by rfl) ⟨1303124, by rfl⟩ : syracuseStep 1737499 = 2606249) B2606249
theorem B3474431 : Blo 1543469 3474431 := bstep (se 1 (by rfl) ⟨2605823, by rfl⟩ : syracuseStep 3474431 = 5211647) B5211647
theorem B2606107 : Blo 1543469 2606107 := bstep (se 1 (by rfl) ⟨1954580, by rfl⟩ : syracuseStep 2606107 = 3909161) B3909161
theorem B23782679 : Blo 1543469 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B67725071 : Blo 1543469 67725071 := bstep (se 1 (by rfl) ⟨50793803, by rfl⟩ : syracuseStep 67725071 = 101587607) B101587607
theorem B2607167 : Blo 1543469 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B5212727 : Blo 1543469 5212727 := bstep (se 1 (by rfl) ⟨3909545, by rfl⟩ : syracuseStep 5212727 = 7819091) B7819091
theorem B9898807 : Blo 1543469 9898807 := bstep (se 1 (by rfl) ⟨7424105, by rfl⟩ : syracuseStep 9898807 = 14848211) B14848211
theorem B1543527 : Blo 1543469 1543527 := bstep (se 1 (by rfl) ⟨1157645, by rfl⟩ : syracuseStep 1543527 = 2315291) B2315291
theorem B11128175 : Blo 1543469 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B17837617 : Blo 1543469 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B5213807 : Blo 1543469 5213807 := bstep (se 1 (by rfl) ⟨3910355, by rfl⟩ : syracuseStep 5213807 = 7820711) B7820711
theorem B4698337 : Blo 1543469 4698337 := bstep (se 2 (by rfl) ⟨1761876, by rfl⟩ : syracuseStep 4698337 = 3523753) B3523753
theorem B13201825 : Blo 1543469 13201825 := bstep (se 2 (by rfl) ⟨4950684, by rfl⟩ : syracuseStep 13201825 = 9901369) B9901369
theorem B1544687 : Blo 1543469 1544687 := bstep (se 1 (by rfl) ⟨1158515, by rfl⟩ : syracuseStep 1544687 = 2317031) B2317031
theorem B1545243 : Blo 1543469 1545243 := bstep (se 1 (by rfl) ⟨1158932, by rfl⟩ : syracuseStep 1545243 = 2317865) B2317865
theorem B2381159 : Blo 1543469 2381159 := bstep (se 1 (by rfl) ⟨1785869, by rfl⟩ : syracuseStep 2381159 = 3571739) B3571739
theorem B5215859 : Blo 1543469 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B4175867 : Blo 1543469 4175867 := bstep (se 1 (by rfl) ⟨3131900, by rfl⟩ : syracuseStep 4175867 = 6263801) B6263801
theorem B8797025 : Blo 1543469 8797025 := bstep (se 2 (by rfl) ⟨3298884, by rfl⟩ : syracuseStep 8797025 = 6597769) B6597769
theorem B2931689 : Blo 1543469 2931689 := bstep (se 2 (by rfl) ⟨1099383, by rfl⟩ : syracuseStep 2931689 = 2198767) B2198767
theorem B12516443 : Blo 1543469 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B7822655 : Blo 1543469 7822655 := bstep (se 1 (by rfl) ⟨5866991, by rfl⟩ : syracuseStep 7822655 = 11733983) B11733983
theorem B5209703 : Blo 1543469 5209703 := bstep (se 1 (by rfl) ⟨3907277, by rfl⟩ : syracuseStep 5209703 = 7814555) B7814555
theorem B25042607 : Blo 1543469 25042607 := bstep (se 1 (by rfl) ⟨18781955, by rfl⟩ : syracuseStep 25042607 = 37563911) B37563911
theorem B5865155 : Blo 1543469 5865155 := bstep (se 1 (by rfl) ⟨4398866, by rfl⟩ : syracuseStep 5865155 = 8797733) B8797733
theorem B3710747 : Blo 1543469 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B13198409 : Blo 1543469 13198409 := bstep (se 2 (by rfl) ⟨4949403, by rfl⟩ : syracuseStep 13198409 = 9898807) B9898807
theorem B3474809 : Blo 1543469 3474809 := bstep (se 2 (by rfl) ⟨1303053, by rfl⟩ : syracuseStep 3474809 = 2606107) B2606107
theorem B1738111 : Blo 1543469 1738111 := bstep (se 1 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 1738111 = 2607167) B2607167
theorem B3475151 : Blo 1543469 3475151 := bstep (se 1 (by rfl) ⟨2606363, by rfl⟩ : syracuseStep 3475151 = 5212727) B5212727
theorem B23783489 : Blo 1543469 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B3475871 : Blo 1543469 3475871 := bstep (se 1 (by rfl) ⟨2606903, by rfl⟩ : syracuseStep 3475871 = 5213807) B5213807
theorem B3910103 : Blo 1543469 3910103 := bstep (se 1 (by rfl) ⟨2932577, by rfl⟩ : syracuseStep 3910103 = 5865155) B5865155
theorem B15855119 : Blo 1543469 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B3477239 : Blo 1543469 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B45150047 : Blo 1543469 45150047 := bstep (se 1 (by rfl) ⟨33862535, by rfl⟩ : syracuseStep 45150047 = 67725071) B67725071
theorem B1954459 : Blo 1543469 1954459 := bstep (se 1 (by rfl) ⟨1465844, by rfl⟩ : syracuseStep 1954459 = 2931689) B2931689
theorem B8344295 : Blo 1543469 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B5215103 : Blo 1543469 5215103 := bstep (se 1 (by rfl) ⟨3911327, by rfl⟩ : syracuseStep 5215103 = 7822655) B7822655
theorem B7418783 : Blo 1543469 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B6264449 : Blo 1543469 6264449 := bstep (se 2 (by rfl) ⟨2349168, by rfl⟩ : syracuseStep 6264449 = 4698337) B4698337
theorem B2316059 : Blo 1543469 2316059 := bstep (se 1 (by rfl) ⟨1737044, by rfl⟩ : syracuseStep 2316059 = 3474089) B3474089
theorem B17602433 : Blo 1543469 17602433 := bstep (se 2 (by rfl) ⟨6600912, by rfl⟩ : syracuseStep 17602433 = 13201825) B13201825
theorem B2316287 : Blo 1543469 2316287 := bstep (se 1 (by rfl) ⟨1737215, by rfl⟩ : syracuseStep 2316287 = 3474431) B3474431
theorem B1587439 : Blo 1543469 1587439 := bstep (se 1 (by rfl) ⟨1190579, by rfl⟩ : syracuseStep 1587439 = 2381159) B2381159
theorem B2316665 : Blo 1543469 2316665 := bstep (se 2 (by rfl) ⟨868749, by rfl⟩ : syracuseStep 2316665 = 1737499) B1737499
theorem B2783911 : Blo 1543469 2783911 := bstep (se 1 (by rfl) ⟨2087933, by rfl⟩ : syracuseStep 2783911 = 4175867) B4175867
theorem B5864683 : Blo 1543469 5864683 := bstep (se 1 (by rfl) ⟨4398512, by rfl⟩ : syracuseStep 5864683 = 8797025) B8797025
theorem B3473135 : Blo 1543469 3473135 := bstep (se 1 (by rfl) ⟨2604851, by rfl⟩ : syracuseStep 3473135 = 5209703) B5209703
theorem B16695071 : Blo 1543469 16695071 := bstep (se 1 (by rfl) ⟨12521303, by rfl⟩ : syracuseStep 16695071 = 25042607) B25042607
theorem B2473831 : Blo 1543469 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B5562863 : Blo 1543469 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B8798939 : Blo 1543469 8798939 := bstep (se 1 (by rfl) ⟨6599204, by rfl⟩ : syracuseStep 8798939 = 13198409) B13198409
theorem B2605945 : Blo 1543469 2605945 := bstep (se 2 (by rfl) ⟨977229, by rfl⟩ : syracuseStep 2605945 = 1954459) B1954459
theorem B3711881 : Blo 1543469 3711881 := bstep (se 2 (by rfl) ⟨1391955, by rfl⟩ : syracuseStep 3711881 = 2783911) B2783911
theorem B2606735 : Blo 1543469 2606735 := bstep (se 1 (by rfl) ⟨1955051, by rfl⟩ : syracuseStep 2606735 = 3910103) B3910103
theorem B10570079 : Blo 1543469 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B30100031 : Blo 1543469 30100031 := bstep (se 1 (by rfl) ⟨22575023, by rfl⟩ : syracuseStep 30100031 = 45150047) B45150047
theorem B2116585 : Blo 1543469 2116585 := bstep (se 2 (by rfl) ⟨793719, by rfl⟩ : syracuseStep 2116585 = 1587439) B1587439
theorem B3476735 : Blo 1543469 3476735 := bstep (se 1 (by rfl) ⟨2607551, by rfl⟩ : syracuseStep 3476735 = 5215103) B5215103
theorem B1544039 : Blo 1543469 1544039 := bstep (se 1 (by rfl) ⟨1158029, by rfl⟩ : syracuseStep 1544039 = 2316059) B2316059
theorem B11734955 : Blo 1543469 11734955 := bstep (se 1 (by rfl) ⟨8801216, by rfl⟩ : syracuseStep 11734955 = 17602433) B17602433
theorem B1544191 : Blo 1543469 1544191 := bstep (se 1 (by rfl) ⟨1158143, by rfl⟩ : syracuseStep 1544191 = 2316287) B2316287
theorem B15855659 : Blo 1543469 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B1544443 : Blo 1543469 1544443 := bstep (se 1 (by rfl) ⟨1158332, by rfl⟩ : syracuseStep 1544443 = 2316665) B2316665
theorem B7819577 : Blo 1543469 7819577 := bstep (se 2 (by rfl) ⟨2932341, by rfl⟩ : syracuseStep 7819577 = 5864683) B5864683
theorem B3298441 : Blo 1543469 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B2315423 : Blo 1543469 2315423 := bstep (se 1 (by rfl) ⟨1736567, by rfl⟩ : syracuseStep 2315423 = 3473135) B3473135
theorem B11130047 : Blo 1543469 11130047 := bstep (se 1 (by rfl) ⟨8347535, by rfl⟩ : syracuseStep 11130047 = 16695071) B16695071
theorem B4945855 : Blo 1543469 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B2316539 : Blo 1543469 2316539 := bstep (se 1 (by rfl) ⟨1737404, by rfl⟩ : syracuseStep 2316539 = 3474809) B3474809
theorem B4176299 : Blo 1543469 4176299 := bstep (se 1 (by rfl) ⟨3132224, by rfl⟩ : syracuseStep 4176299 = 6264449) B6264449
theorem B2316767 : Blo 1543469 2316767 := bstep (se 1 (by rfl) ⟨1737575, by rfl⟩ : syracuseStep 2316767 = 3475151) B3475151
theorem B2317247 : Blo 1543469 2317247 := bstep (se 1 (by rfl) ⟨1737935, by rfl⟩ : syracuseStep 2317247 = 3475871) B3475871
theorem B2317481 : Blo 1543469 2317481 := bstep (se 2 (by rfl) ⟨869055, by rfl⟩ : syracuseStep 2317481 = 1738111) B1738111
theorem B2318159 : Blo 1543469 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B5865959 : Blo 1543469 5865959 := bstep (se 1 (by rfl) ⟨4399469, by rfl⟩ : syracuseStep 5865959 = 8798939) B8798939
theorem B2474587 : Blo 1543469 2474587 := bstep (se 1 (by rfl) ⟨1855940, by rfl⟩ : syracuseStep 2474587 = 3711881) B3711881
theorem B1737823 : Blo 1543469 1737823 := bstep (se 1 (by rfl) ⟨1303367, by rfl⟩ : syracuseStep 1737823 = 2606735) B2606735
theorem B3474593 : Blo 1543469 3474593 := bstep (se 2 (by rfl) ⟨1302972, by rfl⟩ : syracuseStep 3474593 = 2605945) B2605945
theorem B7046719 : Blo 1543469 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B10570439 : Blo 1543469 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B5213051 : Blo 1543469 5213051 := bstep (se 1 (by rfl) ⟨3909788, by rfl⟩ : syracuseStep 5213051 = 7819577) B7819577
theorem B1543615 : Blo 1543469 1543615 := bstep (se 1 (by rfl) ⟨1157711, by rfl⟩ : syracuseStep 1543615 = 2315423) B2315423
theorem B11136797 : Blo 1543469 11136797 := bstep (se 3 (by rfl) ⟨2088149, by rfl⟩ : syracuseStep 11136797 = 4176299) B4176299
theorem B2822113 : Blo 1543469 2822113 := bstep (se 2 (by rfl) ⟨1058292, by rfl⟩ : syracuseStep 2822113 = 2116585) B2116585
theorem B1544359 : Blo 1543469 1544359 := bstep (se 1 (by rfl) ⟨1158269, by rfl⟩ : syracuseStep 1544359 = 2316539) B2316539
theorem B1544511 : Blo 1543469 1544511 := bstep (se 1 (by rfl) ⟨1158383, by rfl⟩ : syracuseStep 1544511 = 2316767) B2316767
theorem B20066687 : Blo 1543469 20066687 := bstep (se 1 (by rfl) ⟨15050015, by rfl⟩ : syracuseStep 20066687 = 30100031) B30100031
theorem B1544831 : Blo 1543469 1544831 := bstep (se 1 (by rfl) ⟨1158623, by rfl⟩ : syracuseStep 1544831 = 2317247) B2317247
theorem B1544987 : Blo 1543469 1544987 := bstep (se 1 (by rfl) ⟨1158740, by rfl⟩ : syracuseStep 1544987 = 2317481) B2317481
theorem B1545439 : Blo 1543469 1545439 := bstep (se 1 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 1545439 = 2318159) B2318159
theorem B3708575 : Blo 1543469 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B7420031 : Blo 1543469 7420031 := bstep (se 1 (by rfl) ⟨5565023, by rfl⟩ : syracuseStep 7420031 = 11130047) B11130047
theorem B4397921 : Blo 1543469 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B2317823 : Blo 1543469 2317823 := bstep (se 1 (by rfl) ⟨1738367, by rfl⟩ : syracuseStep 2317823 = 3476735) B3476735
theorem B6594473 : Blo 1543469 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B7823303 : Blo 1543469 7823303 := bstep (se 1 (by rfl) ⟨5867477, by rfl⟩ : syracuseStep 7823303 = 11734955) B11734955
theorem B13377791 : Blo 1543469 13377791 := bstep (se 1 (by rfl) ⟨10033343, by rfl⟩ : syracuseStep 13377791 = 20066687) B20066687
theorem B7046959 : Blo 1543469 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B3475367 : Blo 1543469 3475367 := bstep (se 1 (by rfl) ⟨2606525, by rfl⟩ : syracuseStep 3475367 = 5213051) B5213051
theorem B7424531 : Blo 1543469 7424531 := bstep (se 1 (by rfl) ⟨5568398, by rfl⟩ : syracuseStep 7424531 = 11136797) B11136797
theorem B3762817 : Blo 1543469 3762817 := bstep (se 2 (by rfl) ⟨1411056, by rfl⟩ : syracuseStep 3762817 = 2822113) B2822113
theorem B3910639 : Blo 1543469 3910639 := bstep (se 1 (by rfl) ⟨2932979, by rfl⟩ : syracuseStep 3910639 = 5865959) B5865959
theorem B1545215 : Blo 1543469 1545215 := bstep (se 1 (by rfl) ⟨1158911, by rfl⟩ : syracuseStep 1545215 = 2317823) B2317823
theorem B4396315 : Blo 1543469 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B5215535 : Blo 1543469 5215535 := bstep (se 1 (by rfl) ⟨3911651, by rfl⟩ : syracuseStep 5215535 = 7823303) B7823303
theorem B37582501 : Blo 1543469 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B2316395 : Blo 1543469 2316395 := bstep (se 1 (by rfl) ⟨1737296, by rfl⟩ : syracuseStep 2316395 = 3474593) B3474593
theorem B3299449 : Blo 1543469 3299449 := bstep (se 2 (by rfl) ⟨1237293, by rfl⟩ : syracuseStep 3299449 = 2474587) B2474587
theorem B2472383 : Blo 1543469 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B4946687 : Blo 1543469 4946687 := bstep (se 1 (by rfl) ⟨3710015, by rfl⟩ : syracuseStep 4946687 = 7420031) B7420031
theorem B2317097 : Blo 1543469 2317097 := bstep (se 2 (by rfl) ⟨868911, by rfl⟩ : syracuseStep 2317097 = 1737823) B1737823
theorem B2931947 : Blo 1543469 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B4399265 : Blo 1543469 4399265 := bstep (se 2 (by rfl) ⟨1649724, by rfl⟩ : syracuseStep 4399265 = 3299449) B3299449
theorem B4949687 : Blo 1543469 4949687 := bstep (se 1 (by rfl) ⟨3712265, by rfl⟩ : syracuseStep 4949687 = 7424531) B7424531
theorem B3477023 : Blo 1543469 3477023 := bstep (se 1 (by rfl) ⟨2607767, by rfl⟩ : syracuseStep 3477023 = 5215535) B5215535
theorem B5214185 : Blo 1543469 5214185 := bstep (se 2 (by rfl) ⟨1955319, by rfl⟩ : syracuseStep 5214185 = 3910639) B3910639
theorem B1544263 : Blo 1543469 1544263 := bstep (se 1 (by rfl) ⟨1158197, by rfl⟩ : syracuseStep 1544263 = 2316395) B2316395
theorem B5861753 : Blo 1543469 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B3297791 : Blo 1543469 3297791 := bstep (se 1 (by rfl) ⟨2473343, by rfl⟩ : syracuseStep 3297791 = 4946687) B4946687
theorem B1544731 : Blo 1543469 1544731 := bstep (se 1 (by rfl) ⟨1158548, by rfl⟩ : syracuseStep 1544731 = 2317097) B2317097
theorem B1954631 : Blo 1543469 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B8918527 : Blo 1543469 8918527 := bstep (se 1 (by rfl) ⟨6688895, by rfl⟩ : syracuseStep 8918527 = 13377791) B13377791
theorem B20068357 : Blo 1543469 20068357 := bstep (se 4 (by rfl) ⟨1881408, by rfl⟩ : syracuseStep 20068357 = 3762817) B3762817
theorem B6593021 : Blo 1543469 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B2316911 : Blo 1543469 2316911 := bstep (se 1 (by rfl) ⟨1737683, by rfl⟩ : syracuseStep 2316911 = 3475367) B3475367
theorem B50110001 : Blo 1543469 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B9395945 : Blo 1543469 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B2932843 : Blo 1543469 2932843 := bstep (se 1 (by rfl) ⟨2199632, by rfl⟩ : syracuseStep 2932843 = 4399265) B4399265
theorem B3907835 : Blo 1543469 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B5212349 : Blo 1543469 5212349 := bstep (se 3 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 5212349 = 1954631) B1954631
theorem B3476123 : Blo 1543469 3476123 := bstep (se 1 (by rfl) ⟨2607092, by rfl⟩ : syracuseStep 3476123 = 5214185) B5214185
theorem B26757809 : Blo 1543469 26757809 := bstep (se 2 (by rfl) ⟨10034178, by rfl⟩ : syracuseStep 26757809 = 20068357) B20068357
theorem B8794109 : Blo 1543469 8794109 := bstep (se 3 (by rfl) ⟨1648895, by rfl⟩ : syracuseStep 8794109 = 3297791) B3297791
theorem B4395347 : Blo 1543469 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B1544607 : Blo 1543469 1544607 := bstep (se 1 (by rfl) ⟨1158455, by rfl⟩ : syracuseStep 1544607 = 2316911) B2316911
theorem B11891369 : Blo 1543469 11891369 := bstep (se 2 (by rfl) ⟨4459263, by rfl⟩ : syracuseStep 11891369 = 8918527) B8918527
theorem B6263963 : Blo 1543469 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B3299791 : Blo 1543469 3299791 := bstep (se 1 (by rfl) ⟨2474843, by rfl⟩ : syracuseStep 3299791 = 4949687) B4949687
theorem B2318015 : Blo 1543469 2318015 := bstep (se 1 (by rfl) ⟨1738511, by rfl⟩ : syracuseStep 2318015 = 3477023) B3477023
theorem B33406667 : Blo 1543469 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B2605223 : Blo 1543469 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B4399721 : Blo 1543469 4399721 := bstep (se 2 (by rfl) ⟨1649895, by rfl⟩ : syracuseStep 4399721 = 3299791) B3299791
theorem B3474899 : Blo 1543469 3474899 := bstep (se 1 (by rfl) ⟨2606174, by rfl⟩ : syracuseStep 3474899 = 5212349) B5212349
theorem B3910457 : Blo 1543469 3910457 := bstep (se 2 (by rfl) ⟨1466421, by rfl⟩ : syracuseStep 3910457 = 2932843) B2932843
theorem B17838539 : Blo 1543469 17838539 := bstep (se 1 (by rfl) ⟨13378904, by rfl⟩ : syracuseStep 17838539 = 26757809) B26757809
theorem B1545343 : Blo 1543469 1545343 := bstep (se 1 (by rfl) ⟨1159007, by rfl⟩ : syracuseStep 1545343 = 2318015) B2318015
theorem B22271111 : Blo 1543469 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B5862739 : Blo 1543469 5862739 := bstep (se 1 (by rfl) ⟨4397054, by rfl⟩ : syracuseStep 5862739 = 8794109) B8794109
theorem B2930231 : Blo 1543469 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B7927579 : Blo 1543469 7927579 := bstep (se 1 (by rfl) ⟨5945684, by rfl⟩ : syracuseStep 7927579 = 11891369) B11891369
theorem B4175975 : Blo 1543469 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B2317415 : Blo 1543469 2317415 := bstep (se 1 (by rfl) ⟨1738061, by rfl⟩ : syracuseStep 2317415 = 3476123) B3476123
theorem B1736815 : Blo 1543469 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B2933147 : Blo 1543469 2933147 := bstep (se 1 (by rfl) ⟨2199860, by rfl⟩ : syracuseStep 2933147 = 4399721) B4399721
theorem B7816985 : Blo 1543469 7816985 := bstep (se 2 (by rfl) ⟨2931369, by rfl⟩ : syracuseStep 7816985 = 5862739) B5862739
theorem B2606971 : Blo 1543469 2606971 := bstep (se 1 (by rfl) ⟨1955228, by rfl⟩ : syracuseStep 2606971 = 3910457) B3910457
theorem B10570105 : Blo 1543469 10570105 := bstep (se 2 (by rfl) ⟨3963789, by rfl⟩ : syracuseStep 10570105 = 7927579) B7927579
theorem B14847407 : Blo 1543469 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B1953487 : Blo 1543469 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B1544943 : Blo 1543469 1544943 := bstep (se 1 (by rfl) ⟨1158707, by rfl⟩ : syracuseStep 1544943 = 2317415) B2317415
theorem B11892359 : Blo 1543469 11892359 := bstep (se 1 (by rfl) ⟨8919269, by rfl⟩ : syracuseStep 11892359 = 17838539) B17838539
theorem B2316599 : Blo 1543469 2316599 := bstep (se 1 (by rfl) ⟨1737449, by rfl⟩ : syracuseStep 2316599 = 3474899) B3474899
theorem B2783983 : Blo 1543469 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B3711977 : Blo 1543469 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B5211323 : Blo 1543469 5211323 := bstep (se 1 (by rfl) ⟨3908492, by rfl⟩ : syracuseStep 5211323 = 7816985) B7816985
theorem B31712957 : Blo 1543469 31712957 := bstep (se 3 (by rfl) ⟨5946179, by rfl⟩ : syracuseStep 31712957 = 11892359) B11892359
theorem B9898271 : Blo 1543469 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B3475961 : Blo 1543469 3475961 := bstep (se 2 (by rfl) ⟨1303485, by rfl⟩ : syracuseStep 3475961 = 2606971) B2606971
theorem B14093473 : Blo 1543469 14093473 := bstep (se 2 (by rfl) ⟨5285052, by rfl⟩ : syracuseStep 14093473 = 10570105) B10570105
theorem B1544399 : Blo 1543469 1544399 := bstep (se 1 (by rfl) ⟨1158299, by rfl⟩ : syracuseStep 1544399 = 2316599) B2316599
theorem B2315753 : Blo 1543469 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B1955431 : Blo 1543469 1955431 := bstep (se 1 (by rfl) ⟨1466573, by rfl⟩ : syracuseStep 1955431 = 2933147) B2933147
theorem B2604649 : Blo 1543469 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B2474651 : Blo 1543469 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B3474215 : Blo 1543469 3474215 := bstep (se 1 (by rfl) ⟨2605661, by rfl⟩ : syracuseStep 3474215 = 5211323) B5211323
theorem B2607241 : Blo 1543469 2607241 := bstep (se 2 (by rfl) ⟨977715, by rfl⟩ : syracuseStep 2607241 = 1955431) B1955431
theorem B1543835 : Blo 1543469 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B6598847 : Blo 1543469 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B21141971 : Blo 1543469 21141971 := bstep (se 1 (by rfl) ⟨15856478, by rfl⟩ : syracuseStep 21141971 = 31712957) B31712957
theorem B18791297 : Blo 1543469 18791297 := bstep (se 2 (by rfl) ⟨7046736, by rfl⟩ : syracuseStep 18791297 = 14093473) B14093473
theorem B2317307 : Blo 1543469 2317307 := bstep (se 1 (by rfl) ⟨1737980, by rfl⟩ : syracuseStep 2317307 = 3475961) B3475961
theorem B3472865 : Blo 1543469 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B4399231 : Blo 1543469 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B12527531 : Blo 1543469 12527531 := bstep (se 1 (by rfl) ⟨9395648, by rfl⟩ : syracuseStep 12527531 = 18791297) B18791297
theorem B3476321 : Blo 1543469 3476321 := bstep (se 2 (by rfl) ⟨1303620, by rfl⟩ : syracuseStep 3476321 = 2607241) B2607241
theorem B14094647 : Blo 1543469 14094647 := bstep (se 1 (by rfl) ⟨10570985, by rfl⟩ : syracuseStep 14094647 = 21141971) B21141971
theorem B6599069 : Blo 1543469 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B1544871 : Blo 1543469 1544871 := bstep (se 1 (by rfl) ⟨1158653, by rfl⟩ : syracuseStep 1544871 = 2317307) B2317307
theorem B2315243 : Blo 1543469 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B2316143 : Blo 1543469 2316143 := bstep (se 1 (by rfl) ⟨1737107, by rfl⟩ : syracuseStep 2316143 = 3474215) B3474215
theorem B5865641 : Blo 1543469 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B9396431 : Blo 1543469 9396431 := bstep (se 1 (by rfl) ⟨7047323, by rfl⟩ : syracuseStep 9396431 = 14094647) B14094647
theorem B4399379 : Blo 1543469 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B1543495 : Blo 1543469 1543495 := bstep (se 1 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 1543495 = 2315243) B2315243
theorem B1544095 : Blo 1543469 1544095 := bstep (se 1 (by rfl) ⟨1158071, by rfl⟩ : syracuseStep 1544095 = 2316143) B2316143
theorem B8351687 : Blo 1543469 8351687 := bstep (se 1 (by rfl) ⟨6263765, by rfl⟩ : syracuseStep 8351687 = 12527531) B12527531
theorem B2317547 : Blo 1543469 2317547 := bstep (se 1 (by rfl) ⟨1738160, by rfl⟩ : syracuseStep 2317547 = 3476321) B3476321
theorem B2932919 : Blo 1543469 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B3910427 : Blo 1543469 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B1545031 : Blo 1543469 1545031 := bstep (se 1 (by rfl) ⟨1158773, by rfl⟩ : syracuseStep 1545031 = 2317547) B2317547
theorem B5567791 : Blo 1543469 5567791 := bstep (se 1 (by rfl) ⟨4175843, by rfl⟩ : syracuseStep 5567791 = 8351687) B8351687
theorem B6264287 : Blo 1543469 6264287 := bstep (se 1 (by rfl) ⟨4698215, by rfl⟩ : syracuseStep 6264287 = 9396431) B9396431
theorem B7423721 : Blo 1543469 7423721 := bstep (se 2 (by rfl) ⟨2783895, by rfl⟩ : syracuseStep 7423721 = 5567791) B5567791
theorem B2606951 : Blo 1543469 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B1955279 : Blo 1543469 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B4176191 : Blo 1543469 4176191 := bstep (se 1 (by rfl) ⟨3132143, by rfl⟩ : syracuseStep 4176191 = 6264287) B6264287
theorem B4949147 : Blo 1543469 4949147 := bstep (se 1 (by rfl) ⟨3711860, by rfl⟩ : syracuseStep 4949147 = 7423721) B7423721
theorem B1737967 : Blo 1543469 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B5214077 : Blo 1543469 5214077 := bstep (se 3 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 5214077 = 1955279) B1955279
theorem B2784127 : Blo 1543469 2784127 := bstep (se 1 (by rfl) ⟨2088095, by rfl⟩ : syracuseStep 2784127 = 4176191) B4176191
theorem B13197725 : Blo 1543469 13197725 := bstep (se 3 (by rfl) ⟨2474573, by rfl⟩ : syracuseStep 13197725 = 4949147) B4949147
theorem B3712169 : Blo 1543469 3712169 := bstep (se 2 (by rfl) ⟨1392063, by rfl⟩ : syracuseStep 3712169 = 2784127) B2784127
theorem B3476051 : Blo 1543469 3476051 := bstep (se 1 (by rfl) ⟨2607038, by rfl⟩ : syracuseStep 3476051 = 5214077) B5214077
theorem B2317289 : Blo 1543469 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B8798483 : Blo 1543469 8798483 := bstep (se 1 (by rfl) ⟨6598862, by rfl⟩ : syracuseStep 8798483 = 13197725) B13197725
theorem B2474779 : Blo 1543469 2474779 := bstep (se 1 (by rfl) ⟨1856084, by rfl⟩ : syracuseStep 2474779 = 3712169) B3712169
theorem B1544859 : Blo 1543469 1544859 := bstep (se 1 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 1544859 = 2317289) B2317289
theorem B2317367 : Blo 1543469 2317367 := bstep (se 1 (by rfl) ⟨1738025, by rfl⟩ : syracuseStep 2317367 = 3476051) B3476051
theorem B5865655 : Blo 1543469 5865655 := bstep (se 1 (by rfl) ⟨4399241, by rfl⟩ : syracuseStep 5865655 = 8798483) B8798483
theorem B1544911 : Blo 1543469 1544911 := bstep (se 1 (by rfl) ⟨1158683, by rfl⟩ : syracuseStep 1544911 = 2317367) B2317367
theorem B3299705 : Blo 1543469 3299705 := bstep (se 2 (by rfl) ⟨1237389, by rfl⟩ : syracuseStep 3299705 = 2474779) B2474779
theorem B2199803 : Blo 1543469 2199803 := bstep (se 1 (by rfl) ⟨1649852, by rfl⟩ : syracuseStep 2199803 = 3299705) B3299705
theorem B7820873 : Blo 1543469 7820873 := bstep (se 2 (by rfl) ⟨2932827, by rfl⟩ : syracuseStep 7820873 = 5865655) B5865655
theorem B5866141 : Blo 1543469 5866141 := bstep (se 3 (by rfl) ⟨1099901, by rfl⟩ : syracuseStep 5866141 = 2199803) B2199803
theorem B5213915 : Blo 1543469 5213915 := bstep (se 1 (by rfl) ⟨3910436, by rfl⟩ : syracuseStep 5213915 = 7820873) B7820873
theorem B3475943 : Blo 1543469 3475943 := bstep (se 1 (by rfl) ⟨2606957, by rfl⟩ : syracuseStep 3475943 = 5213915) B5213915
theorem B7821521 : Blo 1543469 7821521 := bstep (se 2 (by rfl) ⟨2933070, by rfl⟩ : syracuseStep 7821521 = 5866141) B5866141
theorem B5214347 : Blo 1543469 5214347 := bstep (se 1 (by rfl) ⟨3910760, by rfl⟩ : syracuseStep 5214347 = 7821521) B7821521
theorem B2317295 : Blo 1543469 2317295 := bstep (se 1 (by rfl) ⟨1737971, by rfl⟩ : syracuseStep 2317295 = 3475943) B3475943
theorem B3476231 : Blo 1543469 3476231 := bstep (se 1 (by rfl) ⟨2607173, by rfl⟩ : syracuseStep 3476231 = 5214347) B5214347
theorem B1544863 : Blo 1543469 1544863 := bstep (se 1 (by rfl) ⟨1158647, by rfl⟩ : syracuseStep 1544863 = 2317295) B2317295
theorem B2317487 : Blo 1543469 2317487 := bstep (se 1 (by rfl) ⟨1738115, by rfl⟩ : syracuseStep 2317487 = 3476231) B3476231
theorem B1544991 : Blo 1543469 1544991 := bstep (se 1 (by rfl) ⟨1158743, by rfl⟩ : syracuseStep 1544991 = 2317487) B2317487

theorem C0 (j : ℕ) (h1 : 385867 ≤ j) (h2 : j ≤ 386366) : Blo 1543469 (4 * j + 3) := by
  interval_cases j
  · exact B1543471
  · exact B1543475
  · exact B1543479
  · exact B1543483
  · exact B1543487
  · exact B1543491
  · exact B1543495
  · exact B1543499
  · exact B1543503
  · exact B1543507
  · exact B1543511
  · exact B1543515
  · exact B1543519
  · exact B1543523
  · exact B1543527
  · exact B1543531
  · exact B1543535
  · exact B1543539
  · exact B1543543
  · exact B1543547
  · exact B1543551
  · exact B1543555
  · exact B1543559
  · exact B1543563
  · exact B1543567
  · exact B1543571
  · exact B1543575
  · exact B1543579
  · exact B1543583
  · exact B1543587
  · exact B1543591
  · exact B1543595
  · exact B1543599
  · exact B1543603
  · exact B1543607
  · exact B1543611
  · exact B1543615
  · exact B1543619
  · exact B1543623
  · exact B1543627
  · exact B1543631
  · exact B1543635
  · exact B1543639
  · exact B1543643
  · exact B1543647
  · exact B1543651
  · exact B1543655
  · exact B1543659
  · exact B1543663
  · exact B1543667
  · exact B1543671
  · exact B1543675
  · exact B1543679
  · exact B1543683
  · exact B1543687
  · exact B1543691
  · exact B1543695
  · exact B1543699
  · exact B1543703
  · exact B1543707
  · exact B1543711
  · exact B1543715
  · exact B1543719
  · exact B1543723
  · exact B1543727
  · exact B1543731
  · exact B1543735
  · exact B1543739
  · exact B1543743
  · exact B1543747
  · exact B1543751
  · exact B1543755
  · exact B1543759
  · exact B1543763
  · exact B1543767
  · exact B1543771
  · exact B1543775
  · exact B1543779
  · exact B1543783
  · exact B1543787
  · exact B1543791
  · exact B1543795
  · exact B1543799
  · exact B1543803
  · exact B1543807
  · exact B1543811
  · exact B1543815
  · exact B1543819
  · exact B1543823
  · exact B1543827
  · exact B1543831
  · exact B1543835
  · exact B1543839
  · exact B1543843
  · exact B1543847
  · exact B1543851
  · exact B1543855
  · exact B1543859
  · exact B1543863
  · exact B1543867
  · exact B1543871
  · exact B1543875
  · exact B1543879
  · exact B1543883
  · exact B1543887
  · exact B1543891
  · exact B1543895
  · exact B1543899
  · exact B1543903
  · exact B1543907
  · exact B1543911
  · exact B1543915
  · exact B1543919
  · exact B1543923
  · exact B1543927
  · exact B1543931
  · exact B1543935
  · exact B1543939
  · exact B1543943
  · exact B1543947
  · exact B1543951
  · exact B1543955
  · exact B1543959
  · exact B1543963
  · exact B1543967
  · exact B1543971
  · exact B1543975
  · exact B1543979
  · exact B1543983
  · exact B1543987
  · exact B1543991
  · exact B1543995
  · exact B1543999
  · exact B1544003
  · exact B1544007
  · exact B1544011
  · exact B1544015
  · exact B1544019
  · exact B1544023
  · exact B1544027
  · exact B1544031
  · exact B1544035
  · exact B1544039
  · exact B1544043
  · exact B1544047
  · exact B1544051
  · exact B1544055
  · exact B1544059
  · exact B1544063
  · exact B1544067
  · exact B1544071
  · exact B1544075
  · exact B1544079
  · exact B1544083
  · exact B1544087
  · exact B1544091
  · exact B1544095
  · exact B1544099
  · exact B1544103
  · exact B1544107
  · exact B1544111
  · exact B1544115
  · exact B1544119
  · exact B1544123
  · exact B1544127
  · exact B1544131
  · exact B1544135
  · exact B1544139
  · exact B1544143
  · exact B1544147
  · exact B1544151
  · exact B1544155
  · exact B1544159
  · exact B1544163
  · exact B1544167
  · exact B1544171
  · exact B1544175
  · exact B1544179
  · exact B1544183
  · exact B1544187
  · exact B1544191
  · exact B1544195
  · exact B1544199
  · exact B1544203
  · exact B1544207
  · exact B1544211
  · exact B1544215
  · exact B1544219
  · exact B1544223
  · exact B1544227
  · exact B1544231
  · exact B1544235
  · exact B1544239
  · exact B1544243
  · exact B1544247
  · exact B1544251
  · exact B1544255
  · exact B1544259
  · exact B1544263
  · exact B1544267
  · exact B1544271
  · exact B1544275
  · exact B1544279
  · exact B1544283
  · exact B1544287
  · exact B1544291
  · exact B1544295
  · exact B1544299
  · exact B1544303
  · exact B1544307
  · exact B1544311
  · exact B1544315
  · exact B1544319
  · exact B1544323
  · exact B1544327
  · exact B1544331
  · exact B1544335
  · exact B1544339
  · exact B1544343
  · exact B1544347
  · exact B1544351
  · exact B1544355
  · exact B1544359
  · exact B1544363
  · exact B1544367
  · exact B1544371
  · exact B1544375
  · exact B1544379
  · exact B1544383
  · exact B1544387
  · exact B1544391
  · exact B1544395
  · exact B1544399
  · exact B1544403
  · exact B1544407
  · exact B1544411
  · exact B1544415
  · exact B1544419
  · exact B1544423
  · exact B1544427
  · exact B1544431
  · exact B1544435
  · exact B1544439
  · exact B1544443
  · exact B1544447
  · exact B1544451
  · exact B1544455
  · exact B1544459
  · exact B1544463
  · exact B1544467
  · exact B1544471
  · exact B1544475
  · exact B1544479
  · exact B1544483
  · exact B1544487
  · exact B1544491
  · exact B1544495
  · exact B1544499
  · exact B1544503
  · exact B1544507
  · exact B1544511
  · exact B1544515
  · exact B1544519
  · exact B1544523
  · exact B1544527
  · exact B1544531
  · exact B1544535
  · exact B1544539
  · exact B1544543
  · exact B1544547
  · exact B1544551
  · exact B1544555
  · exact B1544559
  · exact B1544563
  · exact B1544567
  · exact B1544571
  · exact B1544575
  · exact B1544579
  · exact B1544583
  · exact B1544587
  · exact B1544591
  · exact B1544595
  · exact B1544599
  · exact B1544603
  · exact B1544607
  · exact B1544611
  · exact B1544615
  · exact B1544619
  · exact B1544623
  · exact B1544627
  · exact B1544631
  · exact B1544635
  · exact B1544639
  · exact B1544643
  · exact B1544647
  · exact B1544651
  · exact B1544655
  · exact B1544659
  · exact B1544663
  · exact B1544667
  · exact B1544671
  · exact B1544675
  · exact B1544679
  · exact B1544683
  · exact B1544687
  · exact B1544691
  · exact B1544695
  · exact B1544699
  · exact B1544703
  · exact B1544707
  · exact B1544711
  · exact B1544715
  · exact B1544719
  · exact B1544723
  · exact B1544727
  · exact B1544731
  · exact B1544735
  · exact B1544739
  · exact B1544743
  · exact B1544747
  · exact B1544751
  · exact B1544755
  · exact B1544759
  · exact B1544763
  · exact B1544767
  · exact B1544771
  · exact B1544775
  · exact B1544779
  · exact B1544783
  · exact B1544787
  · exact B1544791
  · exact B1544795
  · exact B1544799
  · exact B1544803
  · exact B1544807
  · exact B1544811
  · exact B1544815
  · exact B1544819
  · exact B1544823
  · exact B1544827
  · exact B1544831
  · exact B1544835
  · exact B1544839
  · exact B1544843
  · exact B1544847
  · exact B1544851
  · exact B1544855
  · exact B1544859
  · exact B1544863
  · exact B1544867
  · exact B1544871
  · exact B1544875
  · exact B1544879
  · exact B1544883
  · exact B1544887
  · exact B1544891
  · exact B1544895
  · exact B1544899
  · exact B1544903
  · exact B1544907
  · exact B1544911
  · exact B1544915
  · exact B1544919
  · exact B1544923
  · exact B1544927
  · exact B1544931
  · exact B1544935
  · exact B1544939
  · exact B1544943
  · exact B1544947
  · exact B1544951
  · exact B1544955
  · exact B1544959
  · exact B1544963
  · exact B1544967
  · exact B1544971
  · exact B1544975
  · exact B1544979
  · exact B1544983
  · exact B1544987
  · exact B1544991
  · exact B1544995
  · exact B1544999
  · exact B1545003
  · exact B1545007
  · exact B1545011
  · exact B1545015
  · exact B1545019
  · exact B1545023
  · exact B1545027
  · exact B1545031
  · exact B1545035
  · exact B1545039
  · exact B1545043
  · exact B1545047
  · exact B1545051
  · exact B1545055
  · exact B1545059
  · exact B1545063
  · exact B1545067
  · exact B1545071
  · exact B1545075
  · exact B1545079
  · exact B1545083
  · exact B1545087
  · exact B1545091
  · exact B1545095
  · exact B1545099
  · exact B1545103
  · exact B1545107
  · exact B1545111
  · exact B1545115
  · exact B1545119
  · exact B1545123
  · exact B1545127
  · exact B1545131
  · exact B1545135
  · exact B1545139
  · exact B1545143
  · exact B1545147
  · exact B1545151
  · exact B1545155
  · exact B1545159
  · exact B1545163
  · exact B1545167
  · exact B1545171
  · exact B1545175
  · exact B1545179
  · exact B1545183
  · exact B1545187
  · exact B1545191
  · exact B1545195
  · exact B1545199
  · exact B1545203
  · exact B1545207
  · exact B1545211
  · exact B1545215
  · exact B1545219
  · exact B1545223
  · exact B1545227
  · exact B1545231
  · exact B1545235
  · exact B1545239
  · exact B1545243
  · exact B1545247
  · exact B1545251
  · exact B1545255
  · exact B1545259
  · exact B1545263
  · exact B1545267
  · exact B1545271
  · exact B1545275
  · exact B1545279
  · exact B1545283
  · exact B1545287
  · exact B1545291
  · exact B1545295
  · exact B1545299
  · exact B1545303
  · exact B1545307
  · exact B1545311
  · exact B1545315
  · exact B1545319
  · exact B1545323
  · exact B1545327
  · exact B1545331
  · exact B1545335
  · exact B1545339
  · exact B1545343
  · exact B1545347
  · exact B1545351
  · exact B1545355
  · exact B1545359
  · exact B1545363
  · exact B1545367
  · exact B1545371
  · exact B1545375
  · exact B1545379
  · exact B1545383
  · exact B1545387
  · exact B1545391
  · exact B1545395
  · exact B1545399
  · exact B1545403
  · exact B1545407
  · exact B1545411
  · exact B1545415
  · exact B1545419
  · exact B1545423
  · exact B1545427
  · exact B1545431
  · exact B1545435
  · exact B1545439
  · exact B1545443
  · exact B1545447
  · exact B1545451
  · exact B1545455
  · exact B1545459
  · exact B1545463
  · exact B1545467

theorem solution (m : ℕ) (hlo : 1543469 ≤ m) (hhi : m ≤ 1545469) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 385867 ≤ j := by omega
    have hj2 : j ≤ 386366 := by omega
    have hb : Blo 1543469 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
