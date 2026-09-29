-- Prove2me | solution 1 for syracuse_descends_range_1028606_1032606
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:21.72585+00:00
-- url     : https://prove2.me/submissions/77b768bf-6658-4734-a1b4-44c4d34e5b71

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


theorem B1736741 : Blo 1028606 1736741 := bbase (se 4 (by rfl) ⟨162819, by rfl⟩ : syracuseStep 1736741 = 325639) (by norm_num)
theorem B1736869 : Blo 1028606 1736869 := bbase (se 4 (by rfl) ⟨162831, by rfl⟩ : syracuseStep 1736869 = 325663) (by norm_num)
theorem B1736957 : Blo 1028606 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B5210405 : Blo 1028606 5210405 := bbase (se 4 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 5210405 = 976951) (by norm_num)
theorem B3473765 : Blo 1028606 3473765 := bbase (se 4 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 3473765 = 651331) (by norm_num)
theorem B1737085 : Blo 1028606 1737085 := bbase (se 3 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 1737085 = 651407) (by norm_num)
theorem B4456885 : Blo 1028606 4456885 := bbase (se 5 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 4456885 = 417833) (by norm_num)
theorem B1737173 : Blo 1028606 1737173 := bbase (se 7 (by rfl) ⟨20357, by rfl⟩ : syracuseStep 1737173 = 40715) (by norm_num)
theorem B1737301 : Blo 1028606 1737301 := bbase (se 8 (by rfl) ⟨10179, by rfl⟩ : syracuseStep 1737301 = 20359) (by norm_num)
theorem B1737389 : Blo 1028606 1737389 := bbase (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) (by norm_num)
theorem B3965669 : Blo 1028606 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B3474197 : Blo 1028606 3474197 := bbase (se 6 (by rfl) ⟨81426, by rfl⟩ : syracuseStep 3474197 = 162853) (by norm_num)
theorem B1737517 : Blo 1028606 1737517 := bbase (se 3 (by rfl) ⟨325784, by rfl⟩ : syracuseStep 1737517 = 651569) (by norm_num)
theorem B1737605 : Blo 1028606 1737605 := bbase (se 4 (by rfl) ⟨162900, by rfl⟩ : syracuseStep 1737605 = 325801) (by norm_num)
theorem B2786197 : Blo 1028606 2786197 := bbase (se 6 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 2786197 = 130603) (by norm_num)
theorem B1737733 : Blo 1028606 1737733 := bbase (se 4 (by rfl) ⟨162912, by rfl⟩ : syracuseStep 1737733 = 325825) (by norm_num)
theorem B3965957 : Blo 1028606 3965957 := bbase (se 4 (by rfl) ⟨371808, by rfl⟩ : syracuseStep 3965957 = 743617) (by norm_num)
theorem B1737821 : Blo 1028606 1737821 := bbase (se 3 (by rfl) ⟨325841, by rfl⟩ : syracuseStep 1737821 = 651683) (by norm_num)
theorem B3474629 : Blo 1028606 3474629 := bbase (se 4 (by rfl) ⟨325746, by rfl⟩ : syracuseStep 3474629 = 651493) (by norm_num)
theorem B1737949 : Blo 1028606 1737949 := bbase (se 3 (by rfl) ⟨325865, by rfl⟩ : syracuseStep 1737949 = 651731) (by norm_num)
theorem B1738037 : Blo 1028606 1738037 := bbase (se 5 (by rfl) ⟨81470, by rfl⟩ : syracuseStep 1738037 = 162941) (by norm_num)
theorem B5866901 : Blo 1028606 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B1738165 : Blo 1028606 1738165 := bbase (se 5 (by rfl) ⟨81476, by rfl⟩ : syracuseStep 1738165 = 162953) (by norm_num)
theorem B1738253 : Blo 1028606 1738253 := bbase (se 3 (by rfl) ⟨325922, by rfl⟩ : syracuseStep 1738253 = 651845) (by norm_num)
theorem B5211701 : Blo 1028606 5211701 := bbase (se 5 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 5211701 = 488597) (by norm_num)
theorem B3475061 : Blo 1028606 3475061 := bbase (se 5 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 3475061 = 325787) (by norm_num)
theorem B1738381 : Blo 1028606 1738381 := bbase (se 3 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 1738381 = 651893) (by norm_num)
theorem B1738469 : Blo 1028606 1738469 := bbase (se 4 (by rfl) ⟨162981, by rfl⟩ : syracuseStep 1738469 = 325963) (by norm_num)
theorem B1738597 : Blo 1028606 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B2197381 : Blo 1028606 2197381 := bbase (se 4 (by rfl) ⟨206004, by rfl⟩ : syracuseStep 2197381 = 412009) (by norm_num)
theorem B1738685 : Blo 1028606 1738685 := bbase (se 3 (by rfl) ⟨326003, by rfl⟩ : syracuseStep 1738685 = 652007) (by norm_num)
theorem B2197525 : Blo 1028606 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B3475493 : Blo 1028606 3475493 := bbase (se 4 (by rfl) ⟨325827, by rfl⟩ : syracuseStep 3475493 = 651655) (by norm_num)
theorem B1738813 : Blo 1028606 1738813 := bbase (se 3 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 1738813 = 652055) (by norm_num)
theorem B1738901 : Blo 1028606 1738901 := bbase (se 6 (by rfl) ⟨40755, by rfl⟩ : syracuseStep 1738901 = 81511) (by norm_num)
theorem B1739029 : Blo 1028606 1739029 := bbase (se 6 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 1739029 = 81517) (by norm_num)
theorem B1116509 : Blo 1028606 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B1739117 : Blo 1028606 1739117 := bbase (se 3 (by rfl) ⟨326084, by rfl⟩ : syracuseStep 1739117 = 652169) (by norm_num)
theorem B2197901 : Blo 1028606 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B3475925 : Blo 1028606 3475925 := bbase (se 7 (by rfl) ⟨40733, by rfl⟩ : syracuseStep 3475925 = 81467) (by norm_num)
theorem B1739245 : Blo 1028606 1739245 := bbase (se 3 (by rfl) ⟨326108, by rfl⟩ : syracuseStep 1739245 = 652217) (by norm_num)
theorem B5868085 : Blo 1028606 5868085 := bbase (se 5 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 5868085 = 550133) (by norm_num)
theorem B1739333 : Blo 1028606 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B1739461 : Blo 1028606 1739461 := bbase (se 4 (by rfl) ⟨163074, by rfl⟩ : syracuseStep 1739461 = 326149) (by norm_num)
theorem B2198269 : Blo 1028606 2198269 := bbase (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) (by norm_num)
theorem B1542917 : Blo 1028606 1542917 := bbase (se 4 (by rfl) ⟨144648, by rfl⟩ : syracuseStep 1542917 = 289297) (by norm_num)
theorem B1542941 : Blo 1028606 1542941 := bbase (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) (by norm_num)
theorem B1739549 : Blo 1028606 1739549 := bbase (se 3 (by rfl) ⟨326165, by rfl⟩ : syracuseStep 1739549 = 652331) (by norm_num)
theorem B1542965 : Blo 1028606 1542965 := bbase (se 5 (by rfl) ⟨72326, by rfl⟩ : syracuseStep 1542965 = 144653) (by norm_num)
theorem B5212997 : Blo 1028606 5212997 := bbase (se 4 (by rfl) ⟨488718, by rfl⟩ : syracuseStep 5212997 = 977437) (by norm_num)
theorem B1542989 : Blo 1028606 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B1543013 : Blo 1028606 1543013 := bbase (se 4 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 1543013 = 289315) (by norm_num)
theorem B1543037 : Blo 1028606 1543037 := bbase (se 3 (by rfl) ⟨289319, by rfl⟩ : syracuseStep 1543037 = 578639) (by norm_num)
theorem B3476357 : Blo 1028606 3476357 := bbase (se 4 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 3476357 = 651817) (by norm_num)
theorem B1543061 : Blo 1028606 1543061 := bbase (se 6 (by rfl) ⟨36165, by rfl⟩ : syracuseStep 1543061 = 72331) (by norm_num)
theorem B13732757 : Blo 1028606 13732757 := bbase (se 6 (by rfl) ⟨321861, by rfl⟩ : syracuseStep 13732757 = 643723) (by norm_num)
theorem B1739677 : Blo 1028606 1739677 := bbase (se 3 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 1739677 = 652379) (by norm_num)
theorem B1543085 : Blo 1028606 1543085 := bbase (se 3 (by rfl) ⟨289328, by rfl⟩ : syracuseStep 1543085 = 578657) (by norm_num)
theorem B1543109 : Blo 1028606 1543109 := bbase (se 4 (by rfl) ⟨144666, by rfl⟩ : syracuseStep 1543109 = 289333) (by norm_num)
theorem B1543133 : Blo 1028606 1543133 := bbase (se 3 (by rfl) ⟨289337, by rfl⟩ : syracuseStep 1543133 = 578675) (by norm_num)
theorem B1543157 : Blo 1028606 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B1739765 : Blo 1028606 1739765 := bbase (se 5 (by rfl) ⟨81551, by rfl⟩ : syracuseStep 1739765 = 163103) (by norm_num)
theorem B1543181 : Blo 1028606 1543181 := bbase (se 3 (by rfl) ⟨289346, by rfl⟩ : syracuseStep 1543181 = 578693) (by norm_num)
theorem B1543205 : Blo 1028606 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B1543229 : Blo 1028606 1543229 := bbase (se 3 (by rfl) ⟨289355, by rfl⟩ : syracuseStep 1543229 = 578711) (by norm_num)
theorem B1543253 : Blo 1028606 1543253 := bbase (se 8 (by rfl) ⟨9042, by rfl⟩ : syracuseStep 1543253 = 18085) (by norm_num)
theorem B1543277 : Blo 1028606 1543277 := bbase (se 3 (by rfl) ⟨289364, by rfl⟩ : syracuseStep 1543277 = 578729) (by norm_num)
theorem B1739893 : Blo 1028606 1739893 := bbase (se 5 (by rfl) ⟨81557, by rfl⟩ : syracuseStep 1739893 = 163115) (by norm_num)
theorem B1543301 : Blo 1028606 1543301 := bbase (se 4 (by rfl) ⟨144684, by rfl⟩ : syracuseStep 1543301 = 289369) (by norm_num)
theorem B1543325 : Blo 1028606 1543325 := bbase (se 3 (by rfl) ⟨289373, by rfl⟩ : syracuseStep 1543325 = 578747) (by norm_num)
theorem B1543349 : Blo 1028606 1543349 := bbase (se 5 (by rfl) ⟨72344, by rfl⟩ : syracuseStep 1543349 = 144689) (by norm_num)
theorem B7834805 : Blo 1028606 7834805 := bbase (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) (by norm_num)
theorem B1674437 : Blo 1028606 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B1543373 : Blo 1028606 1543373 := bbase (se 3 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 1543373 = 578765) (by norm_num)
theorem B1739981 : Blo 1028606 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B1543397 : Blo 1028606 1543397 := bbase (se 4 (by rfl) ⟨144693, by rfl⟩ : syracuseStep 1543397 = 289387) (by norm_num)
theorem B1543421 : Blo 1028606 1543421 := bbase (se 3 (by rfl) ⟨289391, by rfl⟩ : syracuseStep 1543421 = 578783) (by norm_num)
theorem B1543445 : Blo 1028606 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B1543469 : Blo 1028606 1543469 := bbase (se 3 (by rfl) ⟨289400, by rfl⟩ : syracuseStep 1543469 = 578801) (by norm_num)
theorem B3476789 : Blo 1028606 3476789 := bbase (se 5 (by rfl) ⟨162974, by rfl⟩ : syracuseStep 3476789 = 325949) (by norm_num)
theorem B1543493 : Blo 1028606 1543493 := bbase (se 4 (by rfl) ⟨144702, by rfl⟩ : syracuseStep 1543493 = 289405) (by norm_num)
theorem B1740109 : Blo 1028606 1740109 := bbase (se 3 (by rfl) ⟨326270, by rfl⟩ : syracuseStep 1740109 = 652541) (by norm_num)
theorem B1543517 : Blo 1028606 1543517 := bbase (se 3 (by rfl) ⟨289409, by rfl⟩ : syracuseStep 1543517 = 578819) (by norm_num)
theorem B1543541 : Blo 1028606 1543541 := bbase (se 5 (by rfl) ⟨72353, by rfl⟩ : syracuseStep 1543541 = 144707) (by norm_num)
theorem B7048565 : Blo 1028606 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1543565 : Blo 1028606 1543565 := bbase (se 3 (by rfl) ⟨289418, by rfl⟩ : syracuseStep 1543565 = 578837) (by norm_num)
theorem B1543589 : Blo 1028606 1543589 := bbase (se 4 (by rfl) ⟨144711, by rfl⟩ : syracuseStep 1543589 = 289423) (by norm_num)
theorem B1740197 : Blo 1028606 1740197 := bbase (se 4 (by rfl) ⟨163143, by rfl⟩ : syracuseStep 1740197 = 326287) (by norm_num)
theorem B1543613 : Blo 1028606 1543613 := bbase (se 3 (by rfl) ⟨289427, by rfl⟩ : syracuseStep 1543613 = 578855) (by norm_num)
theorem B1543637 : Blo 1028606 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B1543661 : Blo 1028606 1543661 := bbase (se 3 (by rfl) ⟨289436, by rfl⟩ : syracuseStep 1543661 = 578873) (by norm_num)
theorem B1543685 : Blo 1028606 1543685 := bbase (se 4 (by rfl) ⟨144720, by rfl⟩ : syracuseStep 1543685 = 289441) (by norm_num)
theorem B1543709 : Blo 1028606 1543709 := bbase (se 3 (by rfl) ⟨289445, by rfl⟩ : syracuseStep 1543709 = 578891) (by norm_num)
theorem B1740325 : Blo 1028606 1740325 := bbase (se 4 (by rfl) ⟨163155, by rfl⟩ : syracuseStep 1740325 = 326311) (by norm_num)
theorem B1543733 : Blo 1028606 1543733 := bbase (se 5 (by rfl) ⟨72362, by rfl⟩ : syracuseStep 1543733 = 144725) (by norm_num)
theorem B1543757 : Blo 1028606 1543757 := bbase (se 3 (by rfl) ⟨289454, by rfl⟩ : syracuseStep 1543757 = 578909) (by norm_num)
theorem B1543781 : Blo 1028606 1543781 := bbase (se 4 (by rfl) ⟨144729, by rfl⟩ : syracuseStep 1543781 = 289459) (by norm_num)
theorem B1543805 : Blo 1028606 1543805 := bbase (se 3 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 1543805 = 578927) (by norm_num)
theorem B1740413 : Blo 1028606 1740413 := bbase (se 3 (by rfl) ⟨326327, by rfl⟩ : syracuseStep 1740413 = 652655) (by norm_num)
theorem B1543829 : Blo 1028606 1543829 := bbase (se 6 (by rfl) ⟨36183, by rfl⟩ : syracuseStep 1543829 = 72367) (by norm_num)
theorem B1543853 : Blo 1028606 1543853 := bbase (se 3 (by rfl) ⟨289472, by rfl⟩ : syracuseStep 1543853 = 578945) (by norm_num)
theorem B1543877 : Blo 1028606 1543877 := bbase (se 4 (by rfl) ⟨144738, by rfl⟩ : syracuseStep 1543877 = 289477) (by norm_num)
theorem B1543901 : Blo 1028606 1543901 := bbase (se 3 (by rfl) ⟨289481, by rfl⟩ : syracuseStep 1543901 = 578963) (by norm_num)
theorem B3477221 : Blo 1028606 3477221 := bbase (se 4 (by rfl) ⟨325989, by rfl⟩ : syracuseStep 3477221 = 651979) (by norm_num)
theorem B1543925 : Blo 1028606 1543925 := bbase (se 5 (by rfl) ⟨72371, by rfl⟩ : syracuseStep 1543925 = 144743) (by norm_num)
theorem B1740541 : Blo 1028606 1740541 := bbase (se 3 (by rfl) ⟨326351, by rfl⟩ : syracuseStep 1740541 = 652703) (by norm_num)
theorem B4951813 : Blo 1028606 4951813 := bbase (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) (by norm_num)
theorem B1543949 : Blo 1028606 1543949 := bbase (se 3 (by rfl) ⟨289490, by rfl⟩ : syracuseStep 1543949 = 578981) (by norm_num)
theorem B1543973 : Blo 1028606 1543973 := bbase (se 4 (by rfl) ⟨144747, by rfl⟩ : syracuseStep 1543973 = 289495) (by norm_num)
theorem B1543997 : Blo 1028606 1543997 := bbase (se 3 (by rfl) ⟨289499, by rfl⟩ : syracuseStep 1543997 = 578999) (by norm_num)
theorem B1544021 : Blo 1028606 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B25431893 : Blo 1028606 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1740629 : Blo 1028606 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1544045 : Blo 1028606 1544045 := bbase (se 3 (by rfl) ⟨289508, by rfl⟩ : syracuseStep 1544045 = 579017) (by norm_num)
theorem B1544069 : Blo 1028606 1544069 := bbase (se 4 (by rfl) ⟨144756, by rfl⟩ : syracuseStep 1544069 = 289513) (by norm_num)
theorem B1544093 : Blo 1028606 1544093 := bbase (se 3 (by rfl) ⟨289517, by rfl⟩ : syracuseStep 1544093 = 579035) (by norm_num)
theorem B1544117 : Blo 1028606 1544117 := bbase (se 5 (by rfl) ⟨72380, by rfl⟩ : syracuseStep 1544117 = 144761) (by norm_num)
theorem B5574581 : Blo 1028606 5574581 := bbase (se 5 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 5574581 = 522617) (by norm_num)
theorem B1544141 : Blo 1028606 1544141 := bbase (se 3 (by rfl) ⟨289526, by rfl⟩ : syracuseStep 1544141 = 579053) (by norm_num)
theorem B1740757 : Blo 1028606 1740757 := bbase (se 7 (by rfl) ⟨20399, by rfl⟩ : syracuseStep 1740757 = 40799) (by norm_num)
theorem B1544165 : Blo 1028606 1544165 := bbase (se 4 (by rfl) ⟨144765, by rfl⟩ : syracuseStep 1544165 = 289531) (by norm_num)
theorem B6688757 : Blo 1028606 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1544189 : Blo 1028606 1544189 := bbase (se 3 (by rfl) ⟨289535, by rfl⟩ : syracuseStep 1544189 = 579071) (by norm_num)
theorem B1544213 : Blo 1028606 1544213 := bbase (se 6 (by rfl) ⟨36192, by rfl⟩ : syracuseStep 1544213 = 72385) (by norm_num)
theorem B1544237 : Blo 1028606 1544237 := bbase (se 3 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 1544237 = 579089) (by norm_num)
theorem B1740845 : Blo 1028606 1740845 := bbase (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) (by norm_num)
theorem B1544261 : Blo 1028606 1544261 := bbase (se 4 (by rfl) ⟨144774, by rfl⟩ : syracuseStep 1544261 = 289549) (by norm_num)
theorem B5214293 : Blo 1028606 5214293 := bbase (se 8 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 5214293 = 61105) (by norm_num)
theorem B1544285 : Blo 1028606 1544285 := bbase (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) (by norm_num)
theorem B1544309 : Blo 1028606 1544309 := bbase (se 5 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 1544309 = 144779) (by norm_num)
theorem B1544333 : Blo 1028606 1544333 := bbase (se 3 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 1544333 = 579125) (by norm_num)
theorem B3477653 : Blo 1028606 3477653 := bbase (se 6 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 3477653 = 163015) (by norm_num)
theorem B1544357 : Blo 1028606 1544357 := bbase (se 4 (by rfl) ⟨144783, by rfl⟩ : syracuseStep 1544357 = 289567) (by norm_num)
theorem B1740973 : Blo 1028606 1740973 := bbase (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) (by norm_num)
theorem B1544381 : Blo 1028606 1544381 := bbase (se 3 (by rfl) ⟨289571, by rfl⟩ : syracuseStep 1544381 = 579143) (by norm_num)
theorem B1544405 : Blo 1028606 1544405 := bbase (se 7 (by rfl) ⟨18098, by rfl⟩ : syracuseStep 1544405 = 36197) (by norm_num)
theorem B2199773 : Blo 1028606 2199773 := bbase (se 3 (by rfl) ⟨412457, by rfl⟩ : syracuseStep 2199773 = 824915) (by norm_num)
theorem B1544429 : Blo 1028606 1544429 := bbase (se 3 (by rfl) ⟨289580, by rfl⟩ : syracuseStep 1544429 = 579161) (by norm_num)
theorem B1544453 : Blo 1028606 1544453 := bbase (se 4 (by rfl) ⟨144792, by rfl⟩ : syracuseStep 1544453 = 289585) (by norm_num)
theorem B1741061 : Blo 1028606 1741061 := bbase (se 4 (by rfl) ⟨163224, by rfl⟩ : syracuseStep 1741061 = 326449) (by norm_num)
theorem B1544477 : Blo 1028606 1544477 := bbase (se 3 (by rfl) ⟨289589, by rfl⟩ : syracuseStep 1544477 = 579179) (by norm_num)
theorem B1544501 : Blo 1028606 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B1544525 : Blo 1028606 1544525 := bbase (se 3 (by rfl) ⟨289598, by rfl⟩ : syracuseStep 1544525 = 579197) (by norm_num)
theorem B1544549 : Blo 1028606 1544549 := bbase (se 4 (by rfl) ⟨144801, by rfl⟩ : syracuseStep 1544549 = 289603) (by norm_num)
theorem B2199917 : Blo 1028606 2199917 := bbase (se 3 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 2199917 = 824969) (by norm_num)
theorem B1544573 : Blo 1028606 1544573 := bbase (se 3 (by rfl) ⟨289607, by rfl⟩ : syracuseStep 1544573 = 579215) (by norm_num)
theorem B1741189 : Blo 1028606 1741189 := bbase (se 4 (by rfl) ⟨163236, by rfl⟩ : syracuseStep 1741189 = 326473) (by norm_num)
theorem B1544597 : Blo 1028606 1544597 := bbase (se 6 (by rfl) ⟨36201, by rfl⟩ : syracuseStep 1544597 = 72403) (by norm_num)
theorem B1544621 : Blo 1028606 1544621 := bbase (se 3 (by rfl) ⟨289616, by rfl⟩ : syracuseStep 1544621 = 579233) (by norm_num)
theorem B1544645 : Blo 1028606 1544645 := bbase (se 4 (by rfl) ⟨144810, by rfl⟩ : syracuseStep 1544645 = 289621) (by norm_num)
theorem B1544669 : Blo 1028606 1544669 := bbase (se 3 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 1544669 = 579251) (by norm_num)
theorem B1741277 : Blo 1028606 1741277 := bbase (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) (by norm_num)
theorem B1544693 : Blo 1028606 1544693 := bbase (se 5 (by rfl) ⟨72407, by rfl⟩ : syracuseStep 1544693 = 144815) (by norm_num)
theorem B5870069 : Blo 1028606 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B2789893 : Blo 1028606 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B1544717 : Blo 1028606 1544717 := bbase (se 3 (by rfl) ⟨289634, by rfl⟩ : syracuseStep 1544717 = 579269) (by norm_num)
theorem B1544741 : Blo 1028606 1544741 := bbase (se 4 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 1544741 = 289639) (by norm_num)
theorem B1544765 : Blo 1028606 1544765 := bbase (se 3 (by rfl) ⟨289643, by rfl⟩ : syracuseStep 1544765 = 579287) (by norm_num)
theorem B3478085 : Blo 1028606 3478085 := bbase (se 4 (by rfl) ⟨326070, by rfl⟩ : syracuseStep 3478085 = 652141) (by norm_num)
theorem B1544789 : Blo 1028606 1544789 := bbase (se 8 (by rfl) ⟨9051, by rfl⟩ : syracuseStep 1544789 = 18103) (by norm_num)
theorem B1741405 : Blo 1028606 1741405 := bbase (se 3 (by rfl) ⟨326513, by rfl⟩ : syracuseStep 1741405 = 653027) (by norm_num)
theorem B1544813 : Blo 1028606 1544813 := bbase (se 3 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 1544813 = 579305) (by norm_num)
theorem B1544837 : Blo 1028606 1544837 := bbase (se 4 (by rfl) ⟨144828, by rfl⟩ : syracuseStep 1544837 = 289657) (by norm_num)
theorem B1544861 : Blo 1028606 1544861 := bbase (se 3 (by rfl) ⟨289661, by rfl⟩ : syracuseStep 1544861 = 579323) (by norm_num)
theorem B1544885 : Blo 1028606 1544885 := bbase (se 5 (by rfl) ⟨72416, by rfl⟩ : syracuseStep 1544885 = 144833) (by norm_num)
theorem B1741493 : Blo 1028606 1741493 := bbase (se 5 (by rfl) ⟨81632, by rfl⟩ : syracuseStep 1741493 = 163265) (by norm_num)
theorem B1544909 : Blo 1028606 1544909 := bbase (se 3 (by rfl) ⟨289670, by rfl⟩ : syracuseStep 1544909 = 579341) (by norm_num)
theorem B2200277 : Blo 1028606 2200277 := bbase (se 7 (by rfl) ⟨25784, by rfl⟩ : syracuseStep 2200277 = 51569) (by norm_num)
theorem B1544933 : Blo 1028606 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1544957 : Blo 1028606 1544957 := bbase (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) (by norm_num)
theorem B1544981 : Blo 1028606 1544981 := bbase (se 6 (by rfl) ⟨36210, by rfl⟩ : syracuseStep 1544981 = 72421) (by norm_num)
theorem B1545005 : Blo 1028606 1545005 := bbase (se 3 (by rfl) ⟨289688, by rfl⟩ : syracuseStep 1545005 = 579377) (by norm_num)
theorem B1741621 : Blo 1028606 1741621 := bbase (se 5 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 1741621 = 163277) (by norm_num)
theorem B2790197 : Blo 1028606 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B1545029 : Blo 1028606 1545029 := bbase (se 4 (by rfl) ⟨144846, by rfl⟩ : syracuseStep 1545029 = 289693) (by norm_num)
theorem B1545053 : Blo 1028606 1545053 := bbase (se 3 (by rfl) ⟨289697, by rfl⟩ : syracuseStep 1545053 = 579395) (by norm_num)
theorem B1545077 : Blo 1028606 1545077 := bbase (se 5 (by rfl) ⟨72425, by rfl⟩ : syracuseStep 1545077 = 144851) (by norm_num)
theorem B1545101 : Blo 1028606 1545101 := bbase (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) (by norm_num)
theorem B1741709 : Blo 1028606 1741709 := bbase (se 3 (by rfl) ⟨326570, by rfl⟩ : syracuseStep 1741709 = 653141) (by norm_num)
theorem B1545125 : Blo 1028606 1545125 := bbase (se 4 (by rfl) ⟨144855, by rfl⟩ : syracuseStep 1545125 = 289711) (by norm_num)
theorem B1545149 : Blo 1028606 1545149 := bbase (se 3 (by rfl) ⟨289715, by rfl⟩ : syracuseStep 1545149 = 579431) (by norm_num)
theorem B1545173 : Blo 1028606 1545173 := bbase (se 7 (by rfl) ⟨18107, by rfl⟩ : syracuseStep 1545173 = 36215) (by norm_num)
theorem B1545197 : Blo 1028606 1545197 := bbase (se 3 (by rfl) ⟨289724, by rfl⟩ : syracuseStep 1545197 = 579449) (by norm_num)
theorem B3478517 : Blo 1028606 3478517 := bbase (se 5 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 3478517 = 326111) (by norm_num)
theorem B1545221 : Blo 1028606 1545221 := bbase (se 4 (by rfl) ⟨144864, by rfl⟩ : syracuseStep 1545221 = 289729) (by norm_num)
theorem B1741837 : Blo 1028606 1741837 := bbase (se 3 (by rfl) ⟨326594, by rfl⟩ : syracuseStep 1741837 = 653189) (by norm_num)
theorem B1545245 : Blo 1028606 1545245 := bbase (se 3 (by rfl) ⟨289733, by rfl⟩ : syracuseStep 1545245 = 579467) (by norm_num)
theorem B1545269 : Blo 1028606 1545269 := bbase (se 5 (by rfl) ⟨72434, by rfl⟩ : syracuseStep 1545269 = 144869) (by norm_num)
theorem B1545293 : Blo 1028606 1545293 := bbase (se 3 (by rfl) ⟨289742, by rfl⟩ : syracuseStep 1545293 = 579485) (by norm_num)
theorem B1545317 : Blo 1028606 1545317 := bbase (se 4 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 1545317 = 289747) (by norm_num)
theorem B1741925 : Blo 1028606 1741925 := bbase (se 4 (by rfl) ⟨163305, by rfl⟩ : syracuseStep 1741925 = 326611) (by norm_num)
theorem B1545341 : Blo 1028606 1545341 := bbase (se 3 (by rfl) ⟨289751, by rfl⟩ : syracuseStep 1545341 = 579503) (by norm_num)
theorem B1545365 : Blo 1028606 1545365 := bbase (se 6 (by rfl) ⟨36219, by rfl⟩ : syracuseStep 1545365 = 72439) (by norm_num)
theorem B1545389 : Blo 1028606 1545389 := bbase (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) (by norm_num)
theorem B1545413 : Blo 1028606 1545413 := bbase (se 4 (by rfl) ⟨144882, by rfl⟩ : syracuseStep 1545413 = 289765) (by norm_num)
theorem B1545437 : Blo 1028606 1545437 := bbase (se 3 (by rfl) ⟨289769, by rfl⟩ : syracuseStep 1545437 = 579539) (by norm_num)
theorem B1742053 : Blo 1028606 1742053 := bbase (se 4 (by rfl) ⟨163317, by rfl⟩ : syracuseStep 1742053 = 326635) (by norm_num)
theorem B1545461 : Blo 1028606 1545461 := bbase (se 5 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 1545461 = 144887) (by norm_num)
theorem B1545485 : Blo 1028606 1545485 := bbase (se 3 (by rfl) ⟨289778, by rfl⟩ : syracuseStep 1545485 = 579557) (by norm_num)
theorem B1545509 : Blo 1028606 1545509 := bbase (se 4 (by rfl) ⟨144891, by rfl⟩ : syracuseStep 1545509 = 289783) (by norm_num)
theorem B1545533 : Blo 1028606 1545533 := bbase (se 3 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 1545533 = 579575) (by norm_num)
theorem B1742141 : Blo 1028606 1742141 := bbase (se 3 (by rfl) ⟨326651, by rfl⟩ : syracuseStep 1742141 = 653303) (by norm_num)
theorem B1545557 : Blo 1028606 1545557 := bbase (se 14 (by rfl) ⟨141, by rfl⟩ : syracuseStep 1545557 = 283) (by norm_num)
theorem B5215589 : Blo 1028606 5215589 := bbase (se 4 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 5215589 = 977923) (by norm_num)
theorem B1545581 : Blo 1028606 1545581 := bbase (se 3 (by rfl) ⟨289796, by rfl⟩ : syracuseStep 1545581 = 579593) (by norm_num)
theorem B1545605 : Blo 1028606 1545605 := bbase (se 4 (by rfl) ⟨144900, by rfl⟩ : syracuseStep 1545605 = 289801) (by norm_num)
theorem B1545629 : Blo 1028606 1545629 := bbase (se 3 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 1545629 = 579611) (by norm_num)
theorem B3478949 : Blo 1028606 3478949 := bbase (se 4 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 3478949 = 652303) (by norm_num)
theorem B1545653 : Blo 1028606 1545653 := bbase (se 5 (by rfl) ⟨72452, by rfl⟩ : syracuseStep 1545653 = 144905) (by norm_num)
theorem B1742269 : Blo 1028606 1742269 := bbase (se 3 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 1742269 = 653351) (by norm_num)
theorem B1545677 : Blo 1028606 1545677 := bbase (se 3 (by rfl) ⟨289814, by rfl⟩ : syracuseStep 1545677 = 579629) (by norm_num)
theorem B1545701 : Blo 1028606 1545701 := bbase (se 4 (by rfl) ⟨144909, by rfl⟩ : syracuseStep 1545701 = 289819) (by norm_num)
theorem B1545725 : Blo 1028606 1545725 := bbase (se 3 (by rfl) ⟨289823, by rfl⟩ : syracuseStep 1545725 = 579647) (by norm_num)
theorem B1545749 : Blo 1028606 1545749 := bbase (se 6 (by rfl) ⟨36228, by rfl⟩ : syracuseStep 1545749 = 72457) (by norm_num)
theorem B1742357 : Blo 1028606 1742357 := bbase (se 6 (by rfl) ⟨40836, by rfl⟩ : syracuseStep 1742357 = 81673) (by norm_num)
theorem B1545773 : Blo 1028606 1545773 := bbase (se 3 (by rfl) ⟨289832, by rfl⟩ : syracuseStep 1545773 = 579665) (by norm_num)
theorem B1545797 : Blo 1028606 1545797 := bbase (se 4 (by rfl) ⟨144918, by rfl⟩ : syracuseStep 1545797 = 289837) (by norm_num)
theorem B2201165 : Blo 1028606 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B1545821 : Blo 1028606 1545821 := bbase (se 3 (by rfl) ⟨289841, by rfl⟩ : syracuseStep 1545821 = 579683) (by norm_num)
theorem B1545845 : Blo 1028606 1545845 := bbase (se 5 (by rfl) ⟨72461, by rfl⟩ : syracuseStep 1545845 = 144923) (by norm_num)
theorem B1545869 : Blo 1028606 1545869 := bbase (se 3 (by rfl) ⟨289850, by rfl⟩ : syracuseStep 1545869 = 579701) (by norm_num)
theorem B1742485 : Blo 1028606 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B1545893 : Blo 1028606 1545893 := bbase (se 4 (by rfl) ⟨144927, by rfl⟩ : syracuseStep 1545893 = 289855) (by norm_num)
theorem B1545917 : Blo 1028606 1545917 := bbase (se 3 (by rfl) ⟨289859, by rfl⟩ : syracuseStep 1545917 = 579719) (by norm_num)
theorem B1545941 : Blo 1028606 1545941 := bbase (se 7 (by rfl) ⟨18116, by rfl⟩ : syracuseStep 1545941 = 36233) (by norm_num)
theorem B1545965 : Blo 1028606 1545965 := bbase (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) (by norm_num)
theorem B1545989 : Blo 1028606 1545989 := bbase (se 4 (by rfl) ⟨144936, by rfl⟩ : syracuseStep 1545989 = 289873) (by norm_num)
theorem B1546013 : Blo 1028606 1546013 := bbase (se 3 (by rfl) ⟨289877, by rfl⟩ : syracuseStep 1546013 = 579755) (by norm_num)
theorem B1546037 : Blo 1028606 1546037 := bbase (se 5 (by rfl) ⟨72470, by rfl⟩ : syracuseStep 1546037 = 144941) (by norm_num)
theorem B2201413 : Blo 1028606 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B1546061 : Blo 1028606 1546061 := bbase (se 3 (by rfl) ⟨289886, by rfl⟩ : syracuseStep 1546061 = 579773) (by norm_num)
theorem B3479381 : Blo 1028606 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1546085 : Blo 1028606 1546085 := bbase (se 4 (by rfl) ⟨144945, by rfl⟩ : syracuseStep 1546085 = 289891) (by norm_num)
theorem B1546109 : Blo 1028606 1546109 := bbase (se 3 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 1546109 = 579791) (by norm_num)
theorem B2234245 : Blo 1028606 2234245 := bbase (se 4 (by rfl) ⟨209460, by rfl⟩ : syracuseStep 2234245 = 418921) (by norm_num)
theorem B4396949 : Blo 1028606 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B1546133 : Blo 1028606 1546133 := bbase (se 6 (by rfl) ⟨36237, by rfl⟩ : syracuseStep 1546133 = 72475) (by norm_num)
theorem B1546157 : Blo 1028606 1546157 := bbase (se 3 (by rfl) ⟨289904, by rfl⟩ : syracuseStep 1546157 = 579809) (by norm_num)
theorem B1546181 : Blo 1028606 1546181 := bbase (se 4 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 1546181 = 289909) (by norm_num)
theorem B1546205 : Blo 1028606 1546205 := bbase (se 3 (by rfl) ⟨289913, by rfl⟩ : syracuseStep 1546205 = 579827) (by norm_num)
theorem B1546229 : Blo 1028606 1546229 := bbase (se 5 (by rfl) ⟨72479, by rfl⟩ : syracuseStep 1546229 = 144959) (by norm_num)
theorem B1546253 : Blo 1028606 1546253 := bbase (se 3 (by rfl) ⟨289922, by rfl⟩ : syracuseStep 1546253 = 579845) (by norm_num)
theorem B1546277 : Blo 1028606 1546277 := bbase (se 4 (by rfl) ⟨144963, by rfl⟩ : syracuseStep 1546277 = 289927) (by norm_num)
theorem B1546301 : Blo 1028606 1546301 := bbase (se 3 (by rfl) ⟨289931, by rfl⟩ : syracuseStep 1546301 = 579863) (by norm_num)
theorem B1546325 : Blo 1028606 1546325 := bbase (se 8 (by rfl) ⟨9060, by rfl⟩ : syracuseStep 1546325 = 18121) (by norm_num)
theorem B1546349 : Blo 1028606 1546349 := bbase (se 3 (by rfl) ⟨289940, by rfl⟩ : syracuseStep 1546349 = 579881) (by norm_num)
theorem B1546373 : Blo 1028606 1546373 := bbase (se 4 (by rfl) ⟨144972, by rfl⟩ : syracuseStep 1546373 = 289945) (by norm_num)
theorem B1546397 : Blo 1028606 1546397 := bbase (se 3 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 1546397 = 579899) (by norm_num)
theorem B4397237 : Blo 1028606 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B1546421 : Blo 1028606 1546421 := bbase (se 5 (by rfl) ⟨72488, by rfl⟩ : syracuseStep 1546421 = 144977) (by norm_num)
theorem B1546445 : Blo 1028606 1546445 := bbase (se 3 (by rfl) ⟨289958, by rfl⟩ : syracuseStep 1546445 = 579917) (by norm_num)
theorem B1546469 : Blo 1028606 1546469 := bbase (se 4 (by rfl) ⟨144981, by rfl⟩ : syracuseStep 1546469 = 289963) (by norm_num)
theorem B1546493 : Blo 1028606 1546493 := bbase (se 3 (by rfl) ⟨289967, by rfl⟩ : syracuseStep 1546493 = 579935) (by norm_num)
theorem B3479813 : Blo 1028606 3479813 := bbase (se 4 (by rfl) ⟨326232, by rfl⟩ : syracuseStep 3479813 = 652465) (by norm_num)
theorem B1546517 : Blo 1028606 1546517 := bbase (se 6 (by rfl) ⟨36246, by rfl⟩ : syracuseStep 1546517 = 72493) (by norm_num)
theorem B1546541 : Blo 1028606 1546541 := bbase (se 3 (by rfl) ⟨289976, by rfl⟩ : syracuseStep 1546541 = 579953) (by norm_num)
theorem B2201917 : Blo 1028606 2201917 := bbase (se 3 (by rfl) ⟨412859, by rfl⟩ : syracuseStep 2201917 = 825719) (by norm_num)
theorem B1546565 : Blo 1028606 1546565 := bbase (se 4 (by rfl) ⟨144990, by rfl⟩ : syracuseStep 1546565 = 289981) (by norm_num)
theorem B1546589 : Blo 1028606 1546589 := bbase (se 3 (by rfl) ⟨289985, by rfl⟩ : syracuseStep 1546589 = 579971) (by norm_num)
theorem B1546613 : Blo 1028606 1546613 := bbase (se 5 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 1546613 = 144995) (by norm_num)
theorem B1546637 : Blo 1028606 1546637 := bbase (se 3 (by rfl) ⟨289994, by rfl⟩ : syracuseStep 1546637 = 579989) (by norm_num)
theorem B1546661 : Blo 1028606 1546661 := bbase (se 4 (by rfl) ⟨144999, by rfl⟩ : syracuseStep 1546661 = 289999) (by norm_num)
theorem B1546685 : Blo 1028606 1546685 := bbase (se 3 (by rfl) ⟨290003, by rfl⟩ : syracuseStep 1546685 = 580007) (by norm_num)
theorem B3578309 : Blo 1028606 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B1546709 : Blo 1028606 1546709 := bbase (se 7 (by rfl) ⟨18125, by rfl⟩ : syracuseStep 1546709 = 36251) (by norm_num)
theorem B1546733 : Blo 1028606 1546733 := bbase (se 3 (by rfl) ⟨290012, by rfl⟩ : syracuseStep 1546733 = 580025) (by norm_num)
theorem B1546757 : Blo 1028606 1546757 := bbase (se 4 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 1546757 = 290017) (by norm_num)
theorem B1546781 : Blo 1028606 1546781 := bbase (se 3 (by rfl) ⟨290021, by rfl⟩ : syracuseStep 1546781 = 580043) (by norm_num)
theorem B3709477 : Blo 1028606 3709477 := bbase (se 4 (by rfl) ⟨347763, by rfl⟩ : syracuseStep 3709477 = 695527) (by norm_num)
theorem B1546805 : Blo 1028606 1546805 := bbase (se 5 (by rfl) ⟨72506, by rfl⟩ : syracuseStep 1546805 = 145013) (by norm_num)
theorem B1546829 : Blo 1028606 1546829 := bbase (se 3 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 1546829 = 580061) (by norm_num)
theorem B1546853 : Blo 1028606 1546853 := bbase (se 4 (by rfl) ⟨145017, by rfl⟩ : syracuseStep 1546853 = 290035) (by norm_num)
theorem B5216885 : Blo 1028606 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B1546877 : Blo 1028606 1546877 := bbase (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) (by norm_num)
theorem B5872277 : Blo 1028606 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B1546901 : Blo 1028606 1546901 := bbase (se 6 (by rfl) ⟨36255, by rfl⟩ : syracuseStep 1546901 = 72511) (by norm_num)
theorem B1546925 : Blo 1028606 1546925 := bbase (se 3 (by rfl) ⟨290048, by rfl⟩ : syracuseStep 1546925 = 580097) (by norm_num)
theorem B3480245 : Blo 1028606 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B1546949 : Blo 1028606 1546949 := bbase (se 4 (by rfl) ⟨145026, by rfl⟩ : syracuseStep 1546949 = 290053) (by norm_num)
theorem B1546973 : Blo 1028606 1546973 := bbase (se 3 (by rfl) ⟨290057, by rfl⟩ : syracuseStep 1546973 = 580115) (by norm_num)
theorem B1546997 : Blo 1028606 1546997 := bbase (se 5 (by rfl) ⟨72515, by rfl⟩ : syracuseStep 1546997 = 145031) (by norm_num)
theorem B1547021 : Blo 1028606 1547021 := bbase (se 3 (by rfl) ⟨290066, by rfl⟩ : syracuseStep 1547021 = 580133) (by norm_num)
theorem B1547045 : Blo 1028606 1547045 := bbase (se 4 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 1547045 = 290071) (by norm_num)
theorem B1547069 : Blo 1028606 1547069 := bbase (se 3 (by rfl) ⟨290075, by rfl⟩ : syracuseStep 1547069 = 580151) (by norm_num)
theorem B1547093 : Blo 1028606 1547093 := bbase (se 9 (by rfl) ⟨4532, by rfl⟩ : syracuseStep 1547093 = 9065) (by norm_num)
theorem B1547117 : Blo 1028606 1547117 := bbase (se 3 (by rfl) ⟨290084, by rfl⟩ : syracuseStep 1547117 = 580169) (by norm_num)
theorem B1547141 : Blo 1028606 1547141 := bbase (se 4 (by rfl) ⟨145044, by rfl⟩ : syracuseStep 1547141 = 290089) (by norm_num)
theorem B2235269 : Blo 1028606 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1547165 : Blo 1028606 1547165 := bbase (se 3 (by rfl) ⟨290093, by rfl⟩ : syracuseStep 1547165 = 580187) (by norm_num)
theorem B4397989 : Blo 1028606 4397989 := bbase (se 4 (by rfl) ⟨412311, by rfl⟩ : syracuseStep 4397989 = 824623) (by norm_num)
theorem B1547189 : Blo 1028606 1547189 := bbase (se 5 (by rfl) ⟨72524, by rfl⟩ : syracuseStep 1547189 = 145049) (by norm_num)
theorem B1547213 : Blo 1028606 1547213 := bbase (se 3 (by rfl) ⟨290102, by rfl⟩ : syracuseStep 1547213 = 580205) (by norm_num)
theorem B1547237 : Blo 1028606 1547237 := bbase (se 4 (by rfl) ⟨145053, by rfl⟩ : syracuseStep 1547237 = 290107) (by norm_num)
theorem B1547261 : Blo 1028606 1547261 := bbase (se 3 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 1547261 = 580223) (by norm_num)
theorem B1547285 : Blo 1028606 1547285 := bbase (se 6 (by rfl) ⟨36264, by rfl⟩ : syracuseStep 1547285 = 72529) (by norm_num)
theorem B1547309 : Blo 1028606 1547309 := bbase (se 3 (by rfl) ⟨290120, by rfl⟩ : syracuseStep 1547309 = 580241) (by norm_num)
theorem B1547333 : Blo 1028606 1547333 := bbase (se 4 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 1547333 = 290125) (by norm_num)
theorem B1547357 : Blo 1028606 1547357 := bbase (se 3 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 1547357 = 580259) (by norm_num)
theorem B3480677 : Blo 1028606 3480677 := bbase (se 4 (by rfl) ⟨326313, by rfl⟩ : syracuseStep 3480677 = 652627) (by norm_num)
theorem B1547381 : Blo 1028606 1547381 := bbase (se 5 (by rfl) ⟨72533, by rfl⟩ : syracuseStep 1547381 = 145067) (by norm_num)
theorem B1547405 : Blo 1028606 1547405 := bbase (se 3 (by rfl) ⟨290138, by rfl⟩ : syracuseStep 1547405 = 580277) (by norm_num)
theorem B1547429 : Blo 1028606 1547429 := bbase (se 4 (by rfl) ⟨145071, by rfl⟩ : syracuseStep 1547429 = 290143) (by norm_num)
theorem B2202805 : Blo 1028606 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1547453 : Blo 1028606 1547453 := bbase (se 3 (by rfl) ⟨290147, by rfl⟩ : syracuseStep 1547453 = 580295) (by norm_num)
theorem B1547477 : Blo 1028606 1547477 := bbase (se 7 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 1547477 = 36269) (by norm_num)
theorem B1547501 : Blo 1028606 1547501 := bbase (se 3 (by rfl) ⟨290156, by rfl⟩ : syracuseStep 1547501 = 580313) (by norm_num)
theorem B1547525 : Blo 1028606 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B1547549 : Blo 1028606 1547549 := bbase (se 3 (by rfl) ⟨290165, by rfl⟩ : syracuseStep 1547549 = 580331) (by norm_num)
theorem B6266165 : Blo 1028606 6266165 := bbase (se 5 (by rfl) ⟨293726, by rfl⟩ : syracuseStep 6266165 = 587453) (by norm_num)
theorem B1547573 : Blo 1028606 1547573 := bbase (se 5 (by rfl) ⟨72542, by rfl⟩ : syracuseStep 1547573 = 145085) (by norm_num)
theorem B1547597 : Blo 1028606 1547597 := bbase (se 3 (by rfl) ⟨290174, by rfl⟩ : syracuseStep 1547597 = 580349) (by norm_num)
theorem B38083925 : Blo 1028606 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B1547621 : Blo 1028606 1547621 := bbase (se 4 (by rfl) ⟨145089, by rfl⟩ : syracuseStep 1547621 = 290179) (by norm_num)
theorem B1547645 : Blo 1028606 1547645 := bbase (se 3 (by rfl) ⟨290183, by rfl⟩ : syracuseStep 1547645 = 580367) (by norm_num)
theorem B1547669 : Blo 1028606 1547669 := bbase (se 6 (by rfl) ⟨36273, by rfl⟩ : syracuseStep 1547669 = 72547) (by norm_num)
theorem B1547693 : Blo 1028606 1547693 := bbase (se 3 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 1547693 = 580385) (by norm_num)
theorem B1547717 : Blo 1028606 1547717 := bbase (se 4 (by rfl) ⟨145098, by rfl⟩ : syracuseStep 1547717 = 290197) (by norm_num)
theorem B1547741 : Blo 1028606 1547741 := bbase (se 3 (by rfl) ⟨290201, by rfl⟩ : syracuseStep 1547741 = 580403) (by norm_num)
theorem B5283301 : Blo 1028606 5283301 := bbase (se 4 (by rfl) ⟨495309, by rfl⟩ : syracuseStep 5283301 = 990619) (by norm_num)
theorem B3907061 : Blo 1028606 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B5578229 : Blo 1028606 5578229 := bbase (se 5 (by rfl) ⟨261479, by rfl⟩ : syracuseStep 5578229 = 522959) (by norm_num)
theorem B1547765 : Blo 1028606 1547765 := bbase (se 5 (by rfl) ⟨72551, by rfl⟩ : syracuseStep 1547765 = 145103) (by norm_num)
theorem B1547789 : Blo 1028606 1547789 := bbase (se 3 (by rfl) ⟨290210, by rfl⟩ : syracuseStep 1547789 = 580421) (by norm_num)
theorem B3481109 : Blo 1028606 3481109 := bbase (se 6 (by rfl) ⟨81588, by rfl⟩ : syracuseStep 3481109 = 163177) (by norm_num)
theorem B1547813 : Blo 1028606 1547813 := bbase (se 4 (by rfl) ⟨145107, by rfl⟩ : syracuseStep 1547813 = 290215) (by norm_num)
theorem B1547837 : Blo 1028606 1547837 := bbase (se 3 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 1547837 = 580439) (by norm_num)
theorem B1547861 : Blo 1028606 1547861 := bbase (se 8 (by rfl) ⟨9069, by rfl⟩ : syracuseStep 1547861 = 18139) (by norm_num)
theorem B1547885 : Blo 1028606 1547885 := bbase (se 3 (by rfl) ⟨290228, by rfl⟩ : syracuseStep 1547885 = 580457) (by norm_num)
theorem B1547909 : Blo 1028606 1547909 := bbase (se 4 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 1547909 = 290233) (by norm_num)
theorem B4398725 : Blo 1028606 4398725 := bbase (se 4 (by rfl) ⟨412380, by rfl⟩ : syracuseStep 4398725 = 824761) (by norm_num)
theorem B1547933 : Blo 1028606 1547933 := bbase (se 3 (by rfl) ⟨290237, by rfl⟩ : syracuseStep 1547933 = 580475) (by norm_num)
theorem B2203301 : Blo 1028606 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B1547957 : Blo 1028606 1547957 := bbase (se 5 (by rfl) ⟨72560, by rfl⟩ : syracuseStep 1547957 = 145121) (by norm_num)
theorem B1547981 : Blo 1028606 1547981 := bbase (se 3 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 1547981 = 580493) (by norm_num)
theorem B1548005 : Blo 1028606 1548005 := bbase (se 4 (by rfl) ⟨145125, by rfl⟩ : syracuseStep 1548005 = 290251) (by norm_num)
theorem B1548029 : Blo 1028606 1548029 := bbase (se 3 (by rfl) ⟨290255, by rfl⟩ : syracuseStep 1548029 = 580511) (by norm_num)
theorem B3907349 : Blo 1028606 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1548053 : Blo 1028606 1548053 := bbase (se 6 (by rfl) ⟨36282, by rfl⟩ : syracuseStep 1548053 = 72565) (by norm_num)
theorem B1548077 : Blo 1028606 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B1548101 : Blo 1028606 1548101 := bbase (se 4 (by rfl) ⟨145134, by rfl⟩ : syracuseStep 1548101 = 290269) (by norm_num)
theorem B1548125 : Blo 1028606 1548125 := bbase (se 3 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 1548125 = 580547) (by norm_num)
theorem B4956005 : Blo 1028606 4956005 := bbase (se 4 (by rfl) ⟨464625, by rfl⟩ : syracuseStep 4956005 = 929251) (by norm_num)
theorem B1548149 : Blo 1028606 1548149 := bbase (se 5 (by rfl) ⟨72569, by rfl⟩ : syracuseStep 1548149 = 145139) (by norm_num)
theorem B5218181 : Blo 1028606 5218181 := bbase (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) (by norm_num)
theorem B1548173 : Blo 1028606 1548173 := bbase (se 3 (by rfl) ⟨290282, by rfl⟩ : syracuseStep 1548173 = 580565) (by norm_num)
theorem B1548197 : Blo 1028606 1548197 := bbase (se 4 (by rfl) ⟨145143, by rfl⟩ : syracuseStep 1548197 = 290287) (by norm_num)
theorem B1548221 : Blo 1028606 1548221 := bbase (se 3 (by rfl) ⟨290291, by rfl⟩ : syracuseStep 1548221 = 580583) (by norm_num)
theorem B3481541 : Blo 1028606 3481541 := bbase (se 4 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 3481541 = 652789) (by norm_num)
theorem B1548245 : Blo 1028606 1548245 := bbase (se 7 (by rfl) ⟨18143, by rfl⟩ : syracuseStep 1548245 = 36287) (by norm_num)
theorem B1548269 : Blo 1028606 1548269 := bbase (se 3 (by rfl) ⟨290300, by rfl⟩ : syracuseStep 1548269 = 580601) (by norm_num)
theorem B1548293 : Blo 1028606 1548293 := bbase (se 4 (by rfl) ⟨145152, by rfl⟩ : syracuseStep 1548293 = 290305) (by norm_num)
theorem B1548317 : Blo 1028606 1548317 := bbase (se 3 (by rfl) ⟨290309, by rfl⟩ : syracuseStep 1548317 = 580619) (by norm_num)
theorem B1548341 : Blo 1028606 1548341 := bbase (se 5 (by rfl) ⟨72578, by rfl⟩ : syracuseStep 1548341 = 145157) (by norm_num)
theorem B1548365 : Blo 1028606 1548365 := bbase (se 3 (by rfl) ⟨290318, by rfl⟩ : syracuseStep 1548365 = 580637) (by norm_num)
theorem B1548389 : Blo 1028606 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B1548413 : Blo 1028606 1548413 := bbase (se 3 (by rfl) ⟨290327, by rfl⟩ : syracuseStep 1548413 = 580655) (by norm_num)
theorem B9412757 : Blo 1028606 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B1548437 : Blo 1028606 1548437 := bbase (se 6 (by rfl) ⟨36291, by rfl⟩ : syracuseStep 1548437 = 72583) (by norm_num)
theorem B1548461 : Blo 1028606 1548461 := bbase (se 3 (by rfl) ⟨290336, by rfl⟩ : syracuseStep 1548461 = 580673) (by norm_num)
theorem B1548485 : Blo 1028606 1548485 := bbase (se 4 (by rfl) ⟨145170, by rfl⟩ : syracuseStep 1548485 = 290341) (by norm_num)
theorem B1548509 : Blo 1028606 1548509 := bbase (se 3 (by rfl) ⟨290345, by rfl⟩ : syracuseStep 1548509 = 580691) (by norm_num)
theorem B1548533 : Blo 1028606 1548533 := bbase (se 5 (by rfl) ⟨72587, by rfl⟩ : syracuseStep 1548533 = 145175) (by norm_num)
theorem B1548557 : Blo 1028606 1548557 := bbase (se 3 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 1548557 = 580709) (by norm_num)
theorem B1548581 : Blo 1028606 1548581 := bbase (se 4 (by rfl) ⟨145179, by rfl⟩ : syracuseStep 1548581 = 290359) (by norm_num)
theorem B1548605 : Blo 1028606 1548605 := bbase (se 3 (by rfl) ⟨290363, by rfl⟩ : syracuseStep 1548605 = 580727) (by norm_num)
theorem B1548629 : Blo 1028606 1548629 := bbase (se 10 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 1548629 = 4537) (by norm_num)
theorem B1548653 : Blo 1028606 1548653 := bbase (se 3 (by rfl) ⟨290372, by rfl⟩ : syracuseStep 1548653 = 580745) (by norm_num)
theorem B3481973 : Blo 1028606 3481973 := bbase (se 5 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 3481973 = 326435) (by norm_num)
theorem B1548677 : Blo 1028606 1548677 := bbase (se 4 (by rfl) ⟨145188, by rfl⟩ : syracuseStep 1548677 = 290377) (by norm_num)
theorem B1548701 : Blo 1028606 1548701 := bbase (se 3 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 1548701 = 580763) (by norm_num)
theorem B1548725 : Blo 1028606 1548725 := bbase (se 5 (by rfl) ⟨72596, by rfl⟩ : syracuseStep 1548725 = 145193) (by norm_num)
theorem B1548749 : Blo 1028606 1548749 := bbase (se 3 (by rfl) ⟨290390, by rfl⟩ : syracuseStep 1548749 = 580781) (by norm_num)
theorem B1548773 : Blo 1028606 1548773 := bbase (se 4 (by rfl) ⟨145197, by rfl⟩ : syracuseStep 1548773 = 290395) (by norm_num)
theorem B1548797 : Blo 1028606 1548797 := bbase (se 3 (by rfl) ⟨290399, by rfl⟩ : syracuseStep 1548797 = 580799) (by norm_num)
theorem B1548821 : Blo 1028606 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B2204189 : Blo 1028606 2204189 := bbase (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) (by norm_num)
theorem B1548845 : Blo 1028606 1548845 := bbase (se 3 (by rfl) ⟨290408, by rfl⟩ : syracuseStep 1548845 = 580817) (by norm_num)
theorem B1548869 : Blo 1028606 1548869 := bbase (se 4 (by rfl) ⟨145206, by rfl⟩ : syracuseStep 1548869 = 290413) (by norm_num)
theorem B1548893 : Blo 1028606 1548893 := bbase (se 3 (by rfl) ⟨290417, by rfl⟩ : syracuseStep 1548893 = 580835) (by norm_num)
theorem B2204309 : Blo 1028606 2204309 := bbase (se 6 (by rfl) ⟨51663, by rfl⟩ : syracuseStep 2204309 = 103327) (by norm_num)
theorem B3482405 : Blo 1028606 3482405 := bbase (se 4 (by rfl) ⟨326475, by rfl⟩ : syracuseStep 3482405 = 652951) (by norm_num)
theorem B6595445 : Blo 1028606 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B1254269 : Blo 1028606 1254269 := bbase (se 3 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 1254269 = 470351) (by norm_num)
theorem B3908533 : Blo 1028606 3908533 := bbase (se 5 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 3908533 = 366425) (by norm_num)
theorem B1647677 : Blo 1028606 1647677 := bbase (se 3 (by rfl) ⟨308939, by rfl⟩ : syracuseStep 1647677 = 617879) (by norm_num)
theorem B5022805 : Blo 1028606 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B5219477 : Blo 1028606 5219477 := bbase (se 6 (by rfl) ⟨122331, by rfl⟩ : syracuseStep 5219477 = 244663) (by norm_num)
theorem B3482837 : Blo 1028606 3482837 := bbase (se 7 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 3482837 = 81629) (by norm_num)
theorem B3908837 : Blo 1028606 3908837 := bbase (se 4 (by rfl) ⟨366453, by rfl⟩ : syracuseStep 3908837 = 732907) (by norm_num)
theorem B2204941 : Blo 1028606 2204941 := bbase (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) (by norm_num)
theorem B1647901 : Blo 1028606 1647901 := bbase (se 3 (by rfl) ⟨308981, by rfl⟩ : syracuseStep 1647901 = 617963) (by norm_num)
theorem B1647965 : Blo 1028606 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B1648093 : Blo 1028606 1648093 := bbase (se 3 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 1648093 = 618035) (by norm_num)
theorem B1320457 : Blo 1028606 1320457 := bbase (se 2 (by rfl) ⟨495171, by rfl⟩ : syracuseStep 1320457 = 990343) (by norm_num)
theorem B3483269 : Blo 1028606 3483269 := bbase (se 4 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 3483269 = 653113) (by norm_num)
theorem B1189601 : Blo 1028606 1189601 := bbase (se 2 (by rfl) ⟨446100, by rfl⟩ : syracuseStep 1189601 = 892201) (by norm_num)
theorem B1484821 : Blo 1028606 1484821 := bbase (se 6 (by rfl) ⟨34800, by rfl⟩ : syracuseStep 1484821 = 69601) (by norm_num)
theorem B3483701 : Blo 1028606 3483701 := bbase (se 5 (by rfl) ⟨163298, by rfl⟩ : syracuseStep 3483701 = 326597) (by norm_num)
theorem B1157197 : Blo 1028606 1157197 := bbase (se 3 (by rfl) ⟨216974, by rfl⟩ : syracuseStep 1157197 = 433949) (by norm_num)
theorem B1157233 : Blo 1028606 1157233 := bbase (se 2 (by rfl) ⟨433962, by rfl⟩ : syracuseStep 1157233 = 867925) (by norm_num)
theorem B1157269 : Blo 1028606 1157269 := bbase (se 6 (by rfl) ⟨27123, by rfl⟩ : syracuseStep 1157269 = 54247) (by norm_num)
theorem B1157305 : Blo 1028606 1157305 := bbase (se 2 (by rfl) ⟨433989, by rfl⟩ : syracuseStep 1157305 = 867979) (by norm_num)
theorem B1157341 : Blo 1028606 1157341 := bbase (se 3 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 1157341 = 434003) (by norm_num)
theorem B4466933 : Blo 1028606 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B1157377 : Blo 1028606 1157377 := bbase (se 2 (by rfl) ⟨434016, by rfl⟩ : syracuseStep 1157377 = 868033) (by norm_num)
theorem B1157413 : Blo 1028606 1157413 := bbase (se 4 (by rfl) ⟨108507, by rfl⟩ : syracuseStep 1157413 = 217015) (by norm_num)
theorem B1157449 : Blo 1028606 1157449 := bbase (se 2 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 1157449 = 868087) (by norm_num)
theorem B1157485 : Blo 1028606 1157485 := bbase (se 3 (by rfl) ⟨217028, by rfl⟩ : syracuseStep 1157485 = 434057) (by norm_num)
theorem B1157521 : Blo 1028606 1157521 := bbase (se 2 (by rfl) ⟨434070, by rfl⟩ : syracuseStep 1157521 = 868141) (by norm_num)
theorem B1321381 : Blo 1028606 1321381 := bbase (se 4 (by rfl) ⟨123879, by rfl⟩ : syracuseStep 1321381 = 247759) (by norm_num)
theorem B5220773 : Blo 1028606 5220773 := bbase (se 4 (by rfl) ⟨489447, by rfl⟩ : syracuseStep 5220773 = 978895) (by norm_num)
theorem B1157557 : Blo 1028606 1157557 := bbase (se 5 (by rfl) ⟨54260, by rfl⟩ : syracuseStep 1157557 = 108521) (by norm_num)
theorem B1157593 : Blo 1028606 1157593 := bbase (se 2 (by rfl) ⟨434097, by rfl⟩ : syracuseStep 1157593 = 868195) (by norm_num)
theorem B3484133 : Blo 1028606 3484133 := bbase (se 4 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 3484133 = 653275) (by norm_num)
theorem B1157629 : Blo 1028606 1157629 := bbase (se 3 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 1157629 = 434111) (by norm_num)
theorem B1157665 : Blo 1028606 1157665 := bbase (se 2 (by rfl) ⟨434124, by rfl⟩ : syracuseStep 1157665 = 868249) (by norm_num)
theorem B1321525 : Blo 1028606 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1157701 : Blo 1028606 1157701 := bbase (se 4 (by rfl) ⟨108534, by rfl⟩ : syracuseStep 1157701 = 217069) (by norm_num)
theorem B1157737 : Blo 1028606 1157737 := bbase (se 2 (by rfl) ⟨434151, by rfl⟩ : syracuseStep 1157737 = 868303) (by norm_num)
theorem B1157773 : Blo 1028606 1157773 := bbase (se 3 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 1157773 = 434165) (by norm_num)
theorem B1649317 : Blo 1028606 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B1157809 : Blo 1028606 1157809 := bbase (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) (by norm_num)
theorem B1157845 : Blo 1028606 1157845 := bbase (se 7 (by rfl) ⟨13568, by rfl⟩ : syracuseStep 1157845 = 27137) (by norm_num)
theorem B1157881 : Blo 1028606 1157881 := bbase (se 2 (by rfl) ⟨434205, by rfl⟩ : syracuseStep 1157881 = 868411) (by norm_num)
theorem B1157917 : Blo 1028606 1157917 := bbase (se 3 (by rfl) ⟨217109, by rfl⟩ : syracuseStep 1157917 = 434219) (by norm_num)
theorem B1157953 : Blo 1028606 1157953 := bbase (se 2 (by rfl) ⟨434232, by rfl⟩ : syracuseStep 1157953 = 868465) (by norm_num)
theorem B1157989 : Blo 1028606 1157989 := bbase (se 4 (by rfl) ⟨108561, by rfl⟩ : syracuseStep 1157989 = 217123) (by norm_num)
theorem B4402021 : Blo 1028606 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B1158025 : Blo 1028606 1158025 := bbase (se 2 (by rfl) ⟨434259, by rfl⟩ : syracuseStep 1158025 = 868519) (by norm_num)
theorem B6269845 : Blo 1028606 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B17640341 : Blo 1028606 17640341 := bbase (se 6 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 17640341 = 826891) (by norm_num)
theorem B3484565 : Blo 1028606 3484565 := bbase (se 6 (by rfl) ⟨81669, by rfl⟩ : syracuseStep 3484565 = 163339) (by norm_num)
theorem B1158061 : Blo 1028606 1158061 := bbase (se 3 (by rfl) ⟨217136, by rfl⟩ : syracuseStep 1158061 = 434273) (by norm_num)
theorem B1158097 : Blo 1028606 1158097 := bbase (se 2 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 1158097 = 868573) (by norm_num)
theorem B3714005 : Blo 1028606 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B1158133 : Blo 1028606 1158133 := bbase (se 5 (by rfl) ⟨54287, by rfl⟩ : syracuseStep 1158133 = 108575) (by norm_num)
theorem B1158169 : Blo 1028606 1158169 := bbase (se 2 (by rfl) ⟨434313, by rfl⟩ : syracuseStep 1158169 = 868627) (by norm_num)
theorem B1158205 : Blo 1028606 1158205 := bbase (se 3 (by rfl) ⟨217163, by rfl⟩ : syracuseStep 1158205 = 434327) (by norm_num)
theorem B30125141 : Blo 1028606 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B1158241 : Blo 1028606 1158241 := bbase (se 2 (by rfl) ⟨434340, by rfl⟩ : syracuseStep 1158241 = 868681) (by norm_num)
theorem B1191029 : Blo 1028606 1191029 := bbase (se 5 (by rfl) ⟨55829, by rfl⟩ : syracuseStep 1191029 = 111659) (by norm_num)
theorem B1158277 : Blo 1028606 1158277 := bbase (se 4 (by rfl) ⟨108588, by rfl⟩ : syracuseStep 1158277 = 217177) (by norm_num)
theorem B1158313 : Blo 1028606 1158313 := bbase (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) (by norm_num)
theorem B1158349 : Blo 1028606 1158349 := bbase (se 3 (by rfl) ⟨217190, by rfl⟩ : syracuseStep 1158349 = 434381) (by norm_num)
theorem B1322201 : Blo 1028606 1322201 := bbase (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) (by norm_num)
theorem B1322221 : Blo 1028606 1322221 := bbase (se 3 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 1322221 = 495833) (by norm_num)
theorem B1158385 : Blo 1028606 1158385 := bbase (se 2 (by rfl) ⟨434394, by rfl⟩ : syracuseStep 1158385 = 868789) (by norm_num)
theorem B7417109 : Blo 1028606 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B1158421 : Blo 1028606 1158421 := bbase (se 6 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 1158421 = 54301) (by norm_num)
theorem B3910949 : Blo 1028606 3910949 := bbase (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) (by norm_num)
theorem B1158457 : Blo 1028606 1158457 := bbase (se 2 (by rfl) ⟨434421, by rfl⟩ : syracuseStep 1158457 = 868843) (by norm_num)
theorem B1649989 : Blo 1028606 1649989 := bbase (se 4 (by rfl) ⟨154686, by rfl⟩ : syracuseStep 1649989 = 309373) (by norm_num)
theorem B3484997 : Blo 1028606 3484997 := bbase (se 4 (by rfl) ⟨326718, by rfl⟩ : syracuseStep 3484997 = 653437) (by norm_num)
theorem B1158493 : Blo 1028606 1158493 := bbase (se 3 (by rfl) ⟨217217, by rfl⟩ : syracuseStep 1158493 = 434435) (by norm_num)
theorem B1158529 : Blo 1028606 1158529 := bbase (se 2 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 1158529 = 868897) (by norm_num)
theorem B3714437 : Blo 1028606 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B1158565 : Blo 1028606 1158565 := bbase (se 4 (by rfl) ⟨108615, by rfl⟩ : syracuseStep 1158565 = 217231) (by norm_num)
theorem B1158601 : Blo 1028606 1158601 := bbase (se 2 (by rfl) ⟨434475, by rfl⟩ : syracuseStep 1158601 = 868951) (by norm_num)
theorem B1158637 : Blo 1028606 1158637 := bbase (se 3 (by rfl) ⟨217244, by rfl⟩ : syracuseStep 1158637 = 434489) (by norm_num)
theorem B1158673 : Blo 1028606 1158673 := bbase (se 2 (by rfl) ⟨434502, by rfl⟩ : syracuseStep 1158673 = 869005) (by norm_num)
theorem B4697621 : Blo 1028606 4697621 := bbase (se 6 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 4697621 = 220201) (by norm_num)
theorem B1158709 : Blo 1028606 1158709 := bbase (se 5 (by rfl) ⟨54314, by rfl⟩ : syracuseStep 1158709 = 108629) (by norm_num)
theorem B3911237 : Blo 1028606 3911237 := bbase (se 4 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 3911237 = 733357) (by norm_num)
theorem B1158745 : Blo 1028606 1158745 := bbase (se 2 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 1158745 = 869059) (by norm_num)
theorem B1158781 : Blo 1028606 1158781 := bbase (se 3 (by rfl) ⟨217271, by rfl⟩ : syracuseStep 1158781 = 434543) (by norm_num)
theorem B1158817 : Blo 1028606 1158817 := bbase (se 2 (by rfl) ⟨434556, by rfl⟩ : syracuseStep 1158817 = 869113) (by norm_num)
theorem B5222069 : Blo 1028606 5222069 := bbase (se 5 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 5222069 = 489569) (by norm_num)
theorem B1158853 : Blo 1028606 1158853 := bbase (se 4 (by rfl) ⟨108642, by rfl⟩ : syracuseStep 1158853 = 217285) (by norm_num)
theorem B1158889 : Blo 1028606 1158889 := bbase (se 2 (by rfl) ⟨434583, by rfl⟩ : syracuseStep 1158889 = 869167) (by norm_num)
theorem B1191677 : Blo 1028606 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B1158925 : Blo 1028606 1158925 := bbase (se 3 (by rfl) ⟨217298, by rfl⟩ : syracuseStep 1158925 = 434597) (by norm_num)
theorem B6598421 : Blo 1028606 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B1158961 : Blo 1028606 1158961 := bbase (se 2 (by rfl) ⟨434610, by rfl⟩ : syracuseStep 1158961 = 869221) (by norm_num)
theorem B1158997 : Blo 1028606 1158997 := bbase (se 9 (by rfl) ⟨3395, by rfl⟩ : syracuseStep 1158997 = 6791) (by norm_num)
theorem B1159033 : Blo 1028606 1159033 := bbase (se 2 (by rfl) ⟨434637, by rfl⟩ : syracuseStep 1159033 = 869275) (by norm_num)
theorem B16691093 : Blo 1028606 16691093 := bbase (se 6 (by rfl) ⟨391197, by rfl⟩ : syracuseStep 16691093 = 782395) (by norm_num)
theorem B1159069 : Blo 1028606 1159069 := bbase (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) (by norm_num)
theorem B1159105 : Blo 1028606 1159105 := bbase (se 2 (by rfl) ⟨434664, by rfl⟩ : syracuseStep 1159105 = 869329) (by norm_num)
theorem B3715013 : Blo 1028606 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B1159141 : Blo 1028606 1159141 := bbase (se 4 (by rfl) ⟨108669, by rfl⟩ : syracuseStep 1159141 = 217339) (by norm_num)
theorem B1159177 : Blo 1028606 1159177 := bbase (se 2 (by rfl) ⟨434691, by rfl⟩ : syracuseStep 1159177 = 869383) (by norm_num)
theorem B1159213 : Blo 1028606 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B1159249 : Blo 1028606 1159249 := bbase (se 2 (by rfl) ⟨434718, by rfl⟩ : syracuseStep 1159249 = 869437) (by norm_num)
theorem B1159285 : Blo 1028606 1159285 := bbase (se 5 (by rfl) ⟨54341, by rfl⟩ : syracuseStep 1159285 = 108683) (by norm_num)
theorem B1159321 : Blo 1028606 1159321 := bbase (se 2 (by rfl) ⟨434745, by rfl⟩ : syracuseStep 1159321 = 869491) (by norm_num)
theorem B1159357 : Blo 1028606 1159357 := bbase (se 3 (by rfl) ⟨217379, by rfl⟩ : syracuseStep 1159357 = 434759) (by norm_num)
theorem B1159393 : Blo 1028606 1159393 := bbase (se 2 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 1159393 = 869545) (by norm_num)
theorem B1159429 : Blo 1028606 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B1323289 : Blo 1028606 1323289 := bbase (se 2 (by rfl) ⟨496233, by rfl⟩ : syracuseStep 1323289 = 992467) (by norm_num)
theorem B1159465 : Blo 1028606 1159465 := bbase (se 2 (by rfl) ⟨434799, by rfl⟩ : syracuseStep 1159465 = 869599) (by norm_num)
theorem B1650989 : Blo 1028606 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B1159501 : Blo 1028606 1159501 := bbase (se 3 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 1159501 = 434813) (by norm_num)
theorem B1159537 : Blo 1028606 1159537 := bbase (se 2 (by rfl) ⟨434826, by rfl⟩ : syracuseStep 1159537 = 869653) (by norm_num)
theorem B7811477 : Blo 1028606 7811477 := bbase (se 6 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 7811477 = 366163) (by norm_num)
theorem B1159573 : Blo 1028606 1159573 := bbase (se 6 (by rfl) ⟨27177, by rfl⟩ : syracuseStep 1159573 = 54355) (by norm_num)
theorem B1159609 : Blo 1028606 1159609 := bbase (se 2 (by rfl) ⟨434853, by rfl⟩ : syracuseStep 1159609 = 869707) (by norm_num)
theorem B1159645 : Blo 1028606 1159645 := bbase (se 3 (by rfl) ⟨217433, by rfl⟩ : syracuseStep 1159645 = 434867) (by norm_num)
theorem B1159681 : Blo 1028606 1159681 := bbase (se 2 (by rfl) ⟨434880, by rfl⟩ : syracuseStep 1159681 = 869761) (by norm_num)
theorem B1159717 : Blo 1028606 1159717 := bbase (se 4 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 1159717 = 217447) (by norm_num)
theorem B1323577 : Blo 1028606 1323577 := bbase (se 2 (by rfl) ⟨496341, by rfl⟩ : syracuseStep 1323577 = 992683) (by norm_num)
theorem B1159753 : Blo 1028606 1159753 := bbase (se 2 (by rfl) ⟨434907, by rfl⟩ : syracuseStep 1159753 = 869815) (by norm_num)
theorem B1159789 : Blo 1028606 1159789 := bbase (se 3 (by rfl) ⟨217460, by rfl⟩ : syracuseStep 1159789 = 434921) (by norm_num)
theorem B1159825 : Blo 1028606 1159825 := bbase (se 2 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 1159825 = 869869) (by norm_num)
theorem B1159861 : Blo 1028606 1159861 := bbase (se 5 (by rfl) ⟨54368, by rfl⟩ : syracuseStep 1159861 = 108737) (by norm_num)
theorem B1159897 : Blo 1028606 1159897 := bbase (se 2 (by rfl) ⟨434961, by rfl⟩ : syracuseStep 1159897 = 869923) (by norm_num)
theorem B3912421 : Blo 1028606 3912421 := bbase (se 4 (by rfl) ⟨366789, by rfl⟩ : syracuseStep 3912421 = 733579) (by norm_num)
theorem B1159933 : Blo 1028606 1159933 := bbase (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) (by norm_num)
theorem B1159969 : Blo 1028606 1159969 := bbase (se 2 (by rfl) ⟨434988, by rfl⟩ : syracuseStep 1159969 = 869977) (by norm_num)
theorem B1160005 : Blo 1028606 1160005 := bbase (se 4 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 1160005 = 217501) (by norm_num)
theorem B1160041 : Blo 1028606 1160041 := bbase (se 2 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 1160041 = 870031) (by norm_num)
theorem B1160077 : Blo 1028606 1160077 := bbase (se 3 (by rfl) ⟨217514, by rfl⟩ : syracuseStep 1160077 = 435029) (by norm_num)
theorem B1160113 : Blo 1028606 1160113 := bbase (se 2 (by rfl) ⟨435042, by rfl⟩ : syracuseStep 1160113 = 870085) (by norm_num)
theorem B5223365 : Blo 1028606 5223365 := bbase (se 4 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 5223365 = 979381) (by norm_num)
theorem B1160149 : Blo 1028606 1160149 := bbase (se 7 (by rfl) ⟨13595, by rfl⟩ : syracuseStep 1160149 = 27191) (by norm_num)
theorem B1160185 : Blo 1028606 1160185 := bbase (se 2 (by rfl) ⟨435069, by rfl⟩ : syracuseStep 1160185 = 870139) (by norm_num)
theorem B3912725 : Blo 1028606 3912725 := bbase (se 6 (by rfl) ⟨91704, by rfl⟩ : syracuseStep 3912725 = 183409) (by norm_num)
theorem B1160221 : Blo 1028606 1160221 := bbase (se 3 (by rfl) ⟨217541, by rfl⟩ : syracuseStep 1160221 = 435083) (by norm_num)
theorem B1160257 : Blo 1028606 1160257 := bbase (se 2 (by rfl) ⟨435096, by rfl⟩ : syracuseStep 1160257 = 870193) (by norm_num)
theorem B1160293 : Blo 1028606 1160293 := bbase (se 4 (by rfl) ⟨108777, by rfl⟩ : syracuseStep 1160293 = 217555) (by norm_num)
theorem B1160329 : Blo 1028606 1160329 := bbase (se 2 (by rfl) ⟨435123, by rfl⟩ : syracuseStep 1160329 = 870247) (by norm_num)
theorem B1160365 : Blo 1028606 1160365 := bbase (se 3 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 1160365 = 435137) (by norm_num)
theorem B1160401 : Blo 1028606 1160401 := bbase (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) (by norm_num)
theorem B1160437 : Blo 1028606 1160437 := bbase (se 5 (by rfl) ⟨54395, by rfl⟩ : syracuseStep 1160437 = 108791) (by norm_num)
theorem B9385237 : Blo 1028606 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B1160473 : Blo 1028606 1160473 := bbase (se 2 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 1160473 = 870355) (by norm_num)
theorem B1193249 : Blo 1028606 1193249 := bbase (se 2 (by rfl) ⟨447468, by rfl⟩ : syracuseStep 1193249 = 894937) (by norm_num)
theorem B1160509 : Blo 1028606 1160509 := bbase (se 3 (by rfl) ⟨217595, by rfl⟩ : syracuseStep 1160509 = 435191) (by norm_num)
theorem B1160545 : Blo 1028606 1160545 := bbase (se 2 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 1160545 = 870409) (by norm_num)
theorem B1160581 : Blo 1028606 1160581 := bbase (se 4 (by rfl) ⟨108804, by rfl⟩ : syracuseStep 1160581 = 217609) (by norm_num)
theorem B1160617 : Blo 1028606 1160617 := bbase (se 2 (by rfl) ⟨435231, by rfl⟩ : syracuseStep 1160617 = 870463) (by norm_num)
theorem B1160653 : Blo 1028606 1160653 := bbase (se 3 (by rfl) ⟨217622, by rfl⟩ : syracuseStep 1160653 = 435245) (by norm_num)
theorem B1160689 : Blo 1028606 1160689 := bbase (se 2 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 1160689 = 870517) (by norm_num)
theorem B1160725 : Blo 1028606 1160725 := bbase (se 6 (by rfl) ⟨27204, by rfl⟩ : syracuseStep 1160725 = 54409) (by norm_num)
theorem B1160761 : Blo 1028606 1160761 := bbase (se 2 (by rfl) ⟨435285, by rfl⟩ : syracuseStep 1160761 = 870571) (by norm_num)
theorem B1160797 : Blo 1028606 1160797 := bbase (se 3 (by rfl) ⟨217649, by rfl⟩ : syracuseStep 1160797 = 435299) (by norm_num)
theorem B2471525 : Blo 1028606 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B1390189 : Blo 1028606 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B1160833 : Blo 1028606 1160833 := bbase (se 2 (by rfl) ⟨435312, by rfl⟩ : syracuseStep 1160833 = 870625) (by norm_num)
theorem B1160869 : Blo 1028606 1160869 := bbase (se 4 (by rfl) ⟨108831, by rfl⟩ : syracuseStep 1160869 = 217663) (by norm_num)
theorem B1160905 : Blo 1028606 1160905 := bbase (se 2 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 1160905 = 870679) (by norm_num)
theorem B1160941 : Blo 1028606 1160941 := bbase (se 3 (by rfl) ⟨217676, by rfl⟩ : syracuseStep 1160941 = 435353) (by norm_num)
theorem B1160977 : Blo 1028606 1160977 := bbase (se 2 (by rfl) ⟨435366, by rfl⟩ : syracuseStep 1160977 = 870733) (by norm_num)
theorem B4405013 : Blo 1028606 4405013 := bbase (se 6 (by rfl) ⟨103242, by rfl⟩ : syracuseStep 4405013 = 206485) (by norm_num)
theorem B1652501 : Blo 1028606 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B2471717 : Blo 1028606 2471717 := bbase (se 4 (by rfl) ⟨231723, by rfl⟩ : syracuseStep 2471717 = 463447) (by norm_num)
theorem B1161013 : Blo 1028606 1161013 := bbase (se 5 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 1161013 = 108845) (by norm_num)
theorem B1161049 : Blo 1028606 1161049 := bbase (se 2 (by rfl) ⟨435393, by rfl⟩ : syracuseStep 1161049 = 870787) (by norm_num)
theorem B1161085 : Blo 1028606 1161085 := bbase (se 3 (by rfl) ⟨217703, by rfl⟩ : syracuseStep 1161085 = 435407) (by norm_num)
theorem B1161121 : Blo 1028606 1161121 := bbase (se 2 (by rfl) ⟨435420, by rfl⟩ : syracuseStep 1161121 = 870841) (by norm_num)
theorem B1161157 : Blo 1028606 1161157 := bbase (se 4 (by rfl) ⟨108858, by rfl⟩ : syracuseStep 1161157 = 217717) (by norm_num)
theorem B1161193 : Blo 1028606 1161193 := bbase (se 2 (by rfl) ⟨435447, by rfl⟩ : syracuseStep 1161193 = 870895) (by norm_num)
theorem B1161229 : Blo 1028606 1161229 := bbase (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) (by norm_num)
theorem B1161265 : Blo 1028606 1161265 := bbase (se 2 (by rfl) ⟨435474, by rfl⟩ : syracuseStep 1161265 = 870949) (by norm_num)
theorem B2472005 : Blo 1028606 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B1161301 : Blo 1028606 1161301 := bbase (se 8 (by rfl) ⟨6804, by rfl⟩ : syracuseStep 1161301 = 13609) (by norm_num)
theorem B1161337 : Blo 1028606 1161337 := bbase (se 2 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 1161337 = 871003) (by norm_num)
theorem B1161373 : Blo 1028606 1161373 := bbase (se 3 (by rfl) ⟨217757, by rfl⟩ : syracuseStep 1161373 = 435515) (by norm_num)
theorem B1161409 : Blo 1028606 1161409 := bbase (se 2 (by rfl) ⟨435528, by rfl⟩ : syracuseStep 1161409 = 871057) (by norm_num)
theorem B5224661 : Blo 1028606 5224661 := bbase (se 7 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 5224661 = 122453) (by norm_num)
theorem B1652957 : Blo 1028606 1652957 := bbase (se 3 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 1652957 = 619859) (by norm_num)
theorem B1161445 : Blo 1028606 1161445 := bbase (se 4 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 1161445 = 217771) (by norm_num)
theorem B1128701 : Blo 1028606 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B1161481 : Blo 1028606 1161481 := bbase (se 2 (by rfl) ⟨435555, by rfl⟩ : syracuseStep 1161481 = 871111) (by norm_num)
theorem B1161517 : Blo 1028606 1161517 := bbase (se 3 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 1161517 = 435569) (by norm_num)
theorem B1161553 : Blo 1028606 1161553 := bbase (se 2 (by rfl) ⟨435582, by rfl⟩ : syracuseStep 1161553 = 871165) (by norm_num)
theorem B1161589 : Blo 1028606 1161589 := bbase (se 5 (by rfl) ⟨54449, by rfl⟩ : syracuseStep 1161589 = 108899) (by norm_num)
theorem B1161625 : Blo 1028606 1161625 := bbase (se 2 (by rfl) ⟨435609, by rfl⟩ : syracuseStep 1161625 = 871219) (by norm_num)
theorem B1161661 : Blo 1028606 1161661 := bbase (se 3 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 1161661 = 435623) (by norm_num)
theorem B2931173 : Blo 1028606 2931173 := bbase (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) (by norm_num)
theorem B1391141 : Blo 1028606 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B1391293 : Blo 1028606 1391293 := bbase (se 3 (by rfl) ⟨260867, by rfl⟩ : syracuseStep 1391293 = 521735) (by norm_num)
theorem B1784533 : Blo 1028606 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B2603765 : Blo 1028606 2603765 := bbase (se 5 (by rfl) ⟨122051, by rfl⟩ : syracuseStep 2603765 = 244103) (by norm_num)
theorem B4406021 : Blo 1028606 4406021 := bbase (se 4 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 4406021 = 826129) (by norm_num)
theorem B1391509 : Blo 1028606 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B1391573 : Blo 1028606 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B2604109 : Blo 1028606 2604109 := bbase (se 3 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 2604109 = 976541) (by norm_num)
theorem B3914837 : Blo 1028606 3914837 := bbase (se 8 (by rfl) ⟨22938, by rfl⟩ : syracuseStep 3914837 = 45877) (by norm_num)
theorem B2604221 : Blo 1028606 2604221 := bbase (se 3 (by rfl) ⟨488291, by rfl⟩ : syracuseStep 2604221 = 976583) (by norm_num)
theorem B1653949 : Blo 1028606 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B1981669 : Blo 1028606 1981669 := bbase (se 4 (by rfl) ⟨185781, by rfl⟩ : syracuseStep 1981669 = 371563) (by norm_num)
theorem B3915125 : Blo 1028606 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B2604413 : Blo 1028606 2604413 := bbase (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) (by norm_num)
theorem B5225957 : Blo 1028606 5225957 := bbase (se 4 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 5225957 = 979867) (by norm_num)
theorem B2932357 : Blo 1028606 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B6274709 : Blo 1028606 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B2604757 : Blo 1028606 2604757 := bbase (se 7 (by rfl) ⟨30524, by rfl⟩ : syracuseStep 2604757 = 61049) (by norm_num)
theorem B2932517 : Blo 1028606 2932517 := bbase (se 4 (by rfl) ⟨274923, by rfl⟩ : syracuseStep 2932517 = 549847) (by norm_num)
theorem B2604869 : Blo 1028606 2604869 := bbase (se 4 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 2604869 = 488413) (by norm_num)
theorem B2178893 : Blo 1028606 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B1392493 : Blo 1028606 1392493 := bbase (se 3 (by rfl) ⟨261092, by rfl⟩ : syracuseStep 1392493 = 522185) (by norm_num)
theorem B8798165 : Blo 1028606 8798165 := bbase (se 7 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 8798165 = 206207) (by norm_num)
theorem B2605061 : Blo 1028606 2605061 := bbase (se 4 (by rfl) ⟨244224, by rfl⟩ : syracuseStep 2605061 = 488449) (by norm_num)
theorem B2932757 : Blo 1028606 2932757 := bbase (se 6 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 2932757 = 137473) (by norm_num)
theorem B2932949 : Blo 1028606 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B2605405 : Blo 1028606 2605405 := bbase (se 3 (by rfl) ⟨488513, by rfl⟩ : syracuseStep 2605405 = 977027) (by norm_num)
theorem B2113997 : Blo 1028606 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B2605517 : Blo 1028606 2605517 := bbase (se 3 (by rfl) ⟨488534, by rfl⟩ : syracuseStep 2605517 = 977069) (by norm_num)
theorem B4407797 : Blo 1028606 4407797 := bbase (se 5 (by rfl) ⟨206615, by rfl⟩ : syracuseStep 4407797 = 413231) (by norm_num)
theorem B3916309 : Blo 1028606 3916309 := bbase (se 6 (by rfl) ⟨91788, by rfl⟩ : syracuseStep 3916309 = 183577) (by norm_num)
theorem B2605709 : Blo 1028606 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B1131157 : Blo 1028606 1131157 := bbase (se 6 (by rfl) ⟨26511, by rfl⟩ : syracuseStep 1131157 = 53023) (by norm_num)
theorem B5227253 : Blo 1028606 5227253 := bbase (se 5 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 5227253 = 490055) (by norm_num)
theorem B3916613 : Blo 1028606 3916613 := bbase (se 4 (by rfl) ⟨367182, by rfl⟩ : syracuseStep 3916613 = 734365) (by norm_num)
theorem B20071253 : Blo 1028606 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B2606053 : Blo 1028606 2606053 := bbase (se 4 (by rfl) ⟨244317, by rfl⟩ : syracuseStep 2606053 = 488635) (by norm_num)
theorem B1098793 : Blo 1028606 1098793 := bbase (se 2 (by rfl) ⟨412047, by rfl⟩ : syracuseStep 1098793 = 824095) (by norm_num)
theorem B2606165 : Blo 1028606 2606165 := bbase (se 8 (by rfl) ⟨15270, by rfl⟩ : syracuseStep 2606165 = 30541) (by norm_num)
theorem B1098865 : Blo 1028606 1098865 := bbase (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) (by norm_num)
theorem B2933941 : Blo 1028606 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1393861 : Blo 1028606 1393861 := bbase (se 4 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 1393861 = 261349) (by norm_num)
theorem B3720421 : Blo 1028606 3720421 := bbase (se 4 (by rfl) ⟨348789, by rfl⟩ : syracuseStep 3720421 = 697579) (by norm_num)
theorem B1885421 : Blo 1028606 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1983733 : Blo 1028606 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B2606357 : Blo 1028606 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B1099045 : Blo 1028606 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B2475445 : Blo 1028606 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B28231253 : Blo 1028606 28231253 := bbase (se 8 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 28231253 = 330835) (by norm_num)
theorem B2606701 : Blo 1028606 2606701 := bbase (se 3 (by rfl) ⟨488756, by rfl⟩ : syracuseStep 2606701 = 977513) (by norm_num)
theorem B2475677 : Blo 1028606 2475677 := bbase (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) (by norm_num)
theorem B2606813 : Blo 1028606 2606813 := bbase (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) (by norm_num)
theorem B1099489 : Blo 1028606 1099489 := bbase (se 2 (by rfl) ⟨412308, by rfl⟩ : syracuseStep 1099489 = 824617) (by norm_num)
theorem B2475821 : Blo 1028606 2475821 := bbase (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) (by norm_num)
theorem B1099613 : Blo 1028606 1099613 := bbase (se 3 (by rfl) ⟨206177, by rfl⟩ : syracuseStep 1099613 = 412355) (by norm_num)
theorem B4179845 : Blo 1028606 4179845 := bbase (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) (by norm_num)
theorem B2607005 : Blo 1028606 2607005 := bbase (se 3 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 2607005 = 977627) (by norm_num)
theorem B4769813 : Blo 1028606 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B2476061 : Blo 1028606 2476061 := bbase (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) (by norm_num)
theorem B1099865 : Blo 1028606 1099865 := bbase (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) (by norm_num)
theorem B2607349 : Blo 1028606 2607349 := bbase (se 5 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 2607349 = 244439) (by norm_num)
theorem B2935045 : Blo 1028606 2935045 := bbase (se 4 (by rfl) ⟨275160, by rfl⟩ : syracuseStep 2935045 = 550321) (by norm_num)
theorem B1395029 : Blo 1028606 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B2607461 : Blo 1028606 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B19843541 : Blo 1028606 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B1100309 : Blo 1028606 1100309 := bbase (se 6 (by rfl) ⟨25788, by rfl⟩ : syracuseStep 1100309 = 51577) (by norm_num)
theorem B2607653 : Blo 1028606 2607653 := bbase (se 4 (by rfl) ⟨244467, by rfl⟩ : syracuseStep 2607653 = 488935) (by norm_num)
theorem B1395245 : Blo 1028606 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B1100557 : Blo 1028606 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B2476829 : Blo 1028606 2476829 := bbase (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) (by norm_num)
theorem B2607997 : Blo 1028606 2607997 := bbase (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) (by norm_num)
theorem B3230597 : Blo 1028606 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B3918725 : Blo 1028606 3918725 := bbase (se 4 (by rfl) ⟨367380, by rfl⟩ : syracuseStep 3918725 = 734761) (by norm_num)
theorem B2608109 : Blo 1028606 2608109 := bbase (se 3 (by rfl) ⟨489020, by rfl⟩ : syracuseStep 2608109 = 978041) (by norm_num)
theorem B1952885 : Blo 1028606 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B3919013 : Blo 1028606 3919013 := bbase (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) (by norm_num)
theorem B2608301 : Blo 1028606 2608301 := bbase (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) (by norm_num)
theorem B1101001 : Blo 1028606 1101001 := bbase (se 2 (by rfl) ⟨412875, by rfl⟩ : syracuseStep 1101001 = 825751) (by norm_num)
theorem B1101061 : Blo 1028606 1101061 := bbase (se 4 (by rfl) ⟨103224, by rfl⟩ : syracuseStep 1101061 = 206449) (by norm_num)
theorem B2346301 : Blo 1028606 2346301 := bbase (se 3 (by rfl) ⟨439931, by rfl⟩ : syracuseStep 2346301 = 879863) (by norm_num)
theorem B1953173 : Blo 1028606 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B2608645 : Blo 1028606 2608645 := bbase (se 4 (by rfl) ⟨244560, by rfl⟩ : syracuseStep 2608645 = 489121) (by norm_num)
theorem B1953325 : Blo 1028606 1953325 := bbase (se 3 (by rfl) ⟨366248, by rfl⟩ : syracuseStep 1953325 = 732497) (by norm_num)
theorem B1101377 : Blo 1028606 1101377 := bbase (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) (by norm_num)
theorem B2608757 : Blo 1028606 2608757 := bbase (se 5 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 2608757 = 244571) (by norm_num)
theorem B1855157 : Blo 1028606 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B6606517 : Blo 1028606 6606517 := bbase (se 5 (by rfl) ⟨309680, by rfl⟩ : syracuseStep 6606517 = 619361) (by norm_num)
theorem B2936549 : Blo 1028606 2936549 := bbase (se 4 (by rfl) ⟨275301, by rfl⟩ : syracuseStep 2936549 = 550603) (by norm_num)
theorem B2608949 : Blo 1028606 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B1953629 : Blo 1028606 1953629 := bbase (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) (by norm_num)
theorem B7819253 : Blo 1028606 7819253 := bbase (se 5 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 7819253 = 733055) (by norm_num)
theorem B1101821 : Blo 1028606 1101821 := bbase (se 3 (by rfl) ⟨206591, by rfl⟩ : syracuseStep 1101821 = 413183) (by norm_num)
theorem B1101881 : Blo 1028606 1101881 := bbase (se 2 (by rfl) ⟨413205, by rfl⟩ : syracuseStep 1101881 = 826411) (by norm_num)
theorem B4182101 : Blo 1028606 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B2478205 : Blo 1028606 2478205 := bbase (se 3 (by rfl) ⟨464663, by rfl⟩ : syracuseStep 2478205 = 929327) (by norm_num)
theorem B2609293 : Blo 1028606 2609293 := bbase (se 3 (by rfl) ⟨489242, by rfl⟩ : syracuseStep 2609293 = 978485) (by norm_num)
theorem B1855661 : Blo 1028606 1855661 := bbase (se 3 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 1855661 = 695873) (by norm_num)
theorem B2314421 : Blo 1028606 2314421 := bbase (se 5 (by rfl) ⟨108488, by rfl⟩ : syracuseStep 2314421 = 216977) (by norm_num)
theorem B1102009 : Blo 1028606 1102009 := bbase (se 2 (by rfl) ⟨413253, by rfl⟩ : syracuseStep 1102009 = 826507) (by norm_num)
theorem B2314493 : Blo 1028606 2314493 := bbase (se 3 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 2314493 = 867935) (by norm_num)
theorem B2609405 : Blo 1028606 2609405 := bbase (se 3 (by rfl) ⟨489263, by rfl⟩ : syracuseStep 2609405 = 978527) (by norm_num)
theorem B2314565 : Blo 1028606 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B3920197 : Blo 1028606 3920197 := bbase (se 4 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 3920197 = 735037) (by norm_num)
theorem B2314637 : Blo 1028606 2314637 := bbase (se 3 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 2314637 = 867989) (by norm_num)
theorem B2970037 : Blo 1028606 2970037 := bbase (se 5 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 2970037 = 278441) (by norm_num)
theorem B2609597 : Blo 1028606 2609597 := bbase (se 3 (by rfl) ⟨489299, by rfl⟩ : syracuseStep 2609597 = 978599) (by norm_num)
theorem B2314709 : Blo 1028606 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B2314781 : Blo 1028606 2314781 := bbase (se 3 (by rfl) ⟨434021, by rfl⟩ : syracuseStep 2314781 = 868043) (by norm_num)
theorem B1954381 : Blo 1028606 1954381 := bbase (se 3 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 1954381 = 732893) (by norm_num)
theorem B2314853 : Blo 1028606 2314853 := bbase (se 4 (by rfl) ⟨217017, by rfl⟩ : syracuseStep 2314853 = 434035) (by norm_num)
theorem B1102453 : Blo 1028606 1102453 := bbase (se 5 (by rfl) ⟨51677, by rfl⟩ : syracuseStep 1102453 = 103355) (by norm_num)
theorem B3920501 : Blo 1028606 3920501 := bbase (se 5 (by rfl) ⟨183773, by rfl⟩ : syracuseStep 3920501 = 367547) (by norm_num)
theorem B2314925 : Blo 1028606 2314925 := bbase (se 3 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 2314925 = 868097) (by norm_num)
theorem B1954525 : Blo 1028606 1954525 := bbase (se 3 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 1954525 = 732947) (by norm_num)
theorem B1102573 : Blo 1028606 1102573 := bbase (se 3 (by rfl) ⟨206732, by rfl⟩ : syracuseStep 1102573 = 413465) (by norm_num)
theorem B2314997 : Blo 1028606 2314997 := bbase (se 5 (by rfl) ⟨108515, by rfl⟩ : syracuseStep 2314997 = 217031) (by norm_num)
theorem B2609941 : Blo 1028606 2609941 := bbase (se 6 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 2609941 = 122341) (by norm_num)
theorem B4903733 : Blo 1028606 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B2315069 : Blo 1028606 2315069 := bbase (se 3 (by rfl) ⟨434075, by rfl⟩ : syracuseStep 2315069 = 868151) (by norm_num)
theorem B3298133 : Blo 1028606 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B1954685 : Blo 1028606 1954685 := bbase (se 3 (by rfl) ⟨366503, by rfl⟩ : syracuseStep 1954685 = 733007) (by norm_num)
theorem B2315141 : Blo 1028606 2315141 := bbase (se 4 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 2315141 = 434089) (by norm_num)
theorem B2610053 : Blo 1028606 2610053 := bbase (se 4 (by rfl) ⟨244692, by rfl⟩ : syracuseStep 2610053 = 489385) (by norm_num)
theorem B1856405 : Blo 1028606 1856405 := bbase (se 6 (by rfl) ⟨43509, by rfl⟩ : syracuseStep 1856405 = 87019) (by norm_num)
theorem B2315213 : Blo 1028606 2315213 := bbase (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) (by norm_num)
theorem B1954829 : Blo 1028606 1954829 := bbase (se 3 (by rfl) ⟨366530, by rfl⟩ : syracuseStep 1954829 = 733061) (by norm_num)
theorem B2315285 : Blo 1028606 2315285 := bbase (se 6 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 2315285 = 108529) (by norm_num)
theorem B2610245 : Blo 1028606 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B2315357 : Blo 1028606 2315357 := bbase (se 3 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 2315357 = 868259) (by norm_num)
theorem B2315429 : Blo 1028606 2315429 := bbase (se 4 (by rfl) ⟨217071, by rfl⟩ : syracuseStep 2315429 = 434143) (by norm_num)
theorem B3134629 : Blo 1028606 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B2315501 : Blo 1028606 2315501 := bbase (se 3 (by rfl) ⟨434156, by rfl⟩ : syracuseStep 2315501 = 868313) (by norm_num)
theorem B2938133 : Blo 1028606 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B2479405 : Blo 1028606 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B1955117 : Blo 1028606 1955117 := bbase (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) (by norm_num)
theorem B2315573 : Blo 1028606 2315573 := bbase (se 5 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 2315573 = 217085) (by norm_num)
theorem B2315645 : Blo 1028606 2315645 := bbase (se 3 (by rfl) ⟨434183, by rfl⟩ : syracuseStep 2315645 = 868367) (by norm_num)
theorem B2610589 : Blo 1028606 2610589 := bbase (se 3 (by rfl) ⟨489485, by rfl⟩ : syracuseStep 2610589 = 978971) (by norm_num)
theorem B2315717 : Blo 1028606 2315717 := bbase (se 4 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 2315717 = 434197) (by norm_num)
theorem B1955269 : Blo 1028606 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B3134933 : Blo 1028606 3134933 := bbase (se 7 (by rfl) ⟨36737, by rfl⟩ : syracuseStep 3134933 = 73475) (by norm_num)
theorem B2315789 : Blo 1028606 2315789 := bbase (se 3 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 2315789 = 868421) (by norm_num)
theorem B2610701 : Blo 1028606 2610701 := bbase (se 3 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 2610701 = 979013) (by norm_num)
theorem B2315861 : Blo 1028606 2315861 := bbase (se 8 (by rfl) ⟨13569, by rfl⟩ : syracuseStep 2315861 = 27139) (by norm_num)
theorem B2315933 : Blo 1028606 2315933 := bbase (se 3 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 2315933 = 868475) (by norm_num)
theorem B2610893 : Blo 1028606 2610893 := bbase (se 3 (by rfl) ⟨489542, by rfl⟩ : syracuseStep 2610893 = 979085) (by norm_num)
theorem B2316005 : Blo 1028606 2316005 := bbase (se 4 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 2316005 = 434251) (by norm_num)
theorem B1955573 : Blo 1028606 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B2316077 : Blo 1028606 2316077 := bbase (se 3 (by rfl) ⟨434264, by rfl⟩ : syracuseStep 2316077 = 868529) (by norm_num)
theorem B2316149 : Blo 1028606 2316149 := bbase (se 5 (by rfl) ⟨108569, by rfl⟩ : syracuseStep 2316149 = 217139) (by norm_num)
theorem B2381717 : Blo 1028606 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B2480021 : Blo 1028606 2480021 := bbase (se 6 (by rfl) ⟨58125, by rfl⟩ : syracuseStep 2480021 = 116251) (by norm_num)
theorem B2938805 : Blo 1028606 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B2316221 : Blo 1028606 2316221 := bbase (se 3 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 2316221 = 868583) (by norm_num)
theorem B2316293 : Blo 1028606 2316293 := bbase (se 4 (by rfl) ⟨217152, by rfl⟩ : syracuseStep 2316293 = 434305) (by norm_num)
theorem B2611237 : Blo 1028606 2611237 := bbase (se 4 (by rfl) ⟨244803, by rfl⟩ : syracuseStep 2611237 = 489607) (by norm_num)
theorem B2316365 : Blo 1028606 2316365 := bbase (se 3 (by rfl) ⟨434318, by rfl⟩ : syracuseStep 2316365 = 868637) (by norm_num)
theorem B2480213 : Blo 1028606 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B2349157 : Blo 1028606 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B2316437 : Blo 1028606 2316437 := bbase (se 6 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 2316437 = 108583) (by norm_num)
theorem B2611349 : Blo 1028606 2611349 := bbase (se 6 (by rfl) ⟨61203, by rfl⟩ : syracuseStep 2611349 = 122407) (by norm_num)
theorem B2480309 : Blo 1028606 2480309 := bbase (se 5 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 2480309 = 232529) (by norm_num)
theorem B2316509 : Blo 1028606 2316509 := bbase (se 3 (by rfl) ⟨434345, by rfl⟩ : syracuseStep 2316509 = 868691) (by norm_num)
theorem B2087165 : Blo 1028606 2087165 := bbase (se 3 (by rfl) ⟨391343, by rfl⟩ : syracuseStep 2087165 = 782687) (by norm_num)
theorem B2316581 : Blo 1028606 2316581 := bbase (se 4 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 2316581 = 434359) (by norm_num)
theorem B1857853 : Blo 1028606 1857853 := bbase (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) (by norm_num)
theorem B2611541 : Blo 1028606 2611541 := bbase (se 10 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 2611541 = 7651) (by norm_num)
theorem B2939237 : Blo 1028606 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B2316653 : Blo 1028606 2316653 := bbase (se 3 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 2316653 = 868745) (by norm_num)
theorem B1857925 : Blo 1028606 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B8346037 : Blo 1028606 8346037 := bbase (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) (by norm_num)
theorem B2316725 : Blo 1028606 2316725 := bbase (se 5 (by rfl) ⟨108596, by rfl⟩ : syracuseStep 2316725 = 217193) (by norm_num)
theorem B1956325 : Blo 1028606 1956325 := bbase (se 4 (by rfl) ⟨183405, by rfl⟩ : syracuseStep 1956325 = 366811) (by norm_num)
theorem B2316797 : Blo 1028606 2316797 := bbase (se 3 (by rfl) ⟨434399, by rfl⟩ : syracuseStep 2316797 = 868799) (by norm_num)
theorem B4184581 : Blo 1028606 4184581 := bbase (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) (by norm_num)
theorem B2316869 : Blo 1028606 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B1956469 : Blo 1028606 1956469 := bbase (se 5 (by rfl) ⟨91709, by rfl⟩ : syracuseStep 1956469 = 183419) (by norm_num)
theorem B2382461 : Blo 1028606 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B2316941 : Blo 1028606 2316941 := bbase (se 3 (by rfl) ⟨434426, by rfl⟩ : syracuseStep 2316941 = 868853) (by norm_num)
theorem B1432205 : Blo 1028606 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B2611885 : Blo 1028606 2611885 := bbase (se 3 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 2611885 = 979457) (by norm_num)
theorem B2317013 : Blo 1028606 2317013 := bbase (se 7 (by rfl) ⟨27152, by rfl⟩ : syracuseStep 2317013 = 54305) (by norm_num)
theorem B1465085 : Blo 1028606 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B1956629 : Blo 1028606 1956629 := bbase (se 6 (by rfl) ⟨45858, by rfl⟩ : syracuseStep 1956629 = 91717) (by norm_num)
theorem B2317085 : Blo 1028606 2317085 := bbase (se 3 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 2317085 = 868907) (by norm_num)
theorem B2611997 : Blo 1028606 2611997 := bbase (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) (by norm_num)
theorem B1465165 : Blo 1028606 1465165 := bbase (se 3 (by rfl) ⟨274718, by rfl⟩ : syracuseStep 1465165 = 549437) (by norm_num)
theorem B2317157 : Blo 1028606 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B1858429 : Blo 1028606 1858429 := bbase (se 3 (by rfl) ⟨348455, by rfl⟩ : syracuseStep 1858429 = 696911) (by norm_num)
theorem B1956773 : Blo 1028606 1956773 := bbase (se 4 (by rfl) ⟨183447, by rfl⟩ : syracuseStep 1956773 = 366895) (by norm_num)
theorem B2317229 : Blo 1028606 2317229 := bbase (se 3 (by rfl) ⟨434480, by rfl⟩ : syracuseStep 2317229 = 868961) (by norm_num)
theorem B1465285 : Blo 1028606 1465285 := bbase (se 4 (by rfl) ⟨137370, by rfl⟩ : syracuseStep 1465285 = 274741) (by norm_num)
theorem B4709333 : Blo 1028606 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B2612189 : Blo 1028606 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B2317301 : Blo 1028606 2317301 := bbase (se 5 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 2317301 = 217247) (by norm_num)
theorem B1465381 : Blo 1028606 1465381 := bbase (se 4 (by rfl) ⟨137379, by rfl⟩ : syracuseStep 1465381 = 274759) (by norm_num)
theorem B3300389 : Blo 1028606 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B2317373 : Blo 1028606 2317373 := bbase (se 3 (by rfl) ⟨434507, by rfl⟩ : syracuseStep 2317373 = 869015) (by norm_num)
theorem B2939989 : Blo 1028606 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B1236065 : Blo 1028606 1236065 := bbase (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) (by norm_num)
theorem B2317445 : Blo 1028606 2317445 := bbase (se 4 (by rfl) ⟨217260, by rfl⟩ : syracuseStep 2317445 = 434521) (by norm_num)
theorem B3300517 : Blo 1028606 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B1957061 : Blo 1028606 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B2317517 : Blo 1028606 2317517 := bbase (se 3 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 2317517 = 869069) (by norm_num)
theorem B2317589 : Blo 1028606 2317589 := bbase (se 6 (by rfl) ⟨54318, by rfl⟩ : syracuseStep 2317589 = 108637) (by norm_num)
theorem B2612533 : Blo 1028606 2612533 := bbase (se 5 (by rfl) ⟨122462, by rfl⟩ : syracuseStep 2612533 = 244925) (by norm_num)
theorem B25058645 : Blo 1028606 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B2317661 : Blo 1028606 2317661 := bbase (se 3 (by rfl) ⟨434561, by rfl⟩ : syracuseStep 2317661 = 869123) (by norm_num)
theorem B1957213 : Blo 1028606 1957213 := bbase (se 3 (by rfl) ⟨366977, by rfl⟩ : syracuseStep 1957213 = 733955) (by norm_num)
theorem B1564037 : Blo 1028606 1564037 := bbase (se 4 (by rfl) ⟨146628, by rfl⟩ : syracuseStep 1564037 = 293257) (by norm_num)
theorem B2350469 : Blo 1028606 2350469 := bbase (se 4 (by rfl) ⟨220356, by rfl⟩ : syracuseStep 2350469 = 440713) (by norm_num)
theorem B2317733 : Blo 1028606 2317733 := bbase (se 4 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 2317733 = 434575) (by norm_num)
theorem B2612645 : Blo 1028606 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B1301933 : Blo 1028606 1301933 := bbase (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) (by norm_num)
theorem B1236397 : Blo 1028606 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B7232981 : Blo 1028606 7232981 := bbase (se 7 (by rfl) ⟨84761, by rfl⟩ : syracuseStep 7232981 = 169523) (by norm_num)
theorem B1301989 : Blo 1028606 1301989 := bbase (se 4 (by rfl) ⟨122061, by rfl⟩ : syracuseStep 1301989 = 244123) (by norm_num)
theorem B2317805 : Blo 1028606 2317805 := bbase (se 3 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 2317805 = 869177) (by norm_num)
theorem B1072649 : Blo 1028606 1072649 := bbase (se 2 (by rfl) ⟨402243, by rfl⟩ : syracuseStep 1072649 = 804487) (by norm_num)
theorem B1465877 : Blo 1028606 1465877 := bbase (se 6 (by rfl) ⟨34356, by rfl⟩ : syracuseStep 1465877 = 68713) (by norm_num)
theorem B1859093 : Blo 1028606 1859093 := bbase (se 6 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 1859093 = 87145) (by norm_num)
theorem B2317877 : Blo 1028606 2317877 := bbase (se 5 (by rfl) ⟨108650, by rfl⟩ : syracuseStep 2317877 = 217301) (by norm_num)
theorem B1236541 : Blo 1028606 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B1302085 : Blo 1028606 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B6610517 : Blo 1028606 6610517 := bbase (se 8 (by rfl) ⟨38733, by rfl⟩ : syracuseStep 6610517 = 77467) (by norm_num)
theorem B2612837 : Blo 1028606 2612837 := bbase (se 4 (by rfl) ⟨244953, by rfl⟩ : syracuseStep 2612837 = 489907) (by norm_num)
theorem B2317949 : Blo 1028606 2317949 := bbase (se 3 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 2317949 = 869231) (by norm_num)
theorem B1957517 : Blo 1028606 1957517 := bbase (se 3 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 1957517 = 734069) (by norm_num)
theorem B2318021 : Blo 1028606 2318021 := bbase (se 4 (by rfl) ⟨217314, by rfl⟩ : syracuseStep 2318021 = 434629) (by norm_num)
theorem B1302257 : Blo 1028606 1302257 := bbase (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) (by norm_num)
theorem B2318093 : Blo 1028606 2318093 := bbase (se 3 (by rfl) ⟨434642, by rfl⟩ : syracuseStep 2318093 = 869285) (by norm_num)
theorem B1302313 : Blo 1028606 1302313 := bbase (se 2 (by rfl) ⟨488367, by rfl⟩ : syracuseStep 1302313 = 976735) (by norm_num)
theorem B2318165 : Blo 1028606 2318165 := bbase (se 9 (by rfl) ⟨6791, by rfl⟩ : syracuseStep 2318165 = 13583) (by norm_num)
theorem B8806229 : Blo 1028606 8806229 := bbase (se 9 (by rfl) ⟨25799, by rfl⟩ : syracuseStep 8806229 = 51599) (by norm_num)
theorem B2088821 : Blo 1028606 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B1302409 : Blo 1028606 1302409 := bbase (se 2 (by rfl) ⟨488403, by rfl⟩ : syracuseStep 1302409 = 976807) (by norm_num)
theorem B2318237 : Blo 1028606 2318237 := bbase (se 3 (by rfl) ⟨434669, by rfl⟩ : syracuseStep 2318237 = 869339) (by norm_num)
theorem B2613181 : Blo 1028606 2613181 := bbase (se 3 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 2613181 = 979943) (by norm_num)
theorem B2088917 : Blo 1028606 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B2318309 : Blo 1028606 2318309 := bbase (se 4 (by rfl) ⟨217341, by rfl⟩ : syracuseStep 2318309 = 434683) (by norm_num)
theorem B1761293 : Blo 1028606 1761293 := bbase (se 3 (by rfl) ⟨330242, by rfl⟩ : syracuseStep 1761293 = 660485) (by norm_num)
theorem B2318381 : Blo 1028606 2318381 := bbase (se 3 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 2318381 = 869393) (by norm_num)
theorem B2613293 : Blo 1028606 2613293 := bbase (se 3 (by rfl) ⟨489992, by rfl⟩ : syracuseStep 2613293 = 979985) (by norm_num)
theorem B1302581 : Blo 1028606 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B1466429 : Blo 1028606 1466429 := bbase (se 3 (by rfl) ⟨274955, by rfl⟩ : syracuseStep 1466429 = 549911) (by norm_num)
theorem B1564741 : Blo 1028606 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B1302637 : Blo 1028606 1302637 := bbase (se 3 (by rfl) ⟨244244, by rfl⟩ : syracuseStep 1302637 = 488489) (by norm_num)
theorem B2318453 : Blo 1028606 2318453 := bbase (se 5 (by rfl) ⟨108677, by rfl⟩ : syracuseStep 2318453 = 217355) (by norm_num)
theorem B2318525 : Blo 1028606 2318525 := bbase (se 3 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 2318525 = 869447) (by norm_num)
theorem B1302733 : Blo 1028606 1302733 := bbase (se 3 (by rfl) ⟨244262, by rfl⟩ : syracuseStep 1302733 = 488525) (by norm_num)
theorem B2613485 : Blo 1028606 2613485 := bbase (se 3 (by rfl) ⟨490028, by rfl⟩ : syracuseStep 2613485 = 980057) (by norm_num)
theorem B2318597 : Blo 1028606 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B2318669 : Blo 1028606 2318669 := bbase (se 3 (by rfl) ⟨434750, by rfl⟩ : syracuseStep 2318669 = 869501) (by norm_num)
theorem B2646373 : Blo 1028606 2646373 := bbase (se 4 (by rfl) ⟨248097, by rfl⟩ : syracuseStep 2646373 = 496195) (by norm_num)
theorem B1302905 : Blo 1028606 1302905 := bbase (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) (by norm_num)
theorem B1958269 : Blo 1028606 1958269 := bbase (se 3 (by rfl) ⟨367175, by rfl⟩ : syracuseStep 1958269 = 734351) (by norm_num)
theorem B2646413 : Blo 1028606 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B2318741 : Blo 1028606 2318741 := bbase (se 6 (by rfl) ⟨54345, by rfl⟩ : syracuseStep 2318741 = 108691) (by norm_num)
theorem B1302961 : Blo 1028606 1302961 := bbase (se 2 (by rfl) ⟨488610, by rfl⟩ : syracuseStep 1302961 = 977221) (by norm_num)
theorem B2318813 : Blo 1028606 2318813 := bbase (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) (by norm_num)
theorem B1958413 : Blo 1028606 1958413 := bbase (se 3 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 1958413 = 734405) (by norm_num)
theorem B1303057 : Blo 1028606 1303057 := bbase (se 2 (by rfl) ⟨488646, by rfl⟩ : syracuseStep 1303057 = 977293) (by norm_num)
theorem B2318885 : Blo 1028606 2318885 := bbase (se 4 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 2318885 = 434791) (by norm_num)
theorem B1237565 : Blo 1028606 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B2318957 : Blo 1028606 2318957 := bbase (se 3 (by rfl) ⟨434804, by rfl⟩ : syracuseStep 2318957 = 869609) (by norm_num)
theorem B1958573 : Blo 1028606 1958573 := bbase (se 3 (by rfl) ⟨367232, by rfl⟩ : syracuseStep 1958573 = 734465) (by norm_num)
theorem B2319029 : Blo 1028606 2319029 := bbase (se 5 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 2319029 = 217409) (by norm_num)
theorem B1303229 : Blo 1028606 1303229 := bbase (se 3 (by rfl) ⟨244355, by rfl⟩ : syracuseStep 1303229 = 488711) (by norm_num)
theorem B1303285 : Blo 1028606 1303285 := bbase (se 5 (by rfl) ⟨61091, by rfl⟩ : syracuseStep 1303285 = 122183) (by norm_num)
theorem B2319101 : Blo 1028606 2319101 := bbase (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) (by norm_num)
theorem B1467181 : Blo 1028606 1467181 := bbase (se 3 (by rfl) ⟨275096, by rfl⟩ : syracuseStep 1467181 = 550193) (by norm_num)
theorem B1958717 : Blo 1028606 1958717 := bbase (se 3 (by rfl) ⟨367259, by rfl⟩ : syracuseStep 1958717 = 734519) (by norm_num)
theorem B2319173 : Blo 1028606 2319173 := bbase (se 4 (by rfl) ⟨217422, by rfl⟩ : syracuseStep 2319173 = 434845) (by norm_num)
theorem B1303381 : Blo 1028606 1303381 := bbase (se 9 (by rfl) ⟨3818, by rfl⟩ : syracuseStep 1303381 = 7637) (by norm_num)
theorem B2319245 : Blo 1028606 2319245 := bbase (se 3 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 2319245 = 869717) (by norm_num)
theorem B2319317 : Blo 1028606 2319317 := bbase (se 7 (by rfl) ⟨27179, by rfl⟩ : syracuseStep 2319317 = 54359) (by norm_num)
theorem B1303553 : Blo 1028606 1303553 := bbase (se 2 (by rfl) ⟨488832, by rfl⟩ : syracuseStep 1303553 = 977665) (by norm_num)
theorem B2319389 : Blo 1028606 2319389 := bbase (se 3 (by rfl) ⟨434885, by rfl⟩ : syracuseStep 2319389 = 869771) (by norm_num)
theorem B1303609 : Blo 1028606 1303609 := bbase (se 2 (by rfl) ⟨488853, by rfl⟩ : syracuseStep 1303609 = 977707) (by norm_num)
theorem B1959005 : Blo 1028606 1959005 := bbase (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) (by norm_num)
theorem B2319461 : Blo 1028606 2319461 := bbase (se 4 (by rfl) ⟨217449, by rfl⟩ : syracuseStep 2319461 = 434899) (by norm_num)
theorem B1565813 : Blo 1028606 1565813 := bbase (se 5 (by rfl) ⟨73397, by rfl⟩ : syracuseStep 1565813 = 146795) (by norm_num)
theorem B1303705 : Blo 1028606 1303705 := bbase (se 2 (by rfl) ⟨488889, by rfl⟩ : syracuseStep 1303705 = 977779) (by norm_num)
theorem B2319533 : Blo 1028606 2319533 := bbase (se 3 (by rfl) ⟨434912, by rfl⟩ : syracuseStep 2319533 = 869825) (by norm_num)
theorem B2319605 : Blo 1028606 2319605 := bbase (se 5 (by rfl) ⟨108731, by rfl⟩ : syracuseStep 2319605 = 217463) (by norm_num)
theorem B1959157 : Blo 1028606 1959157 := bbase (se 5 (by rfl) ⟨91835, by rfl⟩ : syracuseStep 1959157 = 183671) (by norm_num)
theorem B2319677 : Blo 1028606 2319677 := bbase (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) (by norm_num)
theorem B1303877 : Blo 1028606 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B1303933 : Blo 1028606 1303933 := bbase (se 3 (by rfl) ⟨244487, by rfl⟩ : syracuseStep 1303933 = 488975) (by norm_num)
theorem B2319749 : Blo 1028606 2319749 := bbase (se 4 (by rfl) ⟨217476, by rfl⟩ : syracuseStep 2319749 = 434953) (by norm_num)
theorem B2319821 : Blo 1028606 2319821 := bbase (se 3 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 2319821 = 869933) (by norm_num)
theorem B1304029 : Blo 1028606 1304029 := bbase (se 3 (by rfl) ⟨244505, by rfl⟩ : syracuseStep 1304029 = 489011) (by norm_num)
theorem B5858837 : Blo 1028606 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B2319893 : Blo 1028606 2319893 := bbase (se 6 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 2319893 = 108745) (by norm_num)
theorem B1959461 : Blo 1028606 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B1467973 : Blo 1028606 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B2319965 : Blo 1028606 2319965 := bbase (se 3 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 2319965 = 869987) (by norm_num)
theorem B2090605 : Blo 1028606 2090605 := bbase (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) (by norm_num)
theorem B1304201 : Blo 1028606 1304201 := bbase (se 2 (by rfl) ⟨489075, by rfl⟩ : syracuseStep 1304201 = 978151) (by norm_num)
theorem B1566373 : Blo 1028606 1566373 := bbase (se 4 (by rfl) ⟨146847, by rfl⟩ : syracuseStep 1566373 = 293695) (by norm_num)
theorem B2320037 : Blo 1028606 2320037 := bbase (se 4 (by rfl) ⟨217503, by rfl⟩ : syracuseStep 2320037 = 435007) (by norm_num)
theorem B1304257 : Blo 1028606 1304257 := bbase (se 2 (by rfl) ⟨489096, by rfl⟩ : syracuseStep 1304257 = 978193) (by norm_num)
theorem B2090701 : Blo 1028606 2090701 := bbase (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) (by norm_num)
theorem B1238761 : Blo 1028606 1238761 := bbase (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) (by norm_num)
theorem B2320109 : Blo 1028606 2320109 := bbase (se 3 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 2320109 = 870041) (by norm_num)
theorem B1566469 : Blo 1028606 1566469 := bbase (se 4 (by rfl) ⟨146856, by rfl⟩ : syracuseStep 1566469 = 293713) (by norm_num)
theorem B1304353 : Blo 1028606 1304353 := bbase (se 2 (by rfl) ⟨489132, by rfl⟩ : syracuseStep 1304353 = 978265) (by norm_num)
theorem B1238833 : Blo 1028606 1238833 := bbase (se 2 (by rfl) ⟨464562, by rfl⟩ : syracuseStep 1238833 = 929125) (by norm_num)
theorem B2320181 : Blo 1028606 2320181 := bbase (se 5 (by rfl) ⟨108758, by rfl⟩ : syracuseStep 2320181 = 217517) (by norm_num)
theorem B2320253 : Blo 1028606 2320253 := bbase (se 3 (by rfl) ⟨435047, by rfl⟩ : syracuseStep 2320253 = 870095) (by norm_num)
theorem B1468309 : Blo 1028606 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B2975669 : Blo 1028606 2975669 := bbase (se 5 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 2975669 = 278969) (by norm_num)
theorem B2320325 : Blo 1028606 2320325 := bbase (se 4 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 2320325 = 435061) (by norm_num)
theorem B1304525 : Blo 1028606 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B3303413 : Blo 1028606 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B1304581 : Blo 1028606 1304581 := bbase (se 4 (by rfl) ⟨122304, by rfl⟩ : syracuseStep 1304581 = 244609) (by norm_num)
theorem B2320397 : Blo 1028606 2320397 := bbase (se 3 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 2320397 = 870149) (by norm_num)
theorem B2320469 : Blo 1028606 2320469 := bbase (se 8 (by rfl) ⟨13596, by rfl⟩ : syracuseStep 2320469 = 27193) (by norm_num)
theorem B1304677 : Blo 1028606 1304677 := bbase (se 4 (by rfl) ⟨122313, by rfl⟩ : syracuseStep 1304677 = 244627) (by norm_num)
theorem B1468525 : Blo 1028606 1468525 := bbase (se 3 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 1468525 = 550697) (by norm_num)
theorem B2320541 : Blo 1028606 2320541 := bbase (se 3 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 2320541 = 870203) (by norm_num)
theorem B1173685 : Blo 1028606 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B2320613 : Blo 1028606 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B2091253 : Blo 1028606 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B1304849 : Blo 1028606 1304849 := bbase (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) (by norm_num)
theorem B1960213 : Blo 1028606 1960213 := bbase (se 6 (by rfl) ⟨45942, by rfl⟩ : syracuseStep 1960213 = 91885) (by norm_num)
theorem B2320685 : Blo 1028606 2320685 := bbase (se 3 (by rfl) ⟨435128, by rfl⟩ : syracuseStep 2320685 = 870257) (by norm_num)
theorem B2091317 : Blo 1028606 2091317 := bbase (se 5 (by rfl) ⟨98030, by rfl⟩ : syracuseStep 2091317 = 196061) (by norm_num)
theorem B1173821 : Blo 1028606 1173821 := bbase (se 3 (by rfl) ⟨220091, by rfl⟩ : syracuseStep 1173821 = 440183) (by norm_num)
theorem B1304905 : Blo 1028606 1304905 := bbase (se 2 (by rfl) ⟨489339, by rfl⟩ : syracuseStep 1304905 = 978679) (by norm_num)
theorem B2320757 : Blo 1028606 2320757 := bbase (se 5 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 2320757 = 217571) (by norm_num)
theorem B1305001 : Blo 1028606 1305001 := bbase (se 2 (by rfl) ⟨489375, by rfl⟩ : syracuseStep 1305001 = 978751) (by norm_num)
theorem B2320829 : Blo 1028606 2320829 := bbase (se 3 (by rfl) ⟨435155, by rfl⟩ : syracuseStep 2320829 = 870311) (by norm_num)
theorem B1468901 : Blo 1028606 1468901 := bbase (se 4 (by rfl) ⟨137709, by rfl⟩ : syracuseStep 1468901 = 275419) (by norm_num)
theorem B2320901 : Blo 1028606 2320901 := bbase (se 4 (by rfl) ⟨217584, by rfl⟩ : syracuseStep 2320901 = 435169) (by norm_num)
theorem B1763893 : Blo 1028606 1763893 := bbase (se 5 (by rfl) ⟨82682, by rfl⟩ : syracuseStep 1763893 = 165365) (by norm_num)
theorem B2320973 : Blo 1028606 2320973 := bbase (se 3 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 2320973 = 870365) (by norm_num)
theorem B1305173 : Blo 1028606 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B1567333 : Blo 1028606 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B1305229 : Blo 1028606 1305229 := bbase (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) (by norm_num)
theorem B2321045 : Blo 1028606 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B1043129 : Blo 1028606 1043129 := bbase (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) (by norm_num)
theorem B2321117 : Blo 1028606 2321117 := bbase (se 3 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 2321117 = 870419) (by norm_num)
theorem B1305325 : Blo 1028606 1305325 := bbase (se 3 (by rfl) ⟨244748, by rfl⟩ : syracuseStep 1305325 = 489497) (by norm_num)
theorem B1239833 : Blo 1028606 1239833 := bbase (se 2 (by rfl) ⟨464937, by rfl⟩ : syracuseStep 1239833 = 929875) (by norm_num)
theorem B2321189 : Blo 1028606 2321189 := bbase (se 4 (by rfl) ⟨217611, by rfl⟩ : syracuseStep 2321189 = 435223) (by norm_num)
theorem B2321261 : Blo 1028606 2321261 := bbase (se 3 (by rfl) ⟨435236, by rfl⟩ : syracuseStep 2321261 = 870473) (by norm_num)
theorem B2091901 : Blo 1028606 2091901 := bbase (se 3 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 2091901 = 784463) (by norm_num)
theorem B1305497 : Blo 1028606 1305497 := bbase (se 2 (by rfl) ⟨489561, by rfl⟩ : syracuseStep 1305497 = 979123) (by norm_num)
theorem B2321333 : Blo 1028606 2321333 := bbase (se 5 (by rfl) ⟨108812, by rfl⟩ : syracuseStep 2321333 = 217625) (by norm_num)
theorem B1043389 : Blo 1028606 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B1305553 : Blo 1028606 1305553 := bbase (se 2 (by rfl) ⟨489582, by rfl⟩ : syracuseStep 1305553 = 979165) (by norm_num)
theorem B1043449 : Blo 1028606 1043449 := bbase (se 2 (by rfl) ⟨391293, by rfl⟩ : syracuseStep 1043449 = 782587) (by norm_num)
theorem B2321405 : Blo 1028606 2321405 := bbase (se 3 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 2321405 = 870527) (by norm_num)
theorem B1305649 : Blo 1028606 1305649 := bbase (se 2 (by rfl) ⟨489618, by rfl⟩ : syracuseStep 1305649 = 979237) (by norm_num)
theorem B2386997 : Blo 1028606 2386997 := bbase (se 5 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 2386997 = 223781) (by norm_num)
theorem B2321477 : Blo 1028606 2321477 := bbase (se 4 (by rfl) ⟨217638, by rfl⟩ : syracuseStep 2321477 = 435277) (by norm_num)
theorem B2354285 : Blo 1028606 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B2321549 : Blo 1028606 2321549 := bbase (se 3 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 2321549 = 870581) (by norm_num)
theorem B2321621 : Blo 1028606 2321621 := bbase (se 7 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 2321621 = 54413) (by norm_num)
theorem B1305821 : Blo 1028606 1305821 := bbase (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) (by norm_num)
theorem B1043713 : Blo 1028606 1043713 := bbase (se 2 (by rfl) ⟨391392, by rfl⟩ : syracuseStep 1043713 = 782785) (by norm_num)
theorem B1305877 : Blo 1028606 1305877 := bbase (se 6 (by rfl) ⟨30606, by rfl⟩ : syracuseStep 1305877 = 61213) (by norm_num)
theorem B2321693 : Blo 1028606 2321693 := bbase (se 3 (by rfl) ⟨435317, by rfl⟩ : syracuseStep 2321693 = 870635) (by norm_num)
theorem B2321765 : Blo 1028606 2321765 := bbase (se 4 (by rfl) ⟨217665, by rfl⟩ : syracuseStep 2321765 = 435331) (by norm_num)
theorem B1305973 : Blo 1028606 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B2321837 : Blo 1028606 2321837 := bbase (se 3 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 2321837 = 870689) (by norm_num)
theorem B1240525 : Blo 1028606 1240525 := bbase (se 3 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 1240525 = 465197) (by norm_num)
theorem B2321909 : Blo 1028606 2321909 := bbase (se 5 (by rfl) ⟨108839, by rfl⟩ : syracuseStep 2321909 = 217679) (by norm_num)
theorem B1306145 : Blo 1028606 1306145 := bbase (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) (by norm_num)
theorem B2321981 : Blo 1028606 2321981 := bbase (se 3 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 2321981 = 870743) (by norm_num)
theorem B7827029 : Blo 1028606 7827029 := bbase (se 8 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 7827029 = 91723) (by norm_num)
theorem B1306201 : Blo 1028606 1306201 := bbase (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) (by norm_num)
theorem B2322053 : Blo 1028606 2322053 := bbase (se 4 (by rfl) ⟨217692, by rfl⟩ : syracuseStep 2322053 = 435385) (by norm_num)
theorem B1306297 : Blo 1028606 1306297 := bbase (se 2 (by rfl) ⟨489861, by rfl⟩ : syracuseStep 1306297 = 979723) (by norm_num)
theorem B2322125 : Blo 1028606 2322125 := bbase (se 3 (by rfl) ⟨435398, by rfl⟩ : syracuseStep 2322125 = 870797) (by norm_num)
theorem B2322197 : Blo 1028606 2322197 := bbase (se 6 (by rfl) ⟨54426, by rfl⟩ : syracuseStep 2322197 = 108853) (by norm_num)
theorem B2322269 : Blo 1028606 2322269 := bbase (se 3 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 2322269 = 870851) (by norm_num)
theorem B1306469 : Blo 1028606 1306469 := bbase (se 4 (by rfl) ⟨122481, by rfl⟩ : syracuseStep 1306469 = 244963) (by norm_num)
theorem B2977669 : Blo 1028606 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1306525 : Blo 1028606 1306525 := bbase (se 3 (by rfl) ⟨244973, by rfl⟩ : syracuseStep 1306525 = 489947) (by norm_num)
theorem B2322341 : Blo 1028606 2322341 := bbase (se 4 (by rfl) ⟨217719, by rfl⟩ : syracuseStep 2322341 = 435439) (by norm_num)
theorem B2322413 : Blo 1028606 2322413 := bbase (se 3 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 2322413 = 870905) (by norm_num)
theorem B1306621 : Blo 1028606 1306621 := bbase (se 3 (by rfl) ⟨244991, by rfl⟩ : syracuseStep 1306621 = 489983) (by norm_num)
theorem B2322485 : Blo 1028606 2322485 := bbase (se 5 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 2322485 = 217733) (by norm_num)
theorem B2322557 : Blo 1028606 2322557 := bbase (se 3 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 2322557 = 870959) (by norm_num)
theorem B3305605 : Blo 1028606 3305605 := bbase (se 4 (by rfl) ⟨309900, by rfl⟩ : syracuseStep 3305605 = 619801) (by norm_num)
theorem B1306793 : Blo 1028606 1306793 := bbase (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) (by norm_num)
theorem B2322629 : Blo 1028606 2322629 := bbase (se 4 (by rfl) ⟨217746, by rfl⟩ : syracuseStep 2322629 = 435493) (by norm_num)
theorem B1306849 : Blo 1028606 1306849 := bbase (se 2 (by rfl) ⟨490068, by rfl⟩ : syracuseStep 1306849 = 980137) (by norm_num)
theorem B2322701 : Blo 1028606 2322701 := bbase (se 3 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 2322701 = 871013) (by norm_num)
theorem B2322773 : Blo 1028606 2322773 := bbase (se 10 (by rfl) ⟨3402, by rfl⟩ : syracuseStep 2322773 = 6805) (by norm_num)
theorem B2781589 : Blo 1028606 2781589 := bbase (se 6 (by rfl) ⟨65193, by rfl⟩ : syracuseStep 2781589 = 130387) (by norm_num)
theorem B2322845 : Blo 1028606 2322845 := bbase (se 3 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 2322845 = 871067) (by norm_num)
theorem B2322917 : Blo 1028606 2322917 := bbase (se 4 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 2322917 = 435547) (by norm_num)
theorem B2322989 : Blo 1028606 2322989 := bbase (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) (by norm_num)
theorem B1765973 : Blo 1028606 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B2323061 : Blo 1028606 2323061 := bbase (se 5 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 2323061 = 217787) (by norm_num)
theorem B1569461 : Blo 1028606 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B2323133 : Blo 1028606 2323133 := bbase (se 3 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 2323133 = 871175) (by norm_num)
theorem B7533269 : Blo 1028606 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B2323205 : Blo 1028606 2323205 := bbase (se 4 (by rfl) ⟨217800, by rfl⟩ : syracuseStep 2323205 = 435601) (by norm_num)
theorem B2323277 : Blo 1028606 2323277 := bbase (se 3 (by rfl) ⟨435614, by rfl⟩ : syracuseStep 2323277 = 871229) (by norm_num)
theorem B2323349 : Blo 1028606 2323349 := bbase (se 6 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 2323349 = 108907) (by norm_num)
theorem B3306437 : Blo 1028606 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B1569797 : Blo 1028606 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B1569845 : Blo 1028606 1569845 := bbase (se 5 (by rfl) ⟨73586, by rfl⟩ : syracuseStep 1569845 = 147173) (by norm_num)
theorem B1046081 : Blo 1028606 1046081 := bbase (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) (by norm_num)
theorem B5732021 : Blo 1028606 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B5207813 : Blo 1028606 5207813 := bbase (se 4 (by rfl) ⟨488232, by rfl⟩ : syracuseStep 5207813 = 976465) (by norm_num)
theorem B1046405 : Blo 1028606 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B11761685 : Blo 1028606 11761685 := bbase (se 6 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 11761685 = 551329) (by norm_num)
theorem B2783429 : Blo 1028606 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B3471605 : Blo 1028606 3471605 := bbase (se 5 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 3471605 = 325463) (by norm_num)
theorem B3472037 : Blo 1028606 3472037 := bbase (se 4 (by rfl) ⟨325503, by rfl⟩ : syracuseStep 3472037 = 651007) (by norm_num)
theorem B16743125 : Blo 1028606 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B4946933 : Blo 1028606 4946933 := bbase (se 5 (by rfl) ⟨231887, by rfl⟩ : syracuseStep 4946933 = 463775) (by norm_num)
theorem B5209109 : Blo 1028606 5209109 := bbase (se 6 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 5209109 = 244177) (by norm_num)
theorem B3472469 : Blo 1028606 3472469 := bbase (se 8 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 3472469 = 40693) (by norm_num)
theorem B1735789 : Blo 1028606 1735789 := bbase (se 3 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 1735789 = 650921) (by norm_num)
theorem B1735877 : Blo 1028606 1735877 := bbase (se 4 (by rfl) ⟨162738, by rfl⟩ : syracuseStep 1735877 = 325477) (by norm_num)
theorem B1736005 : Blo 1028606 1736005 := bbase (se 4 (by rfl) ⟨162750, by rfl⟩ : syracuseStep 1736005 = 325501) (by norm_num)
theorem B1670501 : Blo 1028606 1670501 := bbase (se 4 (by rfl) ⟨156609, by rfl⟩ : syracuseStep 1670501 = 313219) (by norm_num)
theorem B1736093 : Blo 1028606 1736093 := bbase (se 3 (by rfl) ⟨325517, by rfl⟩ : syracuseStep 1736093 = 651035) (by norm_num)
theorem B3472901 : Blo 1028606 3472901 := bbase (se 4 (by rfl) ⟨325584, by rfl⟩ : syracuseStep 3472901 = 651169) (by norm_num)
theorem B1736221 : Blo 1028606 1736221 := bbase (se 3 (by rfl) ⟨325541, by rfl⟩ : syracuseStep 1736221 = 651083) (by norm_num)
theorem B1736309 : Blo 1028606 1736309 := bbase (se 5 (by rfl) ⟨81389, by rfl⟩ : syracuseStep 1736309 = 162779) (by norm_num)
theorem B1736437 : Blo 1028606 1736437 := bbase (se 5 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 1736437 = 162791) (by norm_num)
theorem B1736525 : Blo 1028606 1736525 := bbase (se 3 (by rfl) ⟨325598, by rfl⟩ : syracuseStep 1736525 = 651197) (by norm_num)
theorem B3473333 : Blo 1028606 3473333 := bbase (se 5 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 3473333 = 325625) (by norm_num)
theorem B1736653 : Blo 1028606 1736653 := bbase (se 3 (by rfl) ⟨325622, by rfl⟩ : syracuseStep 1736653 = 651245) (by norm_num)
theorem B1736707 : Blo 1028606 1736707 := bstep (se 1 (by rfl) ⟨1302530, by rfl⟩ : syracuseStep 1736707 = 2605061) B2605061
theorem B3473549 : Blo 1028606 3473549 := bstep (se 3 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 3473549 = 1302581) B1302581
theorem B1736849 : Blo 1028606 1736849 := bstep (se 2 (by rfl) ⟨651318, by rfl⟩ : syracuseStep 1736849 = 1302637) B1302637
theorem B3473603 : Blo 1028606 3473603 := bstep (se 1 (by rfl) ⟨2605202, by rfl⟩ : syracuseStep 3473603 = 5210405) B5210405
theorem B1736977 : Blo 1028606 1736977 := bstep (se 2 (by rfl) ⟨651366, by rfl⟩ : syracuseStep 1736977 = 1302733) B1302733
theorem B1737011 : Blo 1028606 1737011 := bstep (se 1 (by rfl) ⟨1302758, by rfl⟩ : syracuseStep 1737011 = 2605517) B2605517
theorem B1737139 : Blo 1028606 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B3473873 : Blo 1028606 3473873 := bstep (se 2 (by rfl) ⟨1302702, by rfl⟩ : syracuseStep 3473873 = 2605405) B2605405
theorem B1737281 : Blo 1028606 1737281 := bstep (se 2 (by rfl) ⟨651480, by rfl⟩ : syracuseStep 1737281 = 1302961) B1302961
theorem B1737409 : Blo 1028606 1737409 := bstep (se 2 (by rfl) ⟨651528, by rfl⟩ : syracuseStep 1737409 = 1303057) B1303057
theorem B1737443 : Blo 1028606 1737443 := bstep (se 1 (by rfl) ⟨1303082, by rfl⟩ : syracuseStep 1737443 = 2606165) B2606165
theorem B1737571 : Blo 1028606 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B5866445 : Blo 1028606 5866445 := bstep (se 3 (by rfl) ⟨1099958, by rfl⟩ : syracuseStep 5866445 = 2199917) B2199917
theorem B3474413 : Blo 1028606 3474413 := bstep (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) B1302905
theorem B1737713 : Blo 1028606 1737713 := bstep (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) B1303285
theorem B3474467 : Blo 1028606 3474467 := bstep (se 1 (by rfl) ⟨2605850, by rfl⟩ : syracuseStep 3474467 = 5211701) B5211701
theorem B1737841 : Blo 1028606 1737841 := bstep (se 2 (by rfl) ⟨651690, by rfl⟩ : syracuseStep 1737841 = 1303381) B1303381
theorem B1737875 : Blo 1028606 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B5637325 : Blo 1028606 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B5211377 : Blo 1028606 5211377 := bstep (se 2 (by rfl) ⟨1954266, by rfl⟩ : syracuseStep 5211377 = 3908533) B3908533
theorem B2786563 : Blo 1028606 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B1738003 : Blo 1028606 1738003 := bstep (se 1 (by rfl) ⟨1303502, by rfl⟩ : syracuseStep 1738003 = 2607005) B2607005
theorem B3474737 : Blo 1028606 3474737 := bstep (se 2 (by rfl) ⟨1303026, by rfl⟩ : syracuseStep 3474737 = 2606053) B2606053
theorem B1738145 : Blo 1028606 1738145 := bstep (se 2 (by rfl) ⟨651804, by rfl⟩ : syracuseStep 1738145 = 1303609) B1303609
theorem B1738273 : Blo 1028606 1738273 := bstep (se 2 (by rfl) ⟨651852, by rfl⟩ : syracuseStep 1738273 = 1303705) B1303705
theorem B1738307 : Blo 1028606 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B1738435 : Blo 1028606 1738435 := bstep (se 1 (by rfl) ⟨1303826, by rfl⟩ : syracuseStep 1738435 = 2607653) B2607653
theorem B2197201 : Blo 1028606 2197201 := bstep (se 2 (by rfl) ⟨823950, by rfl⟩ : syracuseStep 2197201 = 1647901) B1647901
theorem B19793717 : Blo 1028606 19793717 := bstep (se 5 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 19793717 = 1855661) B1855661
theorem B3475277 : Blo 1028606 3475277 := bstep (se 3 (by rfl) ⟨651614, by rfl⟩ : syracuseStep 3475277 = 1303229) B1303229
theorem B1738577 : Blo 1028606 1738577 := bstep (se 2 (by rfl) ⟨651966, by rfl⟩ : syracuseStep 1738577 = 1303933) B1303933
theorem B3475331 : Blo 1028606 3475331 := bstep (se 1 (by rfl) ⟨2606498, by rfl⟩ : syracuseStep 3475331 = 5212997) B5212997
theorem B2197457 : Blo 1028606 2197457 := bstep (se 2 (by rfl) ⟨824046, by rfl⟩ : syracuseStep 2197457 = 1648093) B1648093
theorem B1738705 : Blo 1028606 1738705 := bstep (se 2 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 1738705 = 1304029) B1304029
theorem B1738739 : Blo 1028606 1738739 := bstep (se 1 (by rfl) ⟨1304054, by rfl⟩ : syracuseStep 1738739 = 2608109) B2608109
theorem B17860661 : Blo 1028606 17860661 := bstep (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) B1674437
theorem B1738867 : Blo 1028606 1738867 := bstep (se 1 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 1738867 = 2608301) B2608301
theorem B3475601 : Blo 1028606 3475601 := bstep (se 2 (by rfl) ⟨1303350, by rfl⟩ : syracuseStep 3475601 = 2606701) B2606701
theorem B2787473 : Blo 1028606 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B1739009 : Blo 1028606 1739009 := bstep (se 2 (by rfl) ⟨652128, by rfl⟩ : syracuseStep 1739009 = 1304257) B1304257
theorem B3344717 : Blo 1028606 3344717 := bstep (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) B1254269
theorem B1739137 : Blo 1028606 1739137 := bstep (se 2 (by rfl) ⟨652176, by rfl⟩ : syracuseStep 1739137 = 1304353) B1304353
theorem B1739171 : Blo 1028606 1739171 := bstep (se 1 (by rfl) ⟨1304378, by rfl⟩ : syracuseStep 1739171 = 2608757) B2608757
theorem B1739299 : Blo 1028606 1739299 := bstep (se 1 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 1739299 = 2608949) B2608949
theorem B5212835 : Blo 1028606 5212835 := bstep (se 1 (by rfl) ⟨3909626, by rfl⟩ : syracuseStep 5212835 = 7819253) B7819253
theorem B3476141 : Blo 1028606 3476141 := bstep (se 3 (by rfl) ⟨651776, by rfl⟩ : syracuseStep 3476141 = 1303553) B1303553
theorem B1739441 : Blo 1028606 1739441 := bstep (se 2 (by rfl) ⟨652290, by rfl⟩ : syracuseStep 1739441 = 1304581) B1304581
theorem B3476195 : Blo 1028606 3476195 := bstep (se 1 (by rfl) ⟨2607146, by rfl⟩ : syracuseStep 3476195 = 5214293) B5214293
theorem B2788067 : Blo 1028606 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B1542929 : Blo 1028606 1542929 := bstep (se 2 (by rfl) ⟨578598, by rfl⟩ : syracuseStep 1542929 = 1157197) B1157197
theorem B1542947 : Blo 1028606 1542947 := bstep (se 1 (by rfl) ⟨1157210, by rfl⟩ : syracuseStep 1542947 = 2314421) B2314421
theorem B1739569 : Blo 1028606 1739569 := bstep (se 2 (by rfl) ⟨652338, by rfl⟩ : syracuseStep 1739569 = 1304677) B1304677
theorem B1542977 : Blo 1028606 1542977 := bstep (se 2 (by rfl) ⟨578616, by rfl⟩ : syracuseStep 1542977 = 1157233) B1157233
theorem B1542995 : Blo 1028606 1542995 := bstep (se 1 (by rfl) ⟨1157246, by rfl⟩ : syracuseStep 1542995 = 2314493) B2314493
theorem B1739603 : Blo 1028606 1739603 := bstep (se 1 (by rfl) ⟨1304702, by rfl⟩ : syracuseStep 1739603 = 2609405) B2609405
theorem B1543025 : Blo 1028606 1543025 := bstep (se 2 (by rfl) ⟨578634, by rfl⟩ : syracuseStep 1543025 = 1157269) B1157269
theorem B1543043 : Blo 1028606 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B1543073 : Blo 1028606 1543073 := bstep (se 2 (by rfl) ⟨578652, by rfl⟩ : syracuseStep 1543073 = 1157305) B1157305
theorem B1543091 : Blo 1028606 1543091 := bstep (se 1 (by rfl) ⟨1157318, by rfl⟩ : syracuseStep 1543091 = 2314637) B2314637
theorem B7048133 : Blo 1028606 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B1543121 : Blo 1028606 1543121 := bstep (se 2 (by rfl) ⟨578670, by rfl⟩ : syracuseStep 1543121 = 1157341) B1157341
theorem B1739731 : Blo 1028606 1739731 := bstep (se 1 (by rfl) ⟨1304798, by rfl⟩ : syracuseStep 1739731 = 2609597) B2609597
theorem B1543139 : Blo 1028606 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B3476465 : Blo 1028606 3476465 := bstep (se 2 (by rfl) ⟨1303674, by rfl⟩ : syracuseStep 3476465 = 2607349) B2607349
theorem B2788337 : Blo 1028606 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B1543169 : Blo 1028606 1543169 := bstep (se 2 (by rfl) ⟨578688, by rfl⟩ : syracuseStep 1543169 = 1157377) B1157377
theorem B1543187 : Blo 1028606 1543187 := bstep (se 1 (by rfl) ⟨1157390, by rfl⟩ : syracuseStep 1543187 = 2314781) B2314781
theorem B1543217 : Blo 1028606 1543217 := bstep (se 2 (by rfl) ⟨578706, by rfl⟩ : syracuseStep 1543217 = 1157413) B1157413
theorem B1543235 : Blo 1028606 1543235 := bstep (se 1 (by rfl) ⟨1157426, by rfl⟩ : syracuseStep 1543235 = 2314853) B2314853
theorem B1543265 : Blo 1028606 1543265 := bstep (se 2 (by rfl) ⟨578724, by rfl⟩ : syracuseStep 1543265 = 1157449) B1157449
theorem B1739873 : Blo 1028606 1739873 := bstep (se 2 (by rfl) ⟨652452, by rfl⟩ : syracuseStep 1739873 = 1304905) B1304905
theorem B1543283 : Blo 1028606 1543283 := bstep (se 1 (by rfl) ⟨1157462, by rfl⟩ : syracuseStep 1543283 = 2314925) B2314925
theorem B1543313 : Blo 1028606 1543313 := bstep (se 2 (by rfl) ⟨578742, by rfl⟩ : syracuseStep 1543313 = 1157485) B1157485
theorem B1543331 : Blo 1028606 1543331 := bstep (se 1 (by rfl) ⟨1157498, by rfl⟩ : syracuseStep 1543331 = 2314997) B2314997
theorem B1543361 : Blo 1028606 1543361 := bstep (se 2 (by rfl) ⟨578760, by rfl⟩ : syracuseStep 1543361 = 1157521) B1157521
theorem B8359109 : Blo 1028606 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B1543379 : Blo 1028606 1543379 := bstep (se 1 (by rfl) ⟨1157534, by rfl⟩ : syracuseStep 1543379 = 2315069) B2315069
theorem B1740001 : Blo 1028606 1740001 := bstep (se 2 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 1740001 = 1305001) B1305001
theorem B2198755 : Blo 1028606 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B1543409 : Blo 1028606 1543409 := bstep (se 2 (by rfl) ⟨578778, by rfl⟩ : syracuseStep 1543409 = 1157557) B1157557
theorem B1543427 : Blo 1028606 1543427 := bstep (se 1 (by rfl) ⟨1157570, by rfl⟩ : syracuseStep 1543427 = 2315141) B2315141
theorem B1740035 : Blo 1028606 1740035 := bstep (se 1 (by rfl) ⟨1305026, by rfl⟩ : syracuseStep 1740035 = 2610053) B2610053
theorem B1543457 : Blo 1028606 1543457 := bstep (se 2 (by rfl) ⟨578796, by rfl⟩ : syracuseStep 1543457 = 1157593) B1157593
theorem B1543475 : Blo 1028606 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B12520757 : Blo 1028606 12520757 := bstep (se 5 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 12520757 = 1173821) B1173821
theorem B1543505 : Blo 1028606 1543505 := bstep (se 2 (by rfl) ⟨578814, by rfl⟩ : syracuseStep 1543505 = 1157629) B1157629
theorem B1543523 : Blo 1028606 1543523 := bstep (se 1 (by rfl) ⟨1157642, by rfl⟩ : syracuseStep 1543523 = 2315285) B2315285
theorem B1543553 : Blo 1028606 1543553 := bstep (se 2 (by rfl) ⟨578832, by rfl⟩ : syracuseStep 1543553 = 1157665) B1157665
theorem B1740163 : Blo 1028606 1740163 := bstep (se 1 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 1740163 = 2610245) B2610245
theorem B1543571 : Blo 1028606 1543571 := bstep (se 1 (by rfl) ⟨1157678, by rfl⟩ : syracuseStep 1543571 = 2315357) B2315357
theorem B3181997 : Blo 1028606 3181997 := bstep (se 3 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 3181997 = 1193249) B1193249
theorem B1543601 : Blo 1028606 1543601 := bstep (se 2 (by rfl) ⟨578850, by rfl⟩ : syracuseStep 1543601 = 1157701) B1157701
theorem B1543619 : Blo 1028606 1543619 := bstep (se 1 (by rfl) ⟨1157714, by rfl⟩ : syracuseStep 1543619 = 2315429) B2315429
theorem B6032837 : Blo 1028606 6032837 := bstep (se 4 (by rfl) ⟨565578, by rfl⟩ : syracuseStep 6032837 = 1131157) B1131157
theorem B5213645 : Blo 1028606 5213645 := bstep (se 3 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 5213645 = 1955117) B1955117
theorem B1543649 : Blo 1028606 1543649 := bstep (se 2 (by rfl) ⟨578868, by rfl⟩ : syracuseStep 1543649 = 1157737) B1157737
theorem B1543667 : Blo 1028606 1543667 := bstep (se 1 (by rfl) ⟨1157750, by rfl⟩ : syracuseStep 1543667 = 2315501) B2315501
theorem B3477005 : Blo 1028606 3477005 := bstep (se 3 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 3477005 = 1303877) B1303877
theorem B1543697 : Blo 1028606 1543697 := bstep (se 2 (by rfl) ⟨578886, by rfl⟩ : syracuseStep 1543697 = 1157773) B1157773
theorem B1740305 : Blo 1028606 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B1543715 : Blo 1028606 1543715 := bstep (se 1 (by rfl) ⟨1157786, by rfl⟩ : syracuseStep 1543715 = 2315573) B2315573
theorem B2199089 : Blo 1028606 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B1543745 : Blo 1028606 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B3477059 : Blo 1028606 3477059 := bstep (se 1 (by rfl) ⟨2607794, by rfl⟩ : syracuseStep 3477059 = 5215589) B5215589
theorem B4394573 : Blo 1028606 4394573 := bstep (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) B1647965
theorem B1543763 : Blo 1028606 1543763 := bstep (se 1 (by rfl) ⟨1157822, by rfl⟩ : syracuseStep 1543763 = 2315645) B2315645
theorem B1543793 : Blo 1028606 1543793 := bstep (se 2 (by rfl) ⟨578922, by rfl⟩ : syracuseStep 1543793 = 1157845) B1157845
theorem B1543811 : Blo 1028606 1543811 := bstep (se 1 (by rfl) ⟨1157858, by rfl⟩ : syracuseStep 1543811 = 2315717) B2315717
theorem B1740433 : Blo 1028606 1740433 := bstep (se 2 (by rfl) ⟨652662, by rfl⟩ : syracuseStep 1740433 = 1305325) B1305325
theorem B1543841 : Blo 1028606 1543841 := bstep (se 2 (by rfl) ⟨578940, by rfl⟩ : syracuseStep 1543841 = 1157881) B1157881
theorem B1543859 : Blo 1028606 1543859 := bstep (se 1 (by rfl) ⟨1157894, by rfl⟩ : syracuseStep 1543859 = 2315789) B2315789
theorem B1740467 : Blo 1028606 1740467 := bstep (se 1 (by rfl) ⟨1305350, by rfl⟩ : syracuseStep 1740467 = 2610701) B2610701
theorem B1543889 : Blo 1028606 1543889 := bstep (se 2 (by rfl) ⟨578958, by rfl⟩ : syracuseStep 1543889 = 1157917) B1157917
theorem B1543907 : Blo 1028606 1543907 := bstep (se 1 (by rfl) ⟨1157930, by rfl⟩ : syracuseStep 1543907 = 2315861) B2315861
theorem B1543937 : Blo 1028606 1543937 := bstep (se 2 (by rfl) ⟨578976, by rfl⟩ : syracuseStep 1543937 = 1157953) B1157953
theorem B1543955 : Blo 1028606 1543955 := bstep (se 1 (by rfl) ⟨1157966, by rfl⟩ : syracuseStep 1543955 = 2315933) B2315933
theorem B1543985 : Blo 1028606 1543985 := bstep (se 2 (by rfl) ⟨578994, by rfl⟩ : syracuseStep 1543985 = 1157989) B1157989
theorem B5869361 : Blo 1028606 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B1740595 : Blo 1028606 1740595 := bstep (se 1 (by rfl) ⟨1305446, by rfl⟩ : syracuseStep 1740595 = 2610893) B2610893
theorem B1544003 : Blo 1028606 1544003 := bstep (se 1 (by rfl) ⟨1158002, by rfl⟩ : syracuseStep 1544003 = 2316005) B2316005
theorem B3477329 : Blo 1028606 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B2789201 : Blo 1028606 2789201 := bstep (se 2 (by rfl) ⟨1045950, by rfl⟩ : syracuseStep 2789201 = 2091901) B2091901
theorem B1544033 : Blo 1028606 1544033 := bstep (se 2 (by rfl) ⟨579012, by rfl⟩ : syracuseStep 1544033 = 1158025) B1158025
theorem B8359793 : Blo 1028606 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B1544051 : Blo 1028606 1544051 := bstep (se 1 (by rfl) ⟨1158038, by rfl⟩ : syracuseStep 1544051 = 2316077) B2316077
theorem B1544081 : Blo 1028606 1544081 := bstep (se 2 (by rfl) ⟨579030, by rfl⟩ : syracuseStep 1544081 = 1158061) B1158061
theorem B1544099 : Blo 1028606 1544099 := bstep (se 1 (by rfl) ⟨1158074, by rfl⟩ : syracuseStep 1544099 = 2316149) B2316149
theorem B1544129 : Blo 1028606 1544129 := bstep (se 2 (by rfl) ⟨579048, by rfl⟩ : syracuseStep 1544129 = 1158097) B1158097
theorem B1740737 : Blo 1028606 1740737 := bstep (se 2 (by rfl) ⟨652776, by rfl⟩ : syracuseStep 1740737 = 1305553) B1305553
theorem B1544147 : Blo 1028606 1544147 := bstep (se 1 (by rfl) ⟨1158110, by rfl⟩ : syracuseStep 1544147 = 2316221) B2316221
theorem B1544177 : Blo 1028606 1544177 := bstep (se 2 (by rfl) ⟨579066, by rfl⟩ : syracuseStep 1544177 = 1158133) B1158133
theorem B1544195 : Blo 1028606 1544195 := bstep (se 1 (by rfl) ⟨1158146, by rfl⟩ : syracuseStep 1544195 = 2316293) B2316293
theorem B1544225 : Blo 1028606 1544225 := bstep (se 2 (by rfl) ⟨579084, by rfl⟩ : syracuseStep 1544225 = 1158169) B1158169
theorem B1544243 : Blo 1028606 1544243 := bstep (se 1 (by rfl) ⟨1158182, by rfl⟩ : syracuseStep 1544243 = 2316365) B2316365
theorem B1740865 : Blo 1028606 1740865 := bstep (se 2 (by rfl) ⟨652824, by rfl⟩ : syracuseStep 1740865 = 1305649) B1305649
theorem B1544273 : Blo 1028606 1544273 := bstep (se 2 (by rfl) ⟨579102, by rfl⟩ : syracuseStep 1544273 = 1158205) B1158205
theorem B1544291 : Blo 1028606 1544291 := bstep (se 1 (by rfl) ⟨1158218, by rfl⟩ : syracuseStep 1544291 = 2316437) B2316437
theorem B1740899 : Blo 1028606 1740899 := bstep (se 1 (by rfl) ⟨1305674, by rfl⟩ : syracuseStep 1740899 = 2611349) B2611349
theorem B1544321 : Blo 1028606 1544321 := bstep (se 2 (by rfl) ⟨579120, by rfl⟩ : syracuseStep 1544321 = 1158241) B1158241
theorem B1544339 : Blo 1028606 1544339 := bstep (se 1 (by rfl) ⟨1158254, by rfl⟩ : syracuseStep 1544339 = 2316509) B2316509
theorem B2789549 : Blo 1028606 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B1544369 : Blo 1028606 1544369 := bstep (se 2 (by rfl) ⟨579138, by rfl⟩ : syracuseStep 1544369 = 1158277) B1158277
theorem B1544387 : Blo 1028606 1544387 := bstep (se 1 (by rfl) ⟨1158290, by rfl⟩ : syracuseStep 1544387 = 2316581) B2316581
theorem B1544417 : Blo 1028606 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B1741027 : Blo 1028606 1741027 := bstep (se 1 (by rfl) ⟨1305770, by rfl⟩ : syracuseStep 1741027 = 2611541) B2611541
theorem B1544435 : Blo 1028606 1544435 := bstep (se 1 (by rfl) ⟨1158326, by rfl⟩ : syracuseStep 1544435 = 2316653) B2316653
theorem B1544465 : Blo 1028606 1544465 := bstep (se 2 (by rfl) ⟨579174, by rfl⟩ : syracuseStep 1544465 = 1158349) B1158349
theorem B1544483 : Blo 1028606 1544483 := bstep (se 1 (by rfl) ⟨1158362, by rfl⟩ : syracuseStep 1544483 = 2316725) B2316725
theorem B1544513 : Blo 1028606 1544513 := bstep (se 2 (by rfl) ⟨579192, by rfl⟩ : syracuseStep 1544513 = 1158385) B1158385
theorem B1544531 : Blo 1028606 1544531 := bstep (se 1 (by rfl) ⟨1158398, by rfl⟩ : syracuseStep 1544531 = 2316797) B2316797
theorem B3477869 : Blo 1028606 3477869 := bstep (se 3 (by rfl) ⟨652100, by rfl⟩ : syracuseStep 3477869 = 1304201) B1304201
theorem B1544561 : Blo 1028606 1544561 := bstep (se 2 (by rfl) ⟨579210, by rfl⟩ : syracuseStep 1544561 = 1158421) B1158421
theorem B1741169 : Blo 1028606 1741169 := bstep (se 2 (by rfl) ⟨652938, by rfl⟩ : syracuseStep 1741169 = 1305877) B1305877
theorem B1544579 : Blo 1028606 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B1544609 : Blo 1028606 1544609 := bstep (se 2 (by rfl) ⟨579228, by rfl⟩ : syracuseStep 1544609 = 1158457) B1158457
theorem B3477923 : Blo 1028606 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B1544627 : Blo 1028606 1544627 := bstep (se 1 (by rfl) ⟨1158470, by rfl⟩ : syracuseStep 1544627 = 2316941) B2316941
theorem B1544657 : Blo 1028606 1544657 := bstep (se 2 (by rfl) ⟨579246, by rfl⟩ : syracuseStep 1544657 = 1158493) B1158493
theorem B1544675 : Blo 1028606 1544675 := bstep (se 1 (by rfl) ⟨1158506, by rfl⟩ : syracuseStep 1544675 = 2317013) B2317013
theorem B1741297 : Blo 1028606 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B1544705 : Blo 1028606 1544705 := bstep (se 2 (by rfl) ⟨579264, by rfl⟩ : syracuseStep 1544705 = 1158529) B1158529
theorem B1544723 : Blo 1028606 1544723 := bstep (se 1 (by rfl) ⟨1158542, by rfl⟩ : syracuseStep 1544723 = 2317085) B2317085
theorem B1741331 : Blo 1028606 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B1544753 : Blo 1028606 1544753 := bstep (se 2 (by rfl) ⟨579282, by rfl⟩ : syracuseStep 1544753 = 1158565) B1158565
theorem B1544771 : Blo 1028606 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B1544801 : Blo 1028606 1544801 := bstep (se 2 (by rfl) ⟨579300, by rfl⟩ : syracuseStep 1544801 = 1158601) B1158601
theorem B1544819 : Blo 1028606 1544819 := bstep (se 1 (by rfl) ⟨1158614, by rfl⟩ : syracuseStep 1544819 = 2317229) B2317229
theorem B1544849 : Blo 1028606 1544849 := bstep (se 2 (by rfl) ⟨579318, by rfl⟩ : syracuseStep 1544849 = 1158637) B1158637
theorem B1741459 : Blo 1028606 1741459 := bstep (se 1 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 1741459 = 2612189) B2612189
theorem B1544867 : Blo 1028606 1544867 := bstep (se 1 (by rfl) ⟨1158650, by rfl⟩ : syracuseStep 1544867 = 2317301) B2317301
theorem B3478193 : Blo 1028606 3478193 := bstep (se 2 (by rfl) ⟨1304322, by rfl⟩ : syracuseStep 3478193 = 2608645) B2608645
theorem B1544897 : Blo 1028606 1544897 := bstep (se 2 (by rfl) ⟨579336, by rfl⟩ : syracuseStep 1544897 = 1158673) B1158673
theorem B2200259 : Blo 1028606 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B1544915 : Blo 1028606 1544915 := bstep (se 1 (by rfl) ⟨1158686, by rfl⟩ : syracuseStep 1544915 = 2317373) B2317373
theorem B1544945 : Blo 1028606 1544945 := bstep (se 2 (by rfl) ⟨579354, by rfl⟩ : syracuseStep 1544945 = 1158709) B1158709
theorem B1544963 : Blo 1028606 1544963 := bstep (se 1 (by rfl) ⟨1158722, by rfl⟩ : syracuseStep 1544963 = 2317445) B2317445
theorem B1544993 : Blo 1028606 1544993 := bstep (se 2 (by rfl) ⟨579372, by rfl⟩ : syracuseStep 1544993 = 1158745) B1158745
theorem B1741601 : Blo 1028606 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B1545011 : Blo 1028606 1545011 := bstep (se 1 (by rfl) ⟨1158758, by rfl⟩ : syracuseStep 1545011 = 2317517) B2317517
theorem B1545041 : Blo 1028606 1545041 := bstep (se 2 (by rfl) ⟨579390, by rfl⟩ : syracuseStep 1545041 = 1158781) B1158781
theorem B1545059 : Blo 1028606 1545059 := bstep (se 1 (by rfl) ⟨1158794, by rfl⟩ : syracuseStep 1545059 = 2317589) B2317589
theorem B1545089 : Blo 1028606 1545089 := bstep (se 2 (by rfl) ⟨579408, by rfl⟩ : syracuseStep 1545089 = 1158817) B1158817
theorem B1545107 : Blo 1028606 1545107 := bstep (se 1 (by rfl) ⟨1158830, by rfl⟩ : syracuseStep 1545107 = 2317661) B2317661
theorem B1741729 : Blo 1028606 1741729 := bstep (se 2 (by rfl) ⟨653148, by rfl⟩ : syracuseStep 1741729 = 1306297) B1306297
theorem B1545137 : Blo 1028606 1545137 := bstep (se 2 (by rfl) ⟨579426, by rfl⟩ : syracuseStep 1545137 = 1158853) B1158853
theorem B1545155 : Blo 1028606 1545155 := bstep (se 1 (by rfl) ⟨1158866, by rfl⟩ : syracuseStep 1545155 = 2317733) B2317733
theorem B1741763 : Blo 1028606 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B1545185 : Blo 1028606 1545185 := bstep (se 2 (by rfl) ⟨579444, by rfl⟩ : syracuseStep 1545185 = 1158889) B1158889
theorem B1545203 : Blo 1028606 1545203 := bstep (se 1 (by rfl) ⟨1158902, by rfl⟩ : syracuseStep 1545203 = 2317805) B2317805
theorem B2790413 : Blo 1028606 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B1545233 : Blo 1028606 1545233 := bstep (se 2 (by rfl) ⟨579462, by rfl⟩ : syracuseStep 1545233 = 1158925) B1158925
theorem B1545251 : Blo 1028606 1545251 := bstep (se 1 (by rfl) ⟨1158938, by rfl⟩ : syracuseStep 1545251 = 2317877) B2317877
theorem B1545281 : Blo 1028606 1545281 := bstep (se 2 (by rfl) ⟨579480, by rfl⟩ : syracuseStep 1545281 = 1158961) B1158961
theorem B1741891 : Blo 1028606 1741891 := bstep (se 1 (by rfl) ⟨1306418, by rfl⟩ : syracuseStep 1741891 = 2612837) B2612837
theorem B1545299 : Blo 1028606 1545299 := bstep (se 1 (by rfl) ⟨1158974, by rfl⟩ : syracuseStep 1545299 = 2317949) B2317949
theorem B1545329 : Blo 1028606 1545329 := bstep (se 2 (by rfl) ⟨579498, by rfl⟩ : syracuseStep 1545329 = 1158997) B1158997
theorem B1545347 : Blo 1028606 1545347 := bstep (se 1 (by rfl) ⟨1159010, by rfl⟩ : syracuseStep 1545347 = 2318021) B2318021
theorem B1545377 : Blo 1028606 1545377 := bstep (se 2 (by rfl) ⟨579516, by rfl⟩ : syracuseStep 1545377 = 1159033) B1159033
theorem B3970225 : Blo 1028606 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B1545395 : Blo 1028606 1545395 := bstep (se 1 (by rfl) ⟨1159046, by rfl⟩ : syracuseStep 1545395 = 2318093) B2318093
theorem B3478733 : Blo 1028606 3478733 := bstep (se 3 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 3478733 = 1304525) B1304525
theorem B1545425 : Blo 1028606 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B1742033 : Blo 1028606 1742033 := bstep (se 2 (by rfl) ⟨653262, by rfl⟩ : syracuseStep 1742033 = 1306525) B1306525
theorem B1545443 : Blo 1028606 1545443 := bstep (se 1 (by rfl) ⟨1159082, by rfl⟩ : syracuseStep 1545443 = 2318165) B2318165
theorem B5870819 : Blo 1028606 5870819 := bstep (se 1 (by rfl) ⟨4403114, by rfl⟩ : syracuseStep 5870819 = 8806229) B8806229
theorem B1545473 : Blo 1028606 1545473 := bstep (se 2 (by rfl) ⟨579552, by rfl⟩ : syracuseStep 1545473 = 1159105) B1159105
theorem B3478787 : Blo 1028606 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B1545491 : Blo 1028606 1545491 := bstep (se 1 (by rfl) ⟨1159118, by rfl⟩ : syracuseStep 1545491 = 2318237) B2318237
theorem B1545521 : Blo 1028606 1545521 := bstep (se 2 (by rfl) ⟨579570, by rfl⟩ : syracuseStep 1545521 = 1159141) B1159141
theorem B1545539 : Blo 1028606 1545539 := bstep (se 1 (by rfl) ⟨1159154, by rfl⟩ : syracuseStep 1545539 = 2318309) B2318309
theorem B1742161 : Blo 1028606 1742161 := bstep (se 2 (by rfl) ⟨653310, by rfl⟩ : syracuseStep 1742161 = 1306621) B1306621
theorem B1545569 : Blo 1028606 1545569 := bstep (se 2 (by rfl) ⟨579588, by rfl⟩ : syracuseStep 1545569 = 1159177) B1159177
theorem B1545587 : Blo 1028606 1545587 := bstep (se 1 (by rfl) ⟨1159190, by rfl⟩ : syracuseStep 1545587 = 2318381) B2318381
theorem B1742195 : Blo 1028606 1742195 := bstep (se 1 (by rfl) ⟨1306646, by rfl⟩ : syracuseStep 1742195 = 2613293) B2613293
theorem B12719501 : Blo 1028606 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1545617 : Blo 1028606 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B1545635 : Blo 1028606 1545635 := bstep (se 1 (by rfl) ⟨1159226, by rfl⟩ : syracuseStep 1545635 = 2318453) B2318453
theorem B1545665 : Blo 1028606 1545665 := bstep (se 2 (by rfl) ⟨579624, by rfl⟩ : syracuseStep 1545665 = 1159249) B1159249
theorem B1545683 : Blo 1028606 1545683 := bstep (se 1 (by rfl) ⟨1159262, by rfl⟩ : syracuseStep 1545683 = 2318525) B2318525
theorem B1545713 : Blo 1028606 1545713 := bstep (se 2 (by rfl) ⟨579642, by rfl⟩ : syracuseStep 1545713 = 1159285) B1159285
theorem B1742323 : Blo 1028606 1742323 := bstep (se 1 (by rfl) ⟨1306742, by rfl⟩ : syracuseStep 1742323 = 2613485) B2613485
theorem B1545731 : Blo 1028606 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B6592013 : Blo 1028606 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B3479057 : Blo 1028606 3479057 := bstep (se 2 (by rfl) ⟨1304646, by rfl⟩ : syracuseStep 3479057 = 2609293) B2609293
theorem B1545761 : Blo 1028606 1545761 := bstep (se 2 (by rfl) ⟨579660, by rfl⟩ : syracuseStep 1545761 = 1159321) B1159321
theorem B1545779 : Blo 1028606 1545779 := bstep (se 1 (by rfl) ⟨1159334, by rfl⟩ : syracuseStep 1545779 = 2318669) B2318669
theorem B1545809 : Blo 1028606 1545809 := bstep (se 2 (by rfl) ⟨579678, by rfl⟩ : syracuseStep 1545809 = 1159357) B1159357
theorem B1545827 : Blo 1028606 1545827 := bstep (se 1 (by rfl) ⟨1159370, by rfl⟩ : syracuseStep 1545827 = 2318741) B2318741
theorem B1545857 : Blo 1028606 1545857 := bstep (se 2 (by rfl) ⟨579696, by rfl⟩ : syracuseStep 1545857 = 1159393) B1159393
theorem B1742465 : Blo 1028606 1742465 := bstep (se 2 (by rfl) ⟨653424, by rfl⟩ : syracuseStep 1742465 = 1306849) B1306849
theorem B1545875 : Blo 1028606 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B1545905 : Blo 1028606 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1545923 : Blo 1028606 1545923 := bstep (se 1 (by rfl) ⟨1159442, by rfl⟩ : syracuseStep 1545923 = 2318885) B2318885
theorem B1545953 : Blo 1028606 1545953 := bstep (se 2 (by rfl) ⟨579732, by rfl⟩ : syracuseStep 1545953 = 1159465) B1159465
theorem B1545971 : Blo 1028606 1545971 := bstep (se 1 (by rfl) ⟨1159478, by rfl⟩ : syracuseStep 1545971 = 2318957) B2318957
theorem B1546001 : Blo 1028606 1546001 := bstep (se 2 (by rfl) ⟨579750, by rfl⟩ : syracuseStep 1546001 = 1159501) B1159501
theorem B1546019 : Blo 1028606 1546019 := bstep (se 1 (by rfl) ⟨1159514, by rfl⟩ : syracuseStep 1546019 = 2319029) B2319029
theorem B1546049 : Blo 1028606 1546049 := bstep (se 2 (by rfl) ⟨579768, by rfl⟩ : syracuseStep 1546049 = 1159537) B1159537
theorem B1546067 : Blo 1028606 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B3708785 : Blo 1028606 3708785 := bstep (se 2 (by rfl) ⟨1390794, by rfl⟩ : syracuseStep 3708785 = 2781589) B2781589
theorem B1546097 : Blo 1028606 1546097 := bstep (se 2 (by rfl) ⟨579786, by rfl⟩ : syracuseStep 1546097 = 1159573) B1159573
theorem B1546115 : Blo 1028606 1546115 := bstep (se 1 (by rfl) ⟨1159586, by rfl⟩ : syracuseStep 1546115 = 2319173) B2319173
theorem B1546145 : Blo 1028606 1546145 := bstep (se 2 (by rfl) ⟨579804, by rfl⟩ : syracuseStep 1546145 = 1159609) B1159609
theorem B1546163 : Blo 1028606 1546163 := bstep (se 1 (by rfl) ⟨1159622, by rfl⟩ : syracuseStep 1546163 = 2319245) B2319245
theorem B1546193 : Blo 1028606 1546193 := bstep (se 2 (by rfl) ⟨579822, by rfl⟩ : syracuseStep 1546193 = 1159645) B1159645
theorem B1546211 : Blo 1028606 1546211 := bstep (se 1 (by rfl) ⟨1159658, by rfl⟩ : syracuseStep 1546211 = 2319317) B2319317
theorem B1546241 : Blo 1028606 1546241 := bstep (se 2 (by rfl) ⟨579840, by rfl⟩ : syracuseStep 1546241 = 1159681) B1159681
theorem B1546259 : Blo 1028606 1546259 := bstep (se 1 (by rfl) ⟨1159694, by rfl⟩ : syracuseStep 1546259 = 2319389) B2319389
theorem B3479597 : Blo 1028606 3479597 := bstep (se 3 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 3479597 = 1304849) B1304849
theorem B1546289 : Blo 1028606 1546289 := bstep (se 2 (by rfl) ⟨579858, by rfl⟩ : syracuseStep 1546289 = 1159717) B1159717
theorem B1546307 : Blo 1028606 1546307 := bstep (se 1 (by rfl) ⟨1159730, by rfl⟩ : syracuseStep 1546307 = 2319461) B2319461
theorem B1546337 : Blo 1028606 1546337 := bstep (se 2 (by rfl) ⟨579876, by rfl⟩ : syracuseStep 1546337 = 1159753) B1159753
theorem B3479651 : Blo 1028606 3479651 := bstep (se 1 (by rfl) ⟨2609738, by rfl⟩ : syracuseStep 3479651 = 5219477) B5219477
theorem B1546355 : Blo 1028606 1546355 := bstep (se 1 (by rfl) ⟨1159766, by rfl⟩ : syracuseStep 1546355 = 2319533) B2319533
theorem B5576845 : Blo 1028606 5576845 := bstep (se 3 (by rfl) ⟨1045658, by rfl⟩ : syracuseStep 5576845 = 2091317) B2091317
theorem B1546385 : Blo 1028606 1546385 := bstep (se 2 (by rfl) ⟨579894, by rfl⟩ : syracuseStep 1546385 = 1159789) B1159789
theorem B1546403 : Blo 1028606 1546403 := bstep (se 1 (by rfl) ⟨1159802, by rfl⟩ : syracuseStep 1546403 = 2319605) B2319605
theorem B1546433 : Blo 1028606 1546433 := bstep (se 2 (by rfl) ⟨579912, by rfl⟩ : syracuseStep 1546433 = 1159825) B1159825
theorem B16718021 : Blo 1028606 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B1546451 : Blo 1028606 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B1546481 : Blo 1028606 1546481 := bstep (se 2 (by rfl) ⟨579930, by rfl⟩ : syracuseStep 1546481 = 1159861) B1159861
theorem B1546499 : Blo 1028606 1546499 := bstep (se 1 (by rfl) ⟨1159874, by rfl⟩ : syracuseStep 1546499 = 2319749) B2319749
theorem B1546529 : Blo 1028606 1546529 := bstep (se 2 (by rfl) ⟨579948, by rfl⟩ : syracuseStep 1546529 = 1159897) B1159897
theorem B5216561 : Blo 1028606 5216561 := bstep (se 2 (by rfl) ⟨1956210, by rfl⟩ : syracuseStep 5216561 = 3912421) B3912421
theorem B1546547 : Blo 1028606 1546547 := bstep (se 1 (by rfl) ⟨1159910, by rfl⟩ : syracuseStep 1546547 = 2319821) B2319821
theorem B8821061 : Blo 1028606 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B1546577 : Blo 1028606 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B3905891 : Blo 1028606 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B1546595 : Blo 1028606 1546595 := bstep (se 1 (by rfl) ⟨1159946, by rfl⟩ : syracuseStep 1546595 = 2319893) B2319893
theorem B3479921 : Blo 1028606 3479921 := bstep (se 2 (by rfl) ⟨1304970, by rfl⟩ : syracuseStep 3479921 = 2609941) B2609941
theorem B1546625 : Blo 1028606 1546625 := bstep (se 2 (by rfl) ⟨579984, by rfl⟩ : syracuseStep 1546625 = 1159969) B1159969
theorem B1546643 : Blo 1028606 1546643 := bstep (se 1 (by rfl) ⟨1159982, by rfl⟩ : syracuseStep 1546643 = 2319965) B2319965
theorem B1546673 : Blo 1028606 1546673 := bstep (se 2 (by rfl) ⟨580002, by rfl⟩ : syracuseStep 1546673 = 1160005) B1160005
theorem B1546691 : Blo 1028606 1546691 := bstep (se 1 (by rfl) ⟨1160018, by rfl⟩ : syracuseStep 1546691 = 2320037) B2320037
theorem B1546721 : Blo 1028606 1546721 := bstep (se 2 (by rfl) ⟨580020, by rfl⟩ : syracuseStep 1546721 = 1160041) B1160041
theorem B1546739 : Blo 1028606 1546739 := bstep (se 1 (by rfl) ⟨1160054, by rfl⟩ : syracuseStep 1546739 = 2320109) B2320109
theorem B1546769 : Blo 1028606 1546769 := bstep (se 2 (by rfl) ⟨580038, by rfl⟩ : syracuseStep 1546769 = 1160077) B1160077
theorem B1546787 : Blo 1028606 1546787 := bstep (se 1 (by rfl) ⟨1160090, by rfl⟩ : syracuseStep 1546787 = 2320181) B2320181
theorem B1546817 : Blo 1028606 1546817 := bstep (se 2 (by rfl) ⟨580056, by rfl⟩ : syracuseStep 1546817 = 1160113) B1160113
theorem B1546835 : Blo 1028606 1546835 := bstep (se 1 (by rfl) ⟨1160126, by rfl⟩ : syracuseStep 1546835 = 2320253) B2320253
theorem B1546865 : Blo 1028606 1546865 := bstep (se 2 (by rfl) ⟨580074, by rfl⟩ : syracuseStep 1546865 = 1160149) B1160149
theorem B1546883 : Blo 1028606 1546883 := bstep (se 1 (by rfl) ⟨1160162, by rfl⟩ : syracuseStep 1546883 = 2320325) B2320325
theorem B1546913 : Blo 1028606 1546913 := bstep (se 2 (by rfl) ⟨580092, by rfl⟩ : syracuseStep 1546913 = 1160185) B1160185
theorem B2202275 : Blo 1028606 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B1546931 : Blo 1028606 1546931 := bstep (se 1 (by rfl) ⟨1160198, by rfl⟩ : syracuseStep 1546931 = 2320397) B2320397
theorem B1546961 : Blo 1028606 1546961 := bstep (se 2 (by rfl) ⟨580110, by rfl⟩ : syracuseStep 1546961 = 1160221) B1160221
theorem B1546979 : Blo 1028606 1546979 := bstep (se 1 (by rfl) ⟨1160234, by rfl⟩ : syracuseStep 1546979 = 2320469) B2320469
theorem B1547009 : Blo 1028606 1547009 := bstep (se 2 (by rfl) ⟨580128, by rfl⟩ : syracuseStep 1547009 = 1160257) B1160257
theorem B3709709 : Blo 1028606 3709709 := bstep (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) B1391141
theorem B1547027 : Blo 1028606 1547027 := bstep (se 1 (by rfl) ⟨1160270, by rfl⟩ : syracuseStep 1547027 = 2320541) B2320541
theorem B1547057 : Blo 1028606 1547057 := bstep (se 2 (by rfl) ⟨580146, by rfl⟩ : syracuseStep 1547057 = 1160293) B1160293
theorem B15276853 : Blo 1028606 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B1547075 : Blo 1028606 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B1547105 : Blo 1028606 1547105 := bstep (se 2 (by rfl) ⟨580164, by rfl⟩ : syracuseStep 1547105 = 1160329) B1160329
theorem B1547123 : Blo 1028606 1547123 := bstep (se 1 (by rfl) ⟨1160342, by rfl⟩ : syracuseStep 1547123 = 2320685) B2320685
theorem B3480461 : Blo 1028606 3480461 := bstep (se 3 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 3480461 = 1305173) B1305173
theorem B1547153 : Blo 1028606 1547153 := bstep (se 2 (by rfl) ⟨580182, by rfl⟩ : syracuseStep 1547153 = 1160365) B1160365
theorem B1547171 : Blo 1028606 1547171 := bstep (se 1 (by rfl) ⟨1160378, by rfl⟩ : syracuseStep 1547171 = 2320757) B2320757
theorem B1547201 : Blo 1028606 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B3480515 : Blo 1028606 3480515 := bstep (se 1 (by rfl) ⟨2610386, by rfl⟩ : syracuseStep 3480515 = 5220773) B5220773
theorem B1547219 : Blo 1028606 1547219 := bstep (se 1 (by rfl) ⟨1160414, by rfl⟩ : syracuseStep 1547219 = 2320829) B2320829
theorem B1547249 : Blo 1028606 1547249 := bstep (se 2 (by rfl) ⟨580218, by rfl⟩ : syracuseStep 1547249 = 1160437) B1160437
theorem B1547267 : Blo 1028606 1547267 := bstep (se 1 (by rfl) ⟨1160450, by rfl⟩ : syracuseStep 1547267 = 2320901) B2320901
theorem B1547297 : Blo 1028606 1547297 := bstep (se 2 (by rfl) ⟨580236, by rfl⟩ : syracuseStep 1547297 = 1160473) B1160473
theorem B1547315 : Blo 1028606 1547315 := bstep (se 1 (by rfl) ⟨1160486, by rfl⟩ : syracuseStep 1547315 = 2320973) B2320973
theorem B1547345 : Blo 1028606 1547345 := bstep (se 2 (by rfl) ⟨580254, by rfl⟩ : syracuseStep 1547345 = 1160509) B1160509
theorem B1547363 : Blo 1028606 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B1547393 : Blo 1028606 1547393 := bstep (se 2 (by rfl) ⟨580272, by rfl⟩ : syracuseStep 1547393 = 1160545) B1160545
theorem B1547411 : Blo 1028606 1547411 := bstep (se 1 (by rfl) ⟨1160558, by rfl⟩ : syracuseStep 1547411 = 2321117) B2321117
theorem B1547441 : Blo 1028606 1547441 := bstep (se 2 (by rfl) ⟨580290, by rfl⟩ : syracuseStep 1547441 = 1160581) B1160581
theorem B1547459 : Blo 1028606 1547459 := bstep (se 1 (by rfl) ⟨1160594, by rfl⟩ : syracuseStep 1547459 = 2321189) B2321189
theorem B3480785 : Blo 1028606 3480785 := bstep (se 2 (by rfl) ⟨1305294, by rfl⟩ : syracuseStep 3480785 = 2610589) B2610589
theorem B1547489 : Blo 1028606 1547489 := bstep (se 2 (by rfl) ⟨580308, by rfl⟩ : syracuseStep 1547489 = 1160617) B1160617
theorem B1547507 : Blo 1028606 1547507 := bstep (se 1 (by rfl) ⟨1160630, by rfl⟩ : syracuseStep 1547507 = 2321261) B2321261
theorem B1547537 : Blo 1028606 1547537 := bstep (se 2 (by rfl) ⟨580326, by rfl⟩ : syracuseStep 1547537 = 1160653) B1160653
theorem B1547555 : Blo 1028606 1547555 := bstep (se 1 (by rfl) ⟨1160666, by rfl⟩ : syracuseStep 1547555 = 2321333) B2321333
theorem B1547585 : Blo 1028606 1547585 := bstep (se 2 (by rfl) ⟨580344, by rfl⟩ : syracuseStep 1547585 = 1160689) B1160689
theorem B3906893 : Blo 1028606 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B1547603 : Blo 1028606 1547603 := bstep (se 1 (by rfl) ⟨1160702, by rfl⟩ : syracuseStep 1547603 = 2321405) B2321405
theorem B1547633 : Blo 1028606 1547633 := bstep (se 2 (by rfl) ⟨580362, by rfl⟩ : syracuseStep 1547633 = 1160725) B1160725
theorem B1547651 : Blo 1028606 1547651 := bstep (se 1 (by rfl) ⟨1160738, by rfl⟩ : syracuseStep 1547651 = 2321477) B2321477
theorem B1547681 : Blo 1028606 1547681 := bstep (se 2 (by rfl) ⟨580380, by rfl⟩ : syracuseStep 1547681 = 1160761) B1160761
theorem B1547699 : Blo 1028606 1547699 := bstep (se 1 (by rfl) ⟨1160774, by rfl⟩ : syracuseStep 1547699 = 2321549) B2321549
theorem B1547729 : Blo 1028606 1547729 := bstep (se 2 (by rfl) ⟨580398, by rfl⟩ : syracuseStep 1547729 = 1160797) B1160797
theorem B1547747 : Blo 1028606 1547747 := bstep (se 1 (by rfl) ⟨1160810, by rfl⟩ : syracuseStep 1547747 = 2321621) B2321621
theorem B1547777 : Blo 1028606 1547777 := bstep (se 2 (by rfl) ⟨580416, by rfl⟩ : syracuseStep 1547777 = 1160833) B1160833
theorem B1547795 : Blo 1028606 1547795 := bstep (se 1 (by rfl) ⟨1160846, by rfl⟩ : syracuseStep 1547795 = 2321693) B2321693
theorem B1547825 : Blo 1028606 1547825 := bstep (se 2 (by rfl) ⟨580434, by rfl⟩ : syracuseStep 1547825 = 1160869) B1160869
theorem B1547843 : Blo 1028606 1547843 := bstep (se 1 (by rfl) ⟨1160882, by rfl⟩ : syracuseStep 1547843 = 2321765) B2321765
theorem B1547873 : Blo 1028606 1547873 := bstep (se 2 (by rfl) ⟨580452, by rfl⟩ : syracuseStep 1547873 = 1160905) B1160905
theorem B1547891 : Blo 1028606 1547891 := bstep (se 1 (by rfl) ⟨1160918, by rfl⟩ : syracuseStep 1547891 = 2321837) B2321837
theorem B1547921 : Blo 1028606 1547921 := bstep (se 2 (by rfl) ⟨580470, by rfl⟩ : syracuseStep 1547921 = 1160941) B1160941
theorem B1547939 : Blo 1028606 1547939 := bstep (se 1 (by rfl) ⟨1160954, by rfl⟩ : syracuseStep 1547939 = 2321909) B2321909
theorem B12689077 : Blo 1028606 12689077 := bstep (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) B1189601
theorem B1547969 : Blo 1028606 1547969 := bstep (se 2 (by rfl) ⟨580488, by rfl⟩ : syracuseStep 1547969 = 1160977) B1160977
theorem B1547987 : Blo 1028606 1547987 := bstep (se 1 (by rfl) ⟨1160990, by rfl⟩ : syracuseStep 1547987 = 2321981) B2321981
theorem B5218019 : Blo 1028606 5218019 := bstep (se 1 (by rfl) ⟨3913514, by rfl⟩ : syracuseStep 5218019 = 7827029) B7827029
theorem B3481325 : Blo 1028606 3481325 := bstep (se 3 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 3481325 = 1305497) B1305497
theorem B1548017 : Blo 1028606 1548017 := bstep (se 2 (by rfl) ⟨580506, by rfl⟩ : syracuseStep 1548017 = 1161013) B1161013
theorem B1548035 : Blo 1028606 1548035 := bstep (se 1 (by rfl) ⟨1161026, by rfl⟩ : syracuseStep 1548035 = 2322053) B2322053
theorem B1548065 : Blo 1028606 1548065 := bstep (se 2 (by rfl) ⟨580524, by rfl⟩ : syracuseStep 1548065 = 1161049) B1161049
theorem B3481379 : Blo 1028606 3481379 := bstep (se 1 (by rfl) ⟨2611034, by rfl⟩ : syracuseStep 3481379 = 5222069) B5222069
theorem B1548083 : Blo 1028606 1548083 := bstep (se 1 (by rfl) ⟨1161062, by rfl⟩ : syracuseStep 1548083 = 2322125) B2322125
theorem B1548113 : Blo 1028606 1548113 := bstep (se 2 (by rfl) ⟨580542, by rfl⟩ : syracuseStep 1548113 = 1161085) B1161085
theorem B4398947 : Blo 1028606 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B1548131 : Blo 1028606 1548131 := bstep (se 1 (by rfl) ⟨1161098, by rfl⟩ : syracuseStep 1548131 = 2322197) B2322197
theorem B1548161 : Blo 1028606 1548161 := bstep (se 2 (by rfl) ⟨580560, by rfl⟩ : syracuseStep 1548161 = 1161121) B1161121
theorem B3710861 : Blo 1028606 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B1548179 : Blo 1028606 1548179 := bstep (se 1 (by rfl) ⟨1161134, by rfl⟩ : syracuseStep 1548179 = 2322269) B2322269
theorem B1548209 : Blo 1028606 1548209 := bstep (se 2 (by rfl) ⟨580578, by rfl⟩ : syracuseStep 1548209 = 1161157) B1161157
theorem B1548227 : Blo 1028606 1548227 := bstep (se 1 (by rfl) ⟨1161170, by rfl⟩ : syracuseStep 1548227 = 2322341) B2322341
theorem B1548257 : Blo 1028606 1548257 := bstep (se 2 (by rfl) ⟨580596, by rfl⟩ : syracuseStep 1548257 = 1161193) B1161193
theorem B1548275 : Blo 1028606 1548275 := bstep (se 1 (by rfl) ⟨1161206, by rfl⟩ : syracuseStep 1548275 = 2322413) B2322413
theorem B1548305 : Blo 1028606 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B1548323 : Blo 1028606 1548323 := bstep (se 1 (by rfl) ⟨1161242, by rfl⟩ : syracuseStep 1548323 = 2322485) B2322485
theorem B3481649 : Blo 1028606 3481649 := bstep (se 2 (by rfl) ⟨1305618, by rfl⟩ : syracuseStep 3481649 = 2611237) B2611237
theorem B1548353 : Blo 1028606 1548353 := bstep (se 2 (by rfl) ⟨580632, by rfl⟩ : syracuseStep 1548353 = 1161265) B1161265
theorem B1548371 : Blo 1028606 1548371 := bstep (se 1 (by rfl) ⟨1161278, by rfl⟩ : syracuseStep 1548371 = 2322557) B2322557
theorem B1548401 : Blo 1028606 1548401 := bstep (se 2 (by rfl) ⟨580650, by rfl⟩ : syracuseStep 1548401 = 1161301) B1161301
theorem B1548419 : Blo 1028606 1548419 := bstep (se 1 (by rfl) ⟨1161314, by rfl⟩ : syracuseStep 1548419 = 2322629) B2322629
theorem B1548449 : Blo 1028606 1548449 := bstep (se 2 (by rfl) ⟨580668, by rfl⟩ : syracuseStep 1548449 = 1161337) B1161337
theorem B1548467 : Blo 1028606 1548467 := bstep (se 1 (by rfl) ⟨1161350, by rfl⟩ : syracuseStep 1548467 = 2322701) B2322701
theorem B1548497 : Blo 1028606 1548497 := bstep (se 2 (by rfl) ⟨580686, by rfl⟩ : syracuseStep 1548497 = 1161373) B1161373
theorem B1548515 : Blo 1028606 1548515 := bstep (se 1 (by rfl) ⟨1161386, by rfl⟩ : syracuseStep 1548515 = 2322773) B2322773
theorem B1548545 : Blo 1028606 1548545 := bstep (se 2 (by rfl) ⟨580704, by rfl⟩ : syracuseStep 1548545 = 1161409) B1161409
theorem B1548563 : Blo 1028606 1548563 := bstep (se 1 (by rfl) ⟨1161422, by rfl⟩ : syracuseStep 1548563 = 2322845) B2322845
theorem B1548593 : Blo 1028606 1548593 := bstep (se 2 (by rfl) ⟨580722, by rfl⟩ : syracuseStep 1548593 = 1161445) B1161445
theorem B1548611 : Blo 1028606 1548611 := bstep (se 1 (by rfl) ⟨1161458, by rfl⟩ : syracuseStep 1548611 = 2322917) B2322917
theorem B1548641 : Blo 1028606 1548641 := bstep (se 2 (by rfl) ⟨580740, by rfl⟩ : syracuseStep 1548641 = 1161481) B1161481
theorem B1548659 : Blo 1028606 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B1548689 : Blo 1028606 1548689 := bstep (se 2 (by rfl) ⟨580758, by rfl⟩ : syracuseStep 1548689 = 1161517) B1161517
theorem B1548707 : Blo 1028606 1548707 := bstep (se 1 (by rfl) ⟨1161530, by rfl⟩ : syracuseStep 1548707 = 2323061) B2323061
theorem B1548737 : Blo 1028606 1548737 := bstep (se 2 (by rfl) ⟨580776, by rfl⟩ : syracuseStep 1548737 = 1161553) B1161553
theorem B1548755 : Blo 1028606 1548755 := bstep (se 1 (by rfl) ⟨1161566, by rfl⟩ : syracuseStep 1548755 = 2323133) B2323133
theorem B5022179 : Blo 1028606 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B1548785 : Blo 1028606 1548785 := bstep (se 2 (by rfl) ⟨580794, by rfl⟩ : syracuseStep 1548785 = 1161589) B1161589
theorem B1548803 : Blo 1028606 1548803 := bstep (se 1 (by rfl) ⟨1161602, by rfl⟩ : syracuseStep 1548803 = 2323205) B2323205
theorem B5218829 : Blo 1028606 5218829 := bstep (se 3 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 5218829 = 1957061) B1957061
theorem B1548833 : Blo 1028606 1548833 := bstep (se 2 (by rfl) ⟨580812, by rfl⟩ : syracuseStep 1548833 = 1161625) B1161625
theorem B1548851 : Blo 1028606 1548851 := bstep (se 1 (by rfl) ⟨1161638, by rfl⟩ : syracuseStep 1548851 = 2323277) B2323277
theorem B3482189 : Blo 1028606 3482189 := bstep (se 3 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 3482189 = 1305821) B1305821
theorem B1548881 : Blo 1028606 1548881 := bstep (se 2 (by rfl) ⟨580830, by rfl⟩ : syracuseStep 1548881 = 1161661) B1161661
theorem B1548899 : Blo 1028606 1548899 := bstep (se 1 (by rfl) ⟨1161674, by rfl⟩ : syracuseStep 1548899 = 2323349) B2323349
theorem B3482243 : Blo 1028606 3482243 := bstep (se 1 (by rfl) ⟨2611682, by rfl⟩ : syracuseStep 3482243 = 5223365) B5223365
theorem B2204291 : Blo 1028606 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B5579441 : Blo 1028606 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B3482513 : Blo 1028606 3482513 := bstep (se 2 (by rfl) ⟨1305942, by rfl⟩ : syracuseStep 3482513 = 2611885) B2611885
theorem B6267917 : Blo 1028606 6267917 := bstep (se 3 (by rfl) ⟨1175234, by rfl⟩ : syracuseStep 6267917 = 2350469) B2350469
theorem B9905165 : Blo 1028606 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B1647683 : Blo 1028606 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B11150405 : Blo 1028606 11150405 := bstep (se 4 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 11150405 = 2090701) B2090701
theorem B1647811 : Blo 1028606 1647811 := bstep (se 1 (by rfl) ⟨1235858, by rfl⟩ : syracuseStep 1647811 = 2471717) B2471717
theorem B7841123 : Blo 1028606 7841123 := bstep (se 1 (by rfl) ⟨5880842, by rfl⟩ : syracuseStep 7841123 = 11761685) B11761685
theorem B2860397 : Blo 1028606 2860397 := bstep (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) B1072649
theorem B3909005 : Blo 1028606 3909005 := bstep (se 3 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 3909005 = 1465877) B1465877
theorem B3483053 : Blo 1028606 3483053 := bstep (se 3 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 3483053 = 1306145) B1306145
theorem B3483107 : Blo 1028606 3483107 := bstep (se 1 (by rfl) ⟨2612330, by rfl⟩ : syracuseStep 3483107 = 5224661) B5224661
theorem B4400689 : Blo 1028606 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B3483377 : Blo 1028606 3483377 := bstep (se 2 (by rfl) ⟨1306266, by rfl⟩ : syracuseStep 3483377 = 2612533) B2612533
theorem B1648529 : Blo 1028606 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B1648721 : Blo 1028606 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B1157251 : Blo 1028606 1157251 := bstep (se 1 (by rfl) ⟨867938, by rfl⟩ : syracuseStep 1157251 = 1735877) B1735877
theorem B3909809 : Blo 1028606 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B5810381 : Blo 1028606 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B3483917 : Blo 1028606 3483917 := bstep (se 3 (by rfl) ⟨653234, by rfl⟩ : syracuseStep 3483917 = 1306469) B1306469
theorem B1157395 : Blo 1028606 1157395 := bstep (se 1 (by rfl) ⟨868046, by rfl⟩ : syracuseStep 1157395 = 1736093) B1736093
theorem B3483971 : Blo 1028606 3483971 := bstep (se 1 (by rfl) ⟨2612978, by rfl⟩ : syracuseStep 3483971 = 5225957) B5225957
theorem B1157539 : Blo 1028606 1157539 := bstep (se 1 (by rfl) ⟨868154, by rfl⟩ : syracuseStep 1157539 = 1736309) B1736309
theorem B1157683 : Blo 1028606 1157683 := bstep (se 1 (by rfl) ⟨868262, by rfl⟩ : syracuseStep 1157683 = 1736525) B1736525
theorem B3484241 : Blo 1028606 3484241 := bstep (se 2 (by rfl) ⟨1306590, by rfl⟩ : syracuseStep 3484241 = 2613181) B2613181
theorem B17836685 : Blo 1028606 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B1157827 : Blo 1028606 1157827 := bstep (se 1 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 1157827 = 1736741) B1736741
theorem B3910477 : Blo 1028606 3910477 := bstep (se 3 (by rfl) ⟨733214, by rfl⟩ : syracuseStep 3910477 = 1466429) B1466429
theorem B1157971 : Blo 1028606 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1158115 : Blo 1028606 1158115 := bstep (se 1 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 1158115 = 1737173) B1737173
theorem B3484781 : Blo 1028606 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B1158259 : Blo 1028606 1158259 := bstep (se 1 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 1158259 = 1737389) B1737389
theorem B3484835 : Blo 1028606 3484835 := bstep (se 1 (by rfl) ⟨2613626, by rfl⟩ : syracuseStep 3484835 = 5227253) B5227253
theorem B5942513 : Blo 1028606 5942513 := bstep (se 2 (by rfl) ⟨2228442, by rfl⟩ : syracuseStep 5942513 = 4456885) B4456885
theorem B1158403 : Blo 1028606 1158403 := bstep (se 1 (by rfl) ⟨868802, by rfl⟩ : syracuseStep 1158403 = 1737605) B1737605
theorem B5221745 : Blo 1028606 5221745 := bstep (se 2 (by rfl) ⟨1958154, by rfl⟩ : syracuseStep 5221745 = 3916309) B3916309
theorem B1158547 : Blo 1028606 1158547 := bstep (se 1 (by rfl) ⟨868910, by rfl⟩ : syracuseStep 1158547 = 1737821) B1737821
theorem B4402637 : Blo 1028606 4402637 := bstep (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) B1650989
theorem B1158691 : Blo 1028606 1158691 := bstep (se 1 (by rfl) ⟨869018, by rfl⟩ : syracuseStep 1158691 = 1738037) B1738037
theorem B3911267 : Blo 1028606 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B1158835 : Blo 1028606 1158835 := bstep (se 1 (by rfl) ⟨869126, by rfl⟩ : syracuseStep 1158835 = 1738253) B1738253
theorem B13184693 : Blo 1028606 13184693 := bstep (se 5 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 13184693 = 1236065) B1236065
theorem B18820835 : Blo 1028606 18820835 := bstep (se 1 (by rfl) ⟨14115626, by rfl⟩ : syracuseStep 18820835 = 28231253) B28231253
theorem B1650451 : Blo 1028606 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B1158979 : Blo 1028606 1158979 := bstep (se 1 (by rfl) ⟨869234, by rfl⟩ : syracuseStep 1158979 = 1738469) B1738469
theorem B3714929 : Blo 1028606 3714929 := bstep (se 2 (by rfl) ⟨1393098, by rfl⟩ : syracuseStep 3714929 = 2786197) B2786197
theorem B1650547 : Blo 1028606 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1159123 : Blo 1028606 1159123 := bstep (se 1 (by rfl) ⟨869342, by rfl⟩ : syracuseStep 1159123 = 1738685) B1738685
theorem B1650707 : Blo 1028606 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B1159267 : Blo 1028606 1159267 := bstep (se 1 (by rfl) ⟨869450, by rfl⟩ : syracuseStep 1159267 = 1738901) B1738901
theorem B6697073 : Blo 1028606 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B3911921 : Blo 1028606 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1159411 : Blo 1028606 1159411 := bstep (se 1 (by rfl) ⟨869558, by rfl⟩ : syracuseStep 1159411 = 1739117) B1739117
theorem B4960561 : Blo 1028606 4960561 := bstep (se 2 (by rfl) ⟨1860210, by rfl⟩ : syracuseStep 4960561 = 3720421) B3720421
theorem B1159555 : Blo 1028606 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B1028611 : Blo 1028606 1028611 := bstep (se 1 (by rfl) ⟨771458, by rfl⟩ : syracuseStep 1028611 = 1542917) B1542917
theorem B1028627 : Blo 1028606 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B1159699 : Blo 1028606 1159699 := bstep (se 1 (by rfl) ⟨869774, by rfl⟩ : syracuseStep 1159699 = 1739549) B1739549
theorem B1028643 : Blo 1028606 1028643 := bstep (se 1 (by rfl) ⟨771482, by rfl⟩ : syracuseStep 1028643 = 1542965) B1542965
theorem B1028659 : Blo 1028606 1028659 := bstep (se 1 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 1028659 = 1542989) B1542989
theorem B1028675 : Blo 1028606 1028675 := bstep (se 1 (by rfl) ⟨771506, by rfl⟩ : syracuseStep 1028675 = 1543013) B1543013
theorem B1028691 : Blo 1028606 1028691 := bstep (se 1 (by rfl) ⟨771518, by rfl⟩ : syracuseStep 1028691 = 1543037) B1543037
theorem B1028707 : Blo 1028606 1028707 := bstep (se 1 (by rfl) ⟨771530, by rfl⟩ : syracuseStep 1028707 = 1543061) B1543061
theorem B9155171 : Blo 1028606 9155171 := bstep (se 1 (by rfl) ⟨6866378, by rfl⟩ : syracuseStep 9155171 = 13732757) B13732757
theorem B1028723 : Blo 1028606 1028723 := bstep (se 1 (by rfl) ⟨771542, by rfl⟩ : syracuseStep 1028723 = 1543085) B1543085
theorem B1028739 : Blo 1028606 1028739 := bstep (se 1 (by rfl) ⟨771554, by rfl⟩ : syracuseStep 1028739 = 1543109) B1543109
theorem B1028755 : Blo 1028606 1028755 := bstep (se 1 (by rfl) ⟨771566, by rfl⟩ : syracuseStep 1028755 = 1543133) B1543133
theorem B1028771 : Blo 1028606 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B1159843 : Blo 1028606 1159843 := bstep (se 1 (by rfl) ⟨869882, by rfl⟩ : syracuseStep 1159843 = 1739765) B1739765
theorem B1028787 : Blo 1028606 1028787 := bstep (se 1 (by rfl) ⟨771590, by rfl⟩ : syracuseStep 1028787 = 1543181) B1543181
theorem B1028803 : Blo 1028606 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B1028819 : Blo 1028606 1028819 := bstep (se 1 (by rfl) ⟨771614, by rfl⟩ : syracuseStep 1028819 = 1543229) B1543229
theorem B1028835 : Blo 1028606 1028835 := bstep (se 1 (by rfl) ⟨771626, by rfl⟩ : syracuseStep 1028835 = 1543253) B1543253
theorem B1028851 : Blo 1028606 1028851 := bstep (se 1 (by rfl) ⟨771638, by rfl⟩ : syracuseStep 1028851 = 1543277) B1543277
theorem B1028867 : Blo 1028606 1028867 := bstep (se 1 (by rfl) ⟨771650, by rfl⟩ : syracuseStep 1028867 = 1543301) B1543301
theorem B1028883 : Blo 1028606 1028883 := bstep (se 1 (by rfl) ⟨771662, by rfl⟩ : syracuseStep 1028883 = 1543325) B1543325
theorem B1028899 : Blo 1028606 1028899 := bstep (se 1 (by rfl) ⟨771674, by rfl⟩ : syracuseStep 1028899 = 1543349) B1543349
theorem B5223203 : Blo 1028606 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B1028915 : Blo 1028606 1028915 := bstep (se 1 (by rfl) ⟨771686, by rfl⟩ : syracuseStep 1028915 = 1543373) B1543373
theorem B1159987 : Blo 1028606 1159987 := bstep (se 1 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 1159987 = 1739981) B1739981
theorem B1028931 : Blo 1028606 1028931 := bstep (se 1 (by rfl) ⟨771698, by rfl⟩ : syracuseStep 1028931 = 1543397) B1543397
theorem B1028947 : Blo 1028606 1028947 := bstep (se 1 (by rfl) ⟨771710, by rfl⟩ : syracuseStep 1028947 = 1543421) B1543421
theorem B1028963 : Blo 1028606 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B1028979 : Blo 1028606 1028979 := bstep (se 1 (by rfl) ⟨771734, by rfl⟩ : syracuseStep 1028979 = 1543469) B1543469
theorem B1028995 : Blo 1028606 1028995 := bstep (se 1 (by rfl) ⟨771746, by rfl⟩ : syracuseStep 1028995 = 1543493) B1543493
theorem B53523341 : Blo 1028606 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B1029011 : Blo 1028606 1029011 := bstep (se 1 (by rfl) ⟨771758, by rfl⟩ : syracuseStep 1029011 = 1543517) B1543517
theorem B1029027 : Blo 1028606 1029027 := bstep (se 1 (by rfl) ⟨771770, by rfl⟩ : syracuseStep 1029027 = 1543541) B1543541
theorem B4699043 : Blo 1028606 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1029043 : Blo 1028606 1029043 := bstep (se 1 (by rfl) ⟨771782, by rfl⟩ : syracuseStep 1029043 = 1543565) B1543565
theorem B1029059 : Blo 1028606 1029059 := bstep (se 1 (by rfl) ⟨771794, by rfl⟩ : syracuseStep 1029059 = 1543589) B1543589
theorem B1160131 : Blo 1028606 1160131 := bstep (se 1 (by rfl) ⟨870098, by rfl⟩ : syracuseStep 1160131 = 1740197) B1740197
theorem B1029075 : Blo 1028606 1029075 := bstep (se 1 (by rfl) ⟨771806, by rfl⟩ : syracuseStep 1029075 = 1543613) B1543613
theorem B1651681 : Blo 1028606 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B1029091 : Blo 1028606 1029091 := bstep (se 1 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 1029091 = 1543637) B1543637
theorem B1029107 : Blo 1028606 1029107 := bstep (se 1 (by rfl) ⟨771830, by rfl⟩ : syracuseStep 1029107 = 1543661) B1543661
theorem B1029123 : Blo 1028606 1029123 := bstep (se 1 (by rfl) ⟨771842, by rfl⟩ : syracuseStep 1029123 = 1543685) B1543685
theorem B1029139 : Blo 1028606 1029139 := bstep (se 1 (by rfl) ⟨771854, by rfl⟩ : syracuseStep 1029139 = 1543709) B1543709
theorem B1029155 : Blo 1028606 1029155 := bstep (se 1 (by rfl) ⟨771866, by rfl⟩ : syracuseStep 1029155 = 1543733) B1543733
theorem B1029171 : Blo 1028606 1029171 := bstep (se 1 (by rfl) ⟨771878, by rfl⟩ : syracuseStep 1029171 = 1543757) B1543757
theorem B1029187 : Blo 1028606 1029187 := bstep (se 1 (by rfl) ⟨771890, by rfl⟩ : syracuseStep 1029187 = 1543781) B1543781
theorem B1029203 : Blo 1028606 1029203 := bstep (se 1 (by rfl) ⟨771902, by rfl⟩ : syracuseStep 1029203 = 1543805) B1543805
theorem B1160275 : Blo 1028606 1160275 := bstep (se 1 (by rfl) ⟨870206, by rfl⟩ : syracuseStep 1160275 = 1740413) B1740413
theorem B1029219 : Blo 1028606 1029219 := bstep (se 1 (by rfl) ⟨771914, by rfl⟩ : syracuseStep 1029219 = 1543829) B1543829
theorem B1029235 : Blo 1028606 1029235 := bstep (se 1 (by rfl) ⟨771926, by rfl⟩ : syracuseStep 1029235 = 1543853) B1543853
theorem B1029251 : Blo 1028606 1029251 := bstep (se 1 (by rfl) ⟨771938, by rfl⟩ : syracuseStep 1029251 = 1543877) B1543877
theorem B1029267 : Blo 1028606 1029267 := bstep (se 1 (by rfl) ⟨771950, by rfl⟩ : syracuseStep 1029267 = 1543901) B1543901
theorem B1029283 : Blo 1028606 1029283 := bstep (se 1 (by rfl) ⟨771962, by rfl⟩ : syracuseStep 1029283 = 1543925) B1543925
theorem B2929841 : Blo 1028606 2929841 := bstep (se 2 (by rfl) ⟨1098690, by rfl⟩ : syracuseStep 2929841 = 2197381) B2197381
theorem B1029299 : Blo 1028606 1029299 := bstep (se 1 (by rfl) ⟨771974, by rfl⟩ : syracuseStep 1029299 = 1543949) B1543949
theorem B1029315 : Blo 1028606 1029315 := bstep (se 1 (by rfl) ⟨771986, by rfl⟩ : syracuseStep 1029315 = 1543973) B1543973
theorem B1029331 : Blo 1028606 1029331 := bstep (se 1 (by rfl) ⟨771998, by rfl⟩ : syracuseStep 1029331 = 1543997) B1543997
theorem B1029347 : Blo 1028606 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B16954595 : Blo 1028606 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B1160419 : Blo 1028606 1160419 := bstep (se 1 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 1160419 = 1740629) B1740629
theorem B1029363 : Blo 1028606 1029363 := bstep (se 1 (by rfl) ⟨772022, by rfl⟩ : syracuseStep 1029363 = 1544045) B1544045
theorem B1029379 : Blo 1028606 1029379 := bstep (se 1 (by rfl) ⟨772034, by rfl⟩ : syracuseStep 1029379 = 1544069) B1544069
theorem B1029395 : Blo 1028606 1029395 := bstep (se 1 (by rfl) ⟨772046, by rfl⟩ : syracuseStep 1029395 = 1544093) B1544093
theorem B1029411 : Blo 1028606 1029411 := bstep (se 1 (by rfl) ⟨772058, by rfl⟩ : syracuseStep 1029411 = 1544117) B1544117
theorem B3716387 : Blo 1028606 3716387 := bstep (se 1 (by rfl) ⟨2787290, by rfl⟩ : syracuseStep 3716387 = 5574581) B5574581
theorem B1029427 : Blo 1028606 1029427 := bstep (se 1 (by rfl) ⟨772070, by rfl⟩ : syracuseStep 1029427 = 1544141) B1544141
theorem B1029443 : Blo 1028606 1029443 := bstep (se 1 (by rfl) ⟨772082, by rfl⟩ : syracuseStep 1029443 = 1544165) B1544165
theorem B1029459 : Blo 1028606 1029459 := bstep (se 1 (by rfl) ⟨772094, by rfl⟩ : syracuseStep 1029459 = 1544189) B1544189
theorem B1029475 : Blo 1028606 1029475 := bstep (se 1 (by rfl) ⟨772106, by rfl⟩ : syracuseStep 1029475 = 1544213) B1544213
theorem B2930033 : Blo 1028606 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B1029491 : Blo 1028606 1029491 := bstep (se 1 (by rfl) ⟨772118, by rfl⟩ : syracuseStep 1029491 = 1544237) B1544237
theorem B1160563 : Blo 1028606 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B1029507 : Blo 1028606 1029507 := bstep (se 1 (by rfl) ⟨772130, by rfl⟩ : syracuseStep 1029507 = 1544261) B1544261
theorem B1029523 : Blo 1028606 1029523 := bstep (se 1 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 1029523 = 1544285) B1544285
theorem B1029539 : Blo 1028606 1029539 := bstep (se 1 (by rfl) ⟨772154, by rfl⟩ : syracuseStep 1029539 = 1544309) B1544309
theorem B1029555 : Blo 1028606 1029555 := bstep (se 1 (by rfl) ⟨772166, by rfl⟩ : syracuseStep 1029555 = 1544333) B1544333
theorem B1029571 : Blo 1028606 1029571 := bstep (se 1 (by rfl) ⟨772178, by rfl⟩ : syracuseStep 1029571 = 1544357) B1544357
theorem B1029587 : Blo 1028606 1029587 := bstep (se 1 (by rfl) ⟨772190, by rfl⟩ : syracuseStep 1029587 = 1544381) B1544381
theorem B1029603 : Blo 1028606 1029603 := bstep (se 1 (by rfl) ⟨772202, by rfl⟩ : syracuseStep 1029603 = 1544405) B1544405
theorem B1029619 : Blo 1028606 1029619 := bstep (se 1 (by rfl) ⟨772214, by rfl⟩ : syracuseStep 1029619 = 1544429) B1544429
theorem B1029635 : Blo 1028606 1029635 := bstep (se 1 (by rfl) ⟨772226, by rfl⟩ : syracuseStep 1029635 = 1544453) B1544453
theorem B1160707 : Blo 1028606 1160707 := bstep (se 1 (by rfl) ⟨870530, by rfl⟩ : syracuseStep 1160707 = 1741061) B1741061
theorem B1029651 : Blo 1028606 1029651 := bstep (se 1 (by rfl) ⟨772238, by rfl⟩ : syracuseStep 1029651 = 1544477) B1544477
theorem B1029667 : Blo 1028606 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B1029683 : Blo 1028606 1029683 := bstep (se 1 (by rfl) ⟨772262, by rfl⟩ : syracuseStep 1029683 = 1544525) B1544525
theorem B1029699 : Blo 1028606 1029699 := bstep (se 1 (by rfl) ⟨772274, by rfl⟩ : syracuseStep 1029699 = 1544549) B1544549
theorem B5224013 : Blo 1028606 5224013 := bstep (se 3 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 5224013 = 1959005) B1959005
theorem B1029715 : Blo 1028606 1029715 := bstep (se 1 (by rfl) ⟨772286, by rfl⟩ : syracuseStep 1029715 = 1544573) B1544573
theorem B1029731 : Blo 1028606 1029731 := bstep (se 1 (by rfl) ⟨772298, by rfl⟩ : syracuseStep 1029731 = 1544597) B1544597
theorem B1029747 : Blo 1028606 1029747 := bstep (se 1 (by rfl) ⟨772310, by rfl⟩ : syracuseStep 1029747 = 1544621) B1544621
theorem B1029763 : Blo 1028606 1029763 := bstep (se 1 (by rfl) ⟨772322, by rfl⟩ : syracuseStep 1029763 = 1544645) B1544645
theorem B1029779 : Blo 1028606 1029779 := bstep (se 1 (by rfl) ⟨772334, by rfl⟩ : syracuseStep 1029779 = 1544669) B1544669
theorem B1160851 : Blo 1028606 1160851 := bstep (se 1 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 1160851 = 1741277) B1741277
theorem B1029795 : Blo 1028606 1029795 := bstep (se 1 (by rfl) ⟨772346, by rfl⟩ : syracuseStep 1029795 = 1544693) B1544693
theorem B3913379 : Blo 1028606 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B3913393 : Blo 1028606 3913393 := bstep (se 2 (by rfl) ⟨1467522, by rfl⟩ : syracuseStep 3913393 = 2935045) B2935045
theorem B1029811 : Blo 1028606 1029811 := bstep (se 1 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 1029811 = 1544717) B1544717
theorem B1029827 : Blo 1028606 1029827 := bstep (se 1 (by rfl) ⟨772370, by rfl⟩ : syracuseStep 1029827 = 1544741) B1544741
theorem B1029843 : Blo 1028606 1029843 := bstep (se 1 (by rfl) ⟨772382, by rfl⟩ : syracuseStep 1029843 = 1544765) B1544765
theorem B1029859 : Blo 1028606 1029859 := bstep (se 1 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 1029859 = 1544789) B1544789
theorem B1029875 : Blo 1028606 1029875 := bstep (se 1 (by rfl) ⟨772406, by rfl⟩ : syracuseStep 1029875 = 1544813) B1544813
theorem B1029891 : Blo 1028606 1029891 := bstep (se 1 (by rfl) ⟨772418, by rfl⟩ : syracuseStep 1029891 = 1544837) B1544837
theorem B1029907 : Blo 1028606 1029907 := bstep (se 1 (by rfl) ⟨772430, by rfl⟩ : syracuseStep 1029907 = 1544861) B1544861
theorem B1029923 : Blo 1028606 1029923 := bstep (se 1 (by rfl) ⟨772442, by rfl⟩ : syracuseStep 1029923 = 1544885) B1544885
theorem B1160995 : Blo 1028606 1160995 := bstep (se 1 (by rfl) ⟨870746, by rfl⟩ : syracuseStep 1160995 = 1741493) B1741493
theorem B1029939 : Blo 1028606 1029939 := bstep (se 1 (by rfl) ⟨772454, by rfl⟩ : syracuseStep 1029939 = 1544909) B1544909
theorem B1029955 : Blo 1028606 1029955 := bstep (se 1 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 1029955 = 1544933) B1544933
theorem B1029971 : Blo 1028606 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B1029987 : Blo 1028606 1029987 := bstep (se 1 (by rfl) ⟨772490, by rfl⟩ : syracuseStep 1029987 = 1544981) B1544981
theorem B1030003 : Blo 1028606 1030003 := bstep (se 1 (by rfl) ⟨772502, by rfl⟩ : syracuseStep 1030003 = 1545005) B1545005
theorem B1030019 : Blo 1028606 1030019 := bstep (se 1 (by rfl) ⟨772514, by rfl⟩ : syracuseStep 1030019 = 1545029) B1545029
theorem B1030035 : Blo 1028606 1030035 := bstep (se 1 (by rfl) ⟨772526, by rfl⟩ : syracuseStep 1030035 = 1545053) B1545053
theorem B1030051 : Blo 1028606 1030051 := bstep (se 1 (by rfl) ⟨772538, by rfl⟩ : syracuseStep 1030051 = 1545077) B1545077
theorem B1030067 : Blo 1028606 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B1161139 : Blo 1028606 1161139 := bstep (se 1 (by rfl) ⟨870854, by rfl⟩ : syracuseStep 1161139 = 1741709) B1741709
theorem B1030083 : Blo 1028606 1030083 := bstep (se 1 (by rfl) ⟨772562, by rfl⟩ : syracuseStep 1030083 = 1545125) B1545125
theorem B5879749 : Blo 1028606 5879749 := bstep (se 4 (by rfl) ⟨551226, by rfl⟩ : syracuseStep 5879749 = 1102453) B1102453
theorem B5027789 : Blo 1028606 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B1030099 : Blo 1028606 1030099 := bstep (se 1 (by rfl) ⟨772574, by rfl⟩ : syracuseStep 1030099 = 1545149) B1545149
theorem B1030115 : Blo 1028606 1030115 := bstep (se 1 (by rfl) ⟨772586, by rfl⟩ : syracuseStep 1030115 = 1545173) B1545173
theorem B1030131 : Blo 1028606 1030131 := bstep (se 1 (by rfl) ⟨772598, by rfl⟩ : syracuseStep 1030131 = 1545197) B1545197
theorem B1030147 : Blo 1028606 1030147 := bstep (se 1 (by rfl) ⟨772610, by rfl⟩ : syracuseStep 1030147 = 1545221) B1545221
theorem B1030163 : Blo 1028606 1030163 := bstep (se 1 (by rfl) ⟨772622, by rfl⟩ : syracuseStep 1030163 = 1545245) B1545245
theorem B1030179 : Blo 1028606 1030179 := bstep (se 1 (by rfl) ⟨772634, by rfl⟩ : syracuseStep 1030179 = 1545269) B1545269
theorem B1030195 : Blo 1028606 1030195 := bstep (se 1 (by rfl) ⟨772646, by rfl⟩ : syracuseStep 1030195 = 1545293) B1545293
theorem B1030211 : Blo 1028606 1030211 := bstep (se 1 (by rfl) ⟨772658, by rfl⟩ : syracuseStep 1030211 = 1545317) B1545317
theorem B1161283 : Blo 1028606 1161283 := bstep (se 1 (by rfl) ⟨870962, by rfl⟩ : syracuseStep 1161283 = 1741925) B1741925
theorem B1030227 : Blo 1028606 1030227 := bstep (se 1 (by rfl) ⟨772670, by rfl⟩ : syracuseStep 1030227 = 1545341) B1545341
theorem B1030243 : Blo 1028606 1030243 := bstep (se 1 (by rfl) ⟨772682, by rfl⟩ : syracuseStep 1030243 = 1545365) B1545365
theorem B1030259 : Blo 1028606 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B1030275 : Blo 1028606 1030275 := bstep (se 1 (by rfl) ⟨772706, by rfl⟩ : syracuseStep 1030275 = 1545413) B1545413
theorem B1030291 : Blo 1028606 1030291 := bstep (se 1 (by rfl) ⟨772718, by rfl⟩ : syracuseStep 1030291 = 1545437) B1545437
theorem B1030307 : Blo 1028606 1030307 := bstep (se 1 (by rfl) ⟨772730, by rfl⟩ : syracuseStep 1030307 = 1545461) B1545461
theorem B1030323 : Blo 1028606 1030323 := bstep (se 1 (by rfl) ⟨772742, by rfl⟩ : syracuseStep 1030323 = 1545485) B1545485
theorem B1030339 : Blo 1028606 1030339 := bstep (se 1 (by rfl) ⟨772754, by rfl⟩ : syracuseStep 1030339 = 1545509) B1545509
theorem B1030355 : Blo 1028606 1030355 := bstep (se 1 (by rfl) ⟨772766, by rfl⟩ : syracuseStep 1030355 = 1545533) B1545533
theorem B1161427 : Blo 1028606 1161427 := bstep (se 1 (by rfl) ⟨871070, by rfl⟩ : syracuseStep 1161427 = 1742141) B1742141
theorem B1030371 : Blo 1028606 1030371 := bstep (se 1 (by rfl) ⟨772778, by rfl⟩ : syracuseStep 1030371 = 1545557) B1545557
theorem B1030387 : Blo 1028606 1030387 := bstep (se 1 (by rfl) ⟨772790, by rfl⟩ : syracuseStep 1030387 = 1545581) B1545581
theorem B1030403 : Blo 1028606 1030403 := bstep (se 1 (by rfl) ⟨772802, by rfl⟩ : syracuseStep 1030403 = 1545605) B1545605
theorem B1030419 : Blo 1028606 1030419 := bstep (se 1 (by rfl) ⟨772814, by rfl⟩ : syracuseStep 1030419 = 1545629) B1545629
theorem B1030435 : Blo 1028606 1030435 := bstep (se 1 (by rfl) ⟨772826, by rfl⟩ : syracuseStep 1030435 = 1545653) B1545653
theorem B1030451 : Blo 1028606 1030451 := bstep (se 1 (by rfl) ⟨772838, by rfl⟩ : syracuseStep 1030451 = 1545677) B1545677
theorem B1030467 : Blo 1028606 1030467 := bstep (se 1 (by rfl) ⟨772850, by rfl⟩ : syracuseStep 1030467 = 1545701) B1545701
theorem B2931025 : Blo 1028606 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B1030483 : Blo 1028606 1030483 := bstep (se 1 (by rfl) ⟨772862, by rfl⟩ : syracuseStep 1030483 = 1545725) B1545725
theorem B1030499 : Blo 1028606 1030499 := bstep (se 1 (by rfl) ⟨772874, by rfl⟩ : syracuseStep 1030499 = 1545749) B1545749
theorem B1161571 : Blo 1028606 1161571 := bstep (se 1 (by rfl) ⟨871178, by rfl⟩ : syracuseStep 1161571 = 1742357) B1742357
theorem B1030515 : Blo 1028606 1030515 := bstep (se 1 (by rfl) ⟨772886, by rfl⟩ : syracuseStep 1030515 = 1545773) B1545773
theorem B1030531 : Blo 1028606 1030531 := bstep (se 1 (by rfl) ⟨772898, by rfl⟩ : syracuseStep 1030531 = 1545797) B1545797
theorem B1030547 : Blo 1028606 1030547 := bstep (se 1 (by rfl) ⟨772910, by rfl⟩ : syracuseStep 1030547 = 1545821) B1545821
theorem B1030563 : Blo 1028606 1030563 := bstep (se 1 (by rfl) ⟨772922, by rfl⟩ : syracuseStep 1030563 = 1545845) B1545845
theorem B1030579 : Blo 1028606 1030579 := bstep (se 1 (by rfl) ⟨772934, by rfl⟩ : syracuseStep 1030579 = 1545869) B1545869
theorem B1030595 : Blo 1028606 1030595 := bstep (se 1 (by rfl) ⟨772946, by rfl⟩ : syracuseStep 1030595 = 1545893) B1545893
theorem B1030611 : Blo 1028606 1030611 := bstep (se 1 (by rfl) ⟨772958, by rfl⟩ : syracuseStep 1030611 = 1545917) B1545917
theorem B1030627 : Blo 1028606 1030627 := bstep (se 1 (by rfl) ⟨772970, by rfl⟩ : syracuseStep 1030627 = 1545941) B1545941
theorem B1030643 : Blo 1028606 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B1030659 : Blo 1028606 1030659 := bstep (se 1 (by rfl) ⟨772994, by rfl⟩ : syracuseStep 1030659 = 1545989) B1545989
theorem B1030675 : Blo 1028606 1030675 := bstep (se 1 (by rfl) ⟨773006, by rfl⟩ : syracuseStep 1030675 = 1546013) B1546013
theorem B1030691 : Blo 1028606 1030691 := bstep (se 1 (by rfl) ⟨773018, by rfl⟩ : syracuseStep 1030691 = 1546037) B1546037
theorem B1030707 : Blo 1028606 1030707 := bstep (se 1 (by rfl) ⟨773030, by rfl⟩ : syracuseStep 1030707 = 1546061) B1546061
theorem B1030723 : Blo 1028606 1030723 := bstep (se 1 (by rfl) ⟨773042, by rfl⟩ : syracuseStep 1030723 = 1546085) B1546085
theorem B1391185 : Blo 1028606 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B1030739 : Blo 1028606 1030739 := bstep (se 1 (by rfl) ⟨773054, by rfl⟩ : syracuseStep 1030739 = 1546109) B1546109
theorem B2931299 : Blo 1028606 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B1587811 : Blo 1028606 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B1030755 : Blo 1028606 1030755 := bstep (se 1 (by rfl) ⟨773066, by rfl⟩ : syracuseStep 1030755 = 1546133) B1546133
theorem B1653347 : Blo 1028606 1653347 := bstep (se 1 (by rfl) ⟨1240010, by rfl⟩ : syracuseStep 1653347 = 2480021) B2480021
theorem B1030771 : Blo 1028606 1030771 := bstep (se 1 (by rfl) ⟨773078, by rfl⟩ : syracuseStep 1030771 = 1546157) B1546157
theorem B1030787 : Blo 1028606 1030787 := bstep (se 1 (by rfl) ⟨773090, by rfl⟩ : syracuseStep 1030787 = 1546181) B1546181
theorem B1030803 : Blo 1028606 1030803 := bstep (se 1 (by rfl) ⟨773102, by rfl⟩ : syracuseStep 1030803 = 1546205) B1546205
theorem B1030819 : Blo 1028606 1030819 := bstep (se 1 (by rfl) ⟨773114, by rfl⟩ : syracuseStep 1030819 = 1546229) B1546229
theorem B1030835 : Blo 1028606 1030835 := bstep (se 1 (by rfl) ⟨773126, by rfl⟩ : syracuseStep 1030835 = 1546253) B1546253
theorem B1030851 : Blo 1028606 1030851 := bstep (se 1 (by rfl) ⟨773138, by rfl⟩ : syracuseStep 1030851 = 1546277) B1546277
theorem B1030867 : Blo 1028606 1030867 := bstep (se 1 (by rfl) ⟨773150, by rfl⟩ : syracuseStep 1030867 = 1546301) B1546301
theorem B1030883 : Blo 1028606 1030883 := bstep (se 1 (by rfl) ⟨773162, by rfl⟩ : syracuseStep 1030883 = 1546325) B1546325
theorem B1653475 : Blo 1028606 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B1030899 : Blo 1028606 1030899 := bstep (se 1 (by rfl) ⟨773174, by rfl⟩ : syracuseStep 1030899 = 1546349) B1546349
theorem B1030915 : Blo 1028606 1030915 := bstep (se 1 (by rfl) ⟨773186, by rfl⟩ : syracuseStep 1030915 = 1546373) B1546373
theorem B1030931 : Blo 1028606 1030931 := bstep (se 1 (by rfl) ⟨773198, by rfl⟩ : syracuseStep 1030931 = 1546397) B1546397
theorem B2931491 : Blo 1028606 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B1030947 : Blo 1028606 1030947 := bstep (se 1 (by rfl) ⟨773210, by rfl⟩ : syracuseStep 1030947 = 1546421) B1546421
theorem B1653539 : Blo 1028606 1653539 := bstep (se 1 (by rfl) ⟨1240154, by rfl⟩ : syracuseStep 1653539 = 2480309) B2480309
theorem B1030963 : Blo 1028606 1030963 := bstep (se 1 (by rfl) ⟨773222, by rfl⟩ : syracuseStep 1030963 = 1546445) B1546445
theorem B1030979 : Blo 1028606 1030979 := bstep (se 1 (by rfl) ⟨773234, by rfl⟩ : syracuseStep 1030979 = 1546469) B1546469
theorem B1030995 : Blo 1028606 1030995 := bstep (se 1 (by rfl) ⟨773246, by rfl⟩ : syracuseStep 1030995 = 1546493) B1546493
theorem B1031011 : Blo 1028606 1031011 := bstep (se 1 (by rfl) ⟨773258, by rfl⟩ : syracuseStep 1031011 = 1546517) B1546517
theorem B1031027 : Blo 1028606 1031027 := bstep (se 1 (by rfl) ⟨773270, by rfl⟩ : syracuseStep 1031027 = 1546541) B1546541
theorem B1031043 : Blo 1028606 1031043 := bstep (se 1 (by rfl) ⟨773282, by rfl⟩ : syracuseStep 1031043 = 1546565) B1546565
theorem B1031059 : Blo 1028606 1031059 := bstep (se 1 (by rfl) ⟨773294, by rfl⟩ : syracuseStep 1031059 = 1546589) B1546589
theorem B1031075 : Blo 1028606 1031075 := bstep (se 1 (by rfl) ⟨773306, by rfl⟩ : syracuseStep 1031075 = 1546613) B1546613
theorem B1031091 : Blo 1028606 1031091 := bstep (se 1 (by rfl) ⟨773318, by rfl⟩ : syracuseStep 1031091 = 1546637) B1546637
theorem B1031107 : Blo 1028606 1031107 := bstep (se 1 (by rfl) ⟨773330, by rfl⟩ : syracuseStep 1031107 = 1546661) B1546661
theorem B1031123 : Blo 1028606 1031123 := bstep (se 1 (by rfl) ⟨773342, by rfl⟩ : syracuseStep 1031123 = 1546685) B1546685
theorem B1031139 : Blo 1028606 1031139 := bstep (se 1 (by rfl) ⟨773354, by rfl⟩ : syracuseStep 1031139 = 1546709) B1546709
theorem B1031155 : Blo 1028606 1031155 := bstep (se 1 (by rfl) ⟨773366, by rfl⟩ : syracuseStep 1031155 = 1546733) B1546733
theorem B1391617 : Blo 1028606 1391617 := bstep (se 2 (by rfl) ⟨521856, by rfl⟩ : syracuseStep 1391617 = 1043713) B1043713
theorem B1031171 : Blo 1028606 1031171 := bstep (se 1 (by rfl) ⟨773378, by rfl⟩ : syracuseStep 1031171 = 1546757) B1546757
theorem B1031187 : Blo 1028606 1031187 := bstep (se 1 (by rfl) ⟨773390, by rfl⟩ : syracuseStep 1031187 = 1546781) B1546781
theorem B1031203 : Blo 1028606 1031203 := bstep (se 1 (by rfl) ⟨773402, by rfl⟩ : syracuseStep 1031203 = 1546805) B1546805
theorem B1031219 : Blo 1028606 1031219 := bstep (se 1 (by rfl) ⟨773414, by rfl⟩ : syracuseStep 1031219 = 1546829) B1546829
theorem B1031235 : Blo 1028606 1031235 := bstep (se 1 (by rfl) ⟨773426, by rfl⟩ : syracuseStep 1031235 = 1546853) B1546853
theorem B3128401 : Blo 1028606 3128401 := bstep (se 2 (by rfl) ⟨1173150, by rfl⟩ : syracuseStep 3128401 = 2346301) B2346301
theorem B1588307 : Blo 1028606 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B1031251 : Blo 1028606 1031251 := bstep (se 1 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 1031251 = 1546877) B1546877
theorem B3914851 : Blo 1028606 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B1031267 : Blo 1028606 1031267 := bstep (se 1 (by rfl) ⟨773450, by rfl⟩ : syracuseStep 1031267 = 1546901) B1546901
theorem B1031283 : Blo 1028606 1031283 := bstep (se 1 (by rfl) ⟨773462, by rfl⟩ : syracuseStep 1031283 = 1546925) B1546925
theorem B1031299 : Blo 1028606 1031299 := bstep (se 1 (by rfl) ⟨773474, by rfl⟩ : syracuseStep 1031299 = 1546949) B1546949
theorem B1031315 : Blo 1028606 1031315 := bstep (se 1 (by rfl) ⟨773486, by rfl⟩ : syracuseStep 1031315 = 1546973) B1546973
theorem B1031331 : Blo 1028606 1031331 := bstep (se 1 (by rfl) ⟨773498, by rfl⟩ : syracuseStep 1031331 = 1546997) B1546997
theorem B1031347 : Blo 1028606 1031347 := bstep (se 1 (by rfl) ⟨773510, by rfl⟩ : syracuseStep 1031347 = 1547021) B1547021
theorem B1031363 : Blo 1028606 1031363 := bstep (se 1 (by rfl) ⟨773522, by rfl⟩ : syracuseStep 1031363 = 1547045) B1547045
theorem B1031379 : Blo 1028606 1031379 := bstep (se 1 (by rfl) ⟨773534, by rfl⟩ : syracuseStep 1031379 = 1547069) B1547069
theorem B1031395 : Blo 1028606 1031395 := bstep (se 1 (by rfl) ⟨773546, by rfl⟩ : syracuseStep 1031395 = 1547093) B1547093
theorem B1031411 : Blo 1028606 1031411 := bstep (se 1 (by rfl) ⟨773558, by rfl⟩ : syracuseStep 1031411 = 1547117) B1547117
theorem B1031427 : Blo 1028606 1031427 := bstep (se 1 (by rfl) ⟨773570, by rfl⟩ : syracuseStep 1031427 = 1547141) B1547141
theorem B1490179 : Blo 1028606 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B1654033 : Blo 1028606 1654033 := bstep (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) B1240525
theorem B1031443 : Blo 1028606 1031443 := bstep (se 1 (by rfl) ⟨773582, by rfl⟩ : syracuseStep 1031443 = 1547165) B1547165
theorem B1031459 : Blo 1028606 1031459 := bstep (se 1 (by rfl) ⟨773594, by rfl⟩ : syracuseStep 1031459 = 1547189) B1547189
theorem B1031475 : Blo 1028606 1031475 := bstep (se 1 (by rfl) ⟨773606, by rfl⟩ : syracuseStep 1031475 = 1547213) B1547213
theorem B1031491 : Blo 1028606 1031491 := bstep (se 1 (by rfl) ⟨773618, by rfl⟩ : syracuseStep 1031491 = 1547237) B1547237
theorem B9911621 : Blo 1028606 9911621 := bstep (se 4 (by rfl) ⟨929214, by rfl⟩ : syracuseStep 9911621 = 1858429) B1858429
theorem B1031507 : Blo 1028606 1031507 := bstep (se 1 (by rfl) ⟨773630, by rfl⟩ : syracuseStep 1031507 = 1547261) B1547261
theorem B1031523 : Blo 1028606 1031523 := bstep (se 1 (by rfl) ⟨773642, by rfl⟩ : syracuseStep 1031523 = 1547285) B1547285
theorem B1031539 : Blo 1028606 1031539 := bstep (se 1 (by rfl) ⟨773654, by rfl⟩ : syracuseStep 1031539 = 1547309) B1547309
theorem B1031555 : Blo 1028606 1031555 := bstep (se 1 (by rfl) ⟨773666, by rfl⟩ : syracuseStep 1031555 = 1547333) B1547333
theorem B4406669 : Blo 1028606 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B2604433 : Blo 1028606 2604433 := bstep (se 2 (by rfl) ⟨976662, by rfl⟩ : syracuseStep 2604433 = 1953325) B1953325
theorem B1031571 : Blo 1028606 1031571 := bstep (se 1 (by rfl) ⟨773678, by rfl⟩ : syracuseStep 1031571 = 1547357) B1547357
theorem B1031587 : Blo 1028606 1031587 := bstep (se 1 (by rfl) ⟨773690, by rfl⟩ : syracuseStep 1031587 = 1547381) B1547381
theorem B1031603 : Blo 1028606 1031603 := bstep (se 1 (by rfl) ⟨773702, by rfl⟩ : syracuseStep 1031603 = 1547405) B1547405
theorem B1031619 : Blo 1028606 1031619 := bstep (se 1 (by rfl) ⟨773714, by rfl⟩ : syracuseStep 1031619 = 1547429) B1547429
theorem B7421381 : Blo 1028606 7421381 := bstep (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) B1391509
theorem B1031635 : Blo 1028606 1031635 := bstep (se 1 (by rfl) ⟨773726, by rfl⟩ : syracuseStep 1031635 = 1547453) B1547453
theorem B1031651 : Blo 1028606 1031651 := bstep (se 1 (by rfl) ⟨773738, by rfl⟩ : syracuseStep 1031651 = 1547477) B1547477
theorem B1031667 : Blo 1028606 1031667 := bstep (se 1 (by rfl) ⟨773750, by rfl⟩ : syracuseStep 1031667 = 1547501) B1547501
theorem B1031683 : Blo 1028606 1031683 := bstep (se 1 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 1031683 = 1547525) B1547525
theorem B1031699 : Blo 1028606 1031699 := bstep (se 1 (by rfl) ⟨773774, by rfl⟩ : syracuseStep 1031699 = 1547549) B1547549
theorem B1031715 : Blo 1028606 1031715 := bstep (se 1 (by rfl) ⟨773786, by rfl⟩ : syracuseStep 1031715 = 1547573) B1547573
theorem B1031731 : Blo 1028606 1031731 := bstep (se 1 (by rfl) ⟨773798, by rfl⟩ : syracuseStep 1031731 = 1547597) B1547597
theorem B77151797 : Blo 1028606 77151797 := bstep (se 5 (by rfl) ⟨3616490, by rfl⟩ : syracuseStep 77151797 = 7232981) B7232981
theorem B1031747 : Blo 1028606 1031747 := bstep (se 1 (by rfl) ⟨773810, by rfl⟩ : syracuseStep 1031747 = 1547621) B1547621
theorem B2932301 : Blo 1028606 2932301 := bstep (se 3 (by rfl) ⟨549806, by rfl⟩ : syracuseStep 2932301 = 1099613) B1099613
theorem B1031763 : Blo 1028606 1031763 := bstep (se 1 (by rfl) ⟨773822, by rfl⟩ : syracuseStep 1031763 = 1547645) B1547645
theorem B1031779 : Blo 1028606 1031779 := bstep (se 1 (by rfl) ⟨773834, by rfl⟩ : syracuseStep 1031779 = 1547669) B1547669
theorem B1031795 : Blo 1028606 1031795 := bstep (se 1 (by rfl) ⟨773846, by rfl⟩ : syracuseStep 1031795 = 1547693) B1547693
theorem B1031811 : Blo 1028606 1031811 := bstep (se 1 (by rfl) ⟨773858, by rfl⟩ : syracuseStep 1031811 = 1547717) B1547717
theorem B1031827 : Blo 1028606 1031827 := bstep (se 1 (by rfl) ⟨773870, by rfl⟩ : syracuseStep 1031827 = 1547741) B1547741
theorem B2604707 : Blo 1028606 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B3718819 : Blo 1028606 3718819 := bstep (se 1 (by rfl) ⟨2789114, by rfl⟩ : syracuseStep 3718819 = 5578229) B5578229
theorem B1031843 : Blo 1028606 1031843 := bstep (se 1 (by rfl) ⟨773882, by rfl⟩ : syracuseStep 1031843 = 1547765) B1547765
theorem B6602417 : Blo 1028606 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B1031859 : Blo 1028606 1031859 := bstep (se 1 (by rfl) ⟨773894, by rfl⟩ : syracuseStep 1031859 = 1547789) B1547789
theorem B1031875 : Blo 1028606 1031875 := bstep (se 1 (by rfl) ⟨773906, by rfl⟩ : syracuseStep 1031875 = 1547813) B1547813
theorem B1031891 : Blo 1028606 1031891 := bstep (se 1 (by rfl) ⟨773918, by rfl⟩ : syracuseStep 1031891 = 1547837) B1547837
theorem B4407011 : Blo 1028606 4407011 := bstep (se 1 (by rfl) ⟨3305258, by rfl⟩ : syracuseStep 4407011 = 6610517) B6610517
theorem B1031907 : Blo 1028606 1031907 := bstep (se 1 (by rfl) ⟨773930, by rfl⟩ : syracuseStep 1031907 = 1547861) B1547861
theorem B1031923 : Blo 1028606 1031923 := bstep (se 1 (by rfl) ⟨773942, by rfl⟩ : syracuseStep 1031923 = 1547885) B1547885
theorem B2932483 : Blo 1028606 2932483 := bstep (se 1 (by rfl) ⟨2199362, by rfl⟩ : syracuseStep 2932483 = 4398725) B4398725
theorem B1031939 : Blo 1028606 1031939 := bstep (se 1 (by rfl) ⟨773954, by rfl⟩ : syracuseStep 1031939 = 1547909) B1547909
theorem B1031955 : Blo 1028606 1031955 := bstep (se 1 (by rfl) ⟨773966, by rfl⟩ : syracuseStep 1031955 = 1547933) B1547933
theorem B1031971 : Blo 1028606 1031971 := bstep (se 1 (by rfl) ⟨773978, by rfl⟩ : syracuseStep 1031971 = 1547957) B1547957
theorem B1031987 : Blo 1028606 1031987 := bstep (se 1 (by rfl) ⟨773990, by rfl⟩ : syracuseStep 1031987 = 1547981) B1547981
theorem B1032003 : Blo 1028606 1032003 := bstep (se 1 (by rfl) ⟨774002, by rfl⟩ : syracuseStep 1032003 = 1548005) B1548005
theorem B1032019 : Blo 1028606 1032019 := bstep (se 1 (by rfl) ⟨774014, by rfl⟩ : syracuseStep 1032019 = 1548029) B1548029
theorem B2604899 : Blo 1028606 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B1032035 : Blo 1028606 1032035 := bstep (se 1 (by rfl) ⟨774026, by rfl⟩ : syracuseStep 1032035 = 1548053) B1548053
theorem B1032051 : Blo 1028606 1032051 := bstep (se 1 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 1032051 = 1548077) B1548077
theorem B1032067 : Blo 1028606 1032067 := bstep (se 1 (by rfl) ⟨774050, by rfl⟩ : syracuseStep 1032067 = 1548101) B1548101
theorem B1032083 : Blo 1028606 1032083 := bstep (se 1 (by rfl) ⟨774062, by rfl⟩ : syracuseStep 1032083 = 1548125) B1548125
theorem B1392547 : Blo 1028606 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B1032099 : Blo 1028606 1032099 := bstep (se 1 (by rfl) ⟨774074, by rfl⟩ : syracuseStep 1032099 = 1548149) B1548149
theorem B1032115 : Blo 1028606 1032115 := bstep (se 1 (by rfl) ⟨774086, by rfl⟩ : syracuseStep 1032115 = 1548173) B1548173
theorem B1032131 : Blo 1028606 1032131 := bstep (se 1 (by rfl) ⟨774098, by rfl⟩ : syracuseStep 1032131 = 1548197) B1548197
theorem B1032147 : Blo 1028606 1032147 := bstep (se 1 (by rfl) ⟨774110, by rfl⟩ : syracuseStep 1032147 = 1548221) B1548221
theorem B1392611 : Blo 1028606 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B1032163 : Blo 1028606 1032163 := bstep (se 1 (by rfl) ⟨774122, by rfl⟩ : syracuseStep 1032163 = 1548245) B1548245
theorem B1032179 : Blo 1028606 1032179 := bstep (se 1 (by rfl) ⟨774134, by rfl⟩ : syracuseStep 1032179 = 1548269) B1548269
theorem B1032195 : Blo 1028606 1032195 := bstep (se 1 (by rfl) ⟨774146, by rfl⟩ : syracuseStep 1032195 = 1548293) B1548293
theorem B1032211 : Blo 1028606 1032211 := bstep (se 1 (by rfl) ⟨774158, by rfl⟩ : syracuseStep 1032211 = 1548317) B1548317
theorem B1032227 : Blo 1028606 1032227 := bstep (se 1 (by rfl) ⟨774170, by rfl⟩ : syracuseStep 1032227 = 1548341) B1548341
theorem B1032243 : Blo 1028606 1032243 := bstep (se 1 (by rfl) ⟨774182, by rfl⟩ : syracuseStep 1032243 = 1548365) B1548365
theorem B1032259 : Blo 1028606 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B1032275 : Blo 1028606 1032275 := bstep (se 1 (by rfl) ⟨774206, by rfl⟩ : syracuseStep 1032275 = 1548413) B1548413
theorem B6275171 : Blo 1028606 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B1032291 : Blo 1028606 1032291 := bstep (se 1 (by rfl) ⟨774218, by rfl⟩ : syracuseStep 1032291 = 1548437) B1548437
theorem B1032307 : Blo 1028606 1032307 := bstep (se 1 (by rfl) ⟨774230, by rfl⟩ : syracuseStep 1032307 = 1548461) B1548461
theorem B1032323 : Blo 1028606 1032323 := bstep (se 1 (by rfl) ⟨774242, by rfl⟩ : syracuseStep 1032323 = 1548485) B1548485
theorem B1032339 : Blo 1028606 1032339 := bstep (se 1 (by rfl) ⟨774254, by rfl⟩ : syracuseStep 1032339 = 1548509) B1548509
theorem B1032355 : Blo 1028606 1032355 := bstep (se 1 (by rfl) ⟨774266, by rfl⟩ : syracuseStep 1032355 = 1548533) B1548533
theorem B4407473 : Blo 1028606 4407473 := bstep (se 2 (by rfl) ⟨1652802, by rfl⟩ : syracuseStep 4407473 = 3305605) B3305605
theorem B1032371 : Blo 1028606 1032371 := bstep (se 1 (by rfl) ⟨774278, by rfl⟩ : syracuseStep 1032371 = 1548557) B1548557
theorem B1032387 : Blo 1028606 1032387 := bstep (se 1 (by rfl) ⟨774290, by rfl⟩ : syracuseStep 1032387 = 1548581) B1548581
theorem B7815365 : Blo 1028606 7815365 := bstep (se 4 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 7815365 = 1465381) B1465381
theorem B1032403 : Blo 1028606 1032403 := bstep (se 1 (by rfl) ⟨774302, by rfl⟩ : syracuseStep 1032403 = 1548605) B1548605
theorem B1032419 : Blo 1028606 1032419 := bstep (se 1 (by rfl) ⟨774314, by rfl⟩ : syracuseStep 1032419 = 1548629) B1548629
theorem B2932973 : Blo 1028606 2932973 := bstep (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) B1099865
theorem B1032435 : Blo 1028606 1032435 := bstep (se 1 (by rfl) ⟨774326, by rfl⟩ : syracuseStep 1032435 = 1548653) B1548653
theorem B1032451 : Blo 1028606 1032451 := bstep (se 1 (by rfl) ⟨774338, by rfl⟩ : syracuseStep 1032451 = 1548677) B1548677
theorem B1032467 : Blo 1028606 1032467 := bstep (se 1 (by rfl) ⟨774350, by rfl⟩ : syracuseStep 1032467 = 1548701) B1548701
theorem B1032483 : Blo 1028606 1032483 := bstep (se 1 (by rfl) ⟨774362, by rfl⟩ : syracuseStep 1032483 = 1548725) B1548725
theorem B1032499 : Blo 1028606 1032499 := bstep (se 1 (by rfl) ⟨774374, by rfl⟩ : syracuseStep 1032499 = 1548749) B1548749
theorem B1032515 : Blo 1028606 1032515 := bstep (se 1 (by rfl) ⟨774386, by rfl⟩ : syracuseStep 1032515 = 1548773) B1548773
theorem B1032531 : Blo 1028606 1032531 := bstep (se 1 (by rfl) ⟨774398, by rfl⟩ : syracuseStep 1032531 = 1548797) B1548797
theorem B1032547 : Blo 1028606 1032547 := bstep (se 1 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 1032547 = 1548821) B1548821
theorem B1032563 : Blo 1028606 1032563 := bstep (se 1 (by rfl) ⟨774422, by rfl⟩ : syracuseStep 1032563 = 1548845) B1548845
theorem B1032579 : Blo 1028606 1032579 := bstep (se 1 (by rfl) ⟨774434, by rfl⟩ : syracuseStep 1032579 = 1548869) B1548869
theorem B1032595 : Blo 1028606 1032595 := bstep (se 1 (by rfl) ⟨774446, by rfl⟩ : syracuseStep 1032595 = 1548893) B1548893
theorem B5226929 : Blo 1028606 5226929 := bstep (se 2 (by rfl) ⟨1960098, by rfl⟩ : syracuseStep 5226929 = 3920197) B3920197
theorem B3719857 : Blo 1028606 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B1098451 : Blo 1028606 1098451 := bstep (se 1 (by rfl) ⟨823838, by rfl⟩ : syracuseStep 1098451 = 1647677) B1647677
theorem B2605841 : Blo 1028606 2605841 := bstep (se 2 (by rfl) ⟨977190, by rfl⟩ : syracuseStep 2605841 = 1954381) B1954381
theorem B2605891 : Blo 1028606 2605891 := bstep (se 1 (by rfl) ⟨1954418, by rfl⟩ : syracuseStep 2605891 = 3908837) B3908837
theorem B3720077 : Blo 1028606 3720077 := bstep (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) B1395029
theorem B2606033 : Blo 1028606 2606033 := bstep (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) B1954525
theorem B3917069 : Blo 1028606 3917069 := bstep (se 3 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 3917069 = 1468901) B1468901
theorem B1983779 : Blo 1028606 1983779 := bstep (se 1 (by rfl) ⟨1487834, by rfl⟩ : syracuseStep 1983779 = 2975669) B2975669
theorem B2934157 : Blo 1028606 2934157 := bstep (se 3 (by rfl) ⟨550154, by rfl⟩ : syracuseStep 2934157 = 1100309) B1100309
theorem B3720653 : Blo 1028606 3720653 := bstep (se 3 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 3720653 = 1395245) B1395245
theorem B8799941 : Blo 1028606 8799941 := bstep (se 4 (by rfl) ⟨824994, by rfl⟩ : syracuseStep 8799941 = 1649989) B1649989
theorem B2607025 : Blo 1028606 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B2476003 : Blo 1028606 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B1591331 : Blo 1028606 1591331 := bstep (se 1 (by rfl) ⟨1193498, by rfl⟩ : syracuseStep 1591331 = 2386997) B2386997
theorem B6604877 : Blo 1028606 6604877 := bstep (se 3 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 6604877 = 2476829) B2476829
theorem B1853585 : Blo 1028606 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B2607299 : Blo 1028606 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B3131747 : Blo 1028606 3131747 := bstep (se 1 (by rfl) ⟨2348810, by rfl⟩ : syracuseStep 3131747 = 4697621) B4697621
theorem B2607491 : Blo 1028606 2607491 := bstep (se 1 (by rfl) ⟨1955618, by rfl⟩ : syracuseStep 2607491 = 3911237) B3911237
theorem B2935217 : Blo 1028606 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B11127395 : Blo 1028606 11127395 := bstep (se 1 (by rfl) ⟨8345546, by rfl⟩ : syracuseStep 11127395 = 16691093) B16691093
theorem B2476675 : Blo 1028606 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B3132209 : Blo 1028606 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B6278093 : Blo 1028606 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B2477137 : Blo 1028606 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B2935889 : Blo 1028606 2935889 := bstep (se 2 (by rfl) ⟨1100958, by rfl⟩ : syracuseStep 2935889 = 2201917) B2201917
theorem B2477233 : Blo 1028606 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B3525869 : Blo 1028606 3525869 := bstep (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) B1322201
theorem B11128049 : Blo 1028606 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B2608433 : Blo 1028606 2608433 := bstep (se 2 (by rfl) ⟨978162, by rfl⟩ : syracuseStep 2608433 = 1956325) B1956325
theorem B2608483 : Blo 1028606 2608483 := bstep (se 1 (by rfl) ⟨1956362, by rfl⟩ : syracuseStep 2608483 = 3912725) B3912725
theorem B2608625 : Blo 1028606 2608625 := bstep (se 2 (by rfl) ⟨978234, by rfl⟩ : syracuseStep 2608625 = 1956469) B1956469
theorem B1855057 : Blo 1028606 1855057 := bstep (se 2 (by rfl) ⟨695646, by rfl⟩ : syracuseStep 1855057 = 1391293) B1391293
theorem B2379377 : Blo 1028606 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B1953553 : Blo 1028606 1953553 := bstep (se 2 (by rfl) ⟨732582, by rfl⟩ : syracuseStep 1953553 = 1465165) B1465165
theorem B3821347 : Blo 1028606 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2936675 : Blo 1028606 2936675 := bstep (se 1 (by rfl) ⟨2202506, by rfl⟩ : syracuseStep 2936675 = 4405013) B4405013
theorem B1953713 : Blo 1028606 1953713 := bstep (se 2 (by rfl) ⟨732642, by rfl⟩ : syracuseStep 1953713 = 1465285) B1465285
theorem B3919985 : Blo 1028606 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B1855619 : Blo 1028606 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B2314385 : Blo 1028606 2314385 := bstep (se 2 (by rfl) ⟨867894, by rfl⟩ : syracuseStep 2314385 = 1735789) B1735789
theorem B1101971 : Blo 1028606 1101971 := bstep (se 1 (by rfl) ⟨826478, by rfl⟩ : syracuseStep 1101971 = 1652957) B1652957
theorem B2314403 : Blo 1028606 2314403 := bstep (se 1 (by rfl) ⟨1735802, by rfl⟩ : syracuseStep 2314403 = 3471605) B3471605
theorem B2937005 : Blo 1028606 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B2937073 : Blo 1028606 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B6607109 : Blo 1028606 6607109 := bstep (se 4 (by rfl) ⟨619416, by rfl⟩ : syracuseStep 6607109 = 1238833) B1238833
theorem B2642225 : Blo 1028606 2642225 := bstep (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) B1981669
theorem B1954115 : Blo 1028606 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B2314673 : Blo 1028606 2314673 := bstep (se 2 (by rfl) ⟨868002, by rfl⟩ : syracuseStep 2314673 = 1736005) B1736005
theorem B2314691 : Blo 1028606 2314691 := bstep (se 1 (by rfl) ⟨1736018, by rfl⟩ : syracuseStep 2314691 = 3472037) B3472037
theorem B2609617 : Blo 1028606 2609617 := bstep (se 2 (by rfl) ⟨978606, by rfl⟩ : syracuseStep 2609617 = 1957213) B1957213
theorem B11162083 : Blo 1028606 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B2937347 : Blo 1028606 2937347 := bstep (se 1 (by rfl) ⟨2203010, by rfl⟩ : syracuseStep 2937347 = 4406021) B4406021
theorem B3297955 : Blo 1028606 3297955 := bstep (se 1 (by rfl) ⟨2473466, by rfl⟩ : syracuseStep 3297955 = 4946933) B4946933
theorem B2314961 : Blo 1028606 2314961 := bstep (se 2 (by rfl) ⟨868110, by rfl⟩ : syracuseStep 2314961 = 1736221) B1736221
theorem B2314979 : Blo 1028606 2314979 := bstep (se 1 (by rfl) ⟨1736234, by rfl⟩ : syracuseStep 2314979 = 3472469) B3472469
theorem B2609891 : Blo 1028606 2609891 := bstep (se 1 (by rfl) ⟨1957418, by rfl⟩ : syracuseStep 2609891 = 3914837) B3914837
theorem B2610083 : Blo 1028606 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B2315249 : Blo 1028606 2315249 := bstep (se 2 (by rfl) ⟨868218, by rfl⟩ : syracuseStep 2315249 = 1736437) B1736437
theorem B2315267 : Blo 1028606 2315267 := bstep (se 1 (by rfl) ⟨1736450, by rfl⟩ : syracuseStep 2315267 = 3472901) B3472901
theorem B4183139 : Blo 1028606 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1856657 : Blo 1028606 1856657 := bstep (se 2 (by rfl) ⟨696246, by rfl⟩ : syracuseStep 1856657 = 1392493) B1392493
theorem B1955011 : Blo 1028606 1955011 := bstep (se 1 (by rfl) ⟨1466258, by rfl⟩ : syracuseStep 1955011 = 2932517) B2932517
theorem B2315537 : Blo 1028606 2315537 := bstep (se 2 (by rfl) ⟨868326, by rfl⟩ : syracuseStep 2315537 = 1736653) B1736653
theorem B2315555 : Blo 1028606 2315555 := bstep (se 1 (by rfl) ⟨1736666, by rfl⟩ : syracuseStep 2315555 = 3473333) B3473333
theorem B2938189 : Blo 1028606 2938189 := bstep (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) B1101821
theorem B1955171 : Blo 1028606 1955171 := bstep (se 1 (by rfl) ⟨1466378, by rfl⟩ : syracuseStep 1955171 = 2932757) B2932757
theorem B7919045 : Blo 1028606 7919045 := bstep (se 4 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 7919045 = 1484821) B1484821
theorem B2938349 : Blo 1028606 2938349 := bstep (se 3 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 2938349 = 1101881) B1101881
theorem B2315825 : Blo 1028606 2315825 := bstep (se 2 (by rfl) ⟨868434, by rfl⟩ : syracuseStep 2315825 = 1736869) B1736869
theorem B2315843 : Blo 1028606 2315843 := bstep (se 1 (by rfl) ⟨1736882, by rfl⟩ : syracuseStep 2315843 = 3473765) B3473765
theorem B2938531 : Blo 1028606 2938531 := bstep (se 1 (by rfl) ⟨2203898, by rfl⟩ : syracuseStep 2938531 = 4407797) B4407797
theorem B8345285 : Blo 1028606 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B3528497 : Blo 1028606 3528497 := bstep (se 2 (by rfl) ⟨1323186, by rfl⟩ : syracuseStep 3528497 = 2646373) B2646373
theorem B2643779 : Blo 1028606 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B2316113 : Blo 1028606 2316113 := bstep (se 2 (by rfl) ⟨868542, by rfl⟩ : syracuseStep 2316113 = 1737085) B1737085
theorem B2611025 : Blo 1028606 2611025 := bstep (se 2 (by rfl) ⟨979134, by rfl⟩ : syracuseStep 2611025 = 1958269) B1958269
theorem B2316131 : Blo 1028606 2316131 := bstep (se 1 (by rfl) ⟨1737098, by rfl⟩ : syracuseStep 2316131 = 3474197) B3474197
theorem B2611075 : Blo 1028606 2611075 := bstep (se 1 (by rfl) ⟨1958306, by rfl⟩ : syracuseStep 2611075 = 3916613) B3916613
theorem B7821197 : Blo 1028606 7821197 := bstep (se 3 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 7821197 = 2932949) B2932949
theorem B2643971 : Blo 1028606 2643971 := bstep (se 1 (by rfl) ⟨1982978, by rfl⟩ : syracuseStep 2643971 = 3965957) B3965957
theorem B2611217 : Blo 1028606 2611217 := bstep (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) B1958413
theorem B2316401 : Blo 1028606 2316401 := bstep (se 2 (by rfl) ⟨868650, by rfl⟩ : syracuseStep 2316401 = 1737301) B1737301
theorem B2316419 : Blo 1028606 2316419 := bstep (se 1 (by rfl) ⟨1737314, by rfl⟩ : syracuseStep 2316419 = 3474629) B3474629
theorem B2316689 : Blo 1028606 2316689 := bstep (se 2 (by rfl) ⟨868758, by rfl⟩ : syracuseStep 2316689 = 1737517) B1737517
theorem B1956241 : Blo 1028606 1956241 := bstep (se 2 (by rfl) ⟨733590, by rfl⟩ : syracuseStep 1956241 = 1467181) B1467181
theorem B2316707 : Blo 1028606 2316707 := bstep (se 1 (by rfl) ⟨1737530, by rfl⟩ : syracuseStep 2316707 = 3475061) B3475061
theorem B2316977 : Blo 1028606 2316977 := bstep (se 2 (by rfl) ⟨868866, by rfl⟩ : syracuseStep 2316977 = 1737733) B1737733
theorem B2316995 : Blo 1028606 2316995 := bstep (se 1 (by rfl) ⟨1737746, by rfl⟩ : syracuseStep 2316995 = 3475493) B3475493
theorem B1465057 : Blo 1028606 1465057 := bstep (se 2 (by rfl) ⟨549396, by rfl⟩ : syracuseStep 1465057 = 1098793) B1098793
theorem B3300173 : Blo 1028606 3300173 := bstep (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) B1237565
theorem B4709261 : Blo 1028606 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B1858481 : Blo 1028606 1858481 := bstep (se 2 (by rfl) ⟨696930, by rfl⟩ : syracuseStep 1858481 = 1393861) B1393861
theorem B2317265 : Blo 1028606 2317265 := bstep (se 2 (by rfl) ⟨868974, by rfl⟩ : syracuseStep 2317265 = 1737949) B1737949
theorem B2317283 : Blo 1028606 2317283 := bstep (se 1 (by rfl) ⟨1737962, by rfl⟩ : syracuseStep 2317283 = 3475925) B3475925
theorem B13229027 : Blo 1028606 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B2612209 : Blo 1028606 2612209 := bstep (se 2 (by rfl) ⟨979578, by rfl⟩ : syracuseStep 2612209 = 1959157) B1959157
theorem B2939921 : Blo 1028606 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B1465393 : Blo 1028606 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B2317553 : Blo 1028606 2317553 := bstep (se 2 (by rfl) ⟨869082, by rfl⟩ : syracuseStep 2317553 = 1738165) B1738165
theorem B3300593 : Blo 1028606 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B2153731 : Blo 1028606 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B2317571 : Blo 1028606 2317571 := bstep (se 1 (by rfl) ⟨1738178, by rfl⟩ : syracuseStep 2317571 = 3476357) B3476357
theorem B2612483 : Blo 1028606 2612483 := bstep (se 1 (by rfl) ⟨1959362, by rfl⟩ : syracuseStep 2612483 = 3918725) B3918725
theorem B1760609 : Blo 1028606 1760609 := bstep (se 2 (by rfl) ⟨660228, by rfl⟩ : syracuseStep 1760609 = 1320457) B1320457
theorem B1301923 : Blo 1028606 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1957297 : Blo 1028606 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B2612675 : Blo 1028606 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B2317841 : Blo 1028606 2317841 := bstep (se 2 (by rfl) ⟨869190, by rfl⟩ : syracuseStep 2317841 = 1738381) B1738381
theorem B2317859 : Blo 1028606 2317859 := bstep (se 1 (by rfl) ⟨1738394, by rfl⟩ : syracuseStep 2317859 = 3476789) B3476789
theorem B2088497 : Blo 1028606 2088497 := bstep (se 2 (by rfl) ⟨783186, by rfl⟩ : syracuseStep 2088497 = 1566373) B1566373
theorem B1465985 : Blo 1028606 1465985 := bstep (se 2 (by rfl) ⟨549744, by rfl⟩ : syracuseStep 1465985 = 1099489) B1099489
theorem B17587853 : Blo 1028606 17587853 := bstep (se 3 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 17587853 = 6595445) B6595445
theorem B2318129 : Blo 1028606 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B2318147 : Blo 1028606 2318147 := bstep (se 1 (by rfl) ⟨1738610, by rfl⟩ : syracuseStep 2318147 = 3477221) B3477221
theorem B1957699 : Blo 1028606 1957699 := bstep (se 1 (by rfl) ⟨1468274, by rfl⟩ : syracuseStep 1957699 = 2936549) B2936549
theorem B1957745 : Blo 1028606 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B1302419 : Blo 1028606 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B2318417 : Blo 1028606 2318417 := bstep (se 2 (by rfl) ⟨869406, by rfl⟩ : syracuseStep 2318417 = 1738813) B1738813
theorem B2318435 : Blo 1028606 2318435 := bstep (se 1 (by rfl) ⟨1738826, by rfl⟩ : syracuseStep 2318435 = 3477653) B3477653
theorem B1958033 : Blo 1028606 1958033 := bstep (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) B1468525
theorem B1466515 : Blo 1028606 1466515 := bstep (se 1 (by rfl) ⟨1099886, by rfl⟩ : syracuseStep 1466515 = 2199773) B2199773
theorem B1564913 : Blo 1028606 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B2318705 : Blo 1028606 2318705 := bstep (se 2 (by rfl) ⟨869514, by rfl⟩ : syracuseStep 2318705 = 1739029) B1739029
theorem B2613617 : Blo 1028606 2613617 := bstep (se 2 (by rfl) ⟨980106, by rfl⟩ : syracuseStep 2613617 = 1960213) B1960213
theorem B2318723 : Blo 1028606 2318723 := bstep (se 1 (by rfl) ⟨1739042, by rfl⟩ : syracuseStep 2318723 = 3478085) B3478085
theorem B2613667 : Blo 1028606 2613667 := bstep (se 1 (by rfl) ⟨1960250, by rfl⟩ : syracuseStep 2613667 = 3920501) B3920501
theorem B1466851 : Blo 1028606 1466851 := bstep (se 1 (by rfl) ⟨1100138, by rfl⟩ : syracuseStep 1466851 = 2200277) B2200277
theorem B3269155 : Blo 1028606 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B1860131 : Blo 1028606 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B1761841 : Blo 1028606 1761841 := bstep (se 2 (by rfl) ⟨660690, by rfl⟩ : syracuseStep 1761841 = 1321381) B1321381
theorem B66839093 : Blo 1028606 66839093 := bstep (se 5 (by rfl) ⟨3133082, by rfl⟩ : syracuseStep 66839093 = 6266165) B6266165
theorem B1303123 : Blo 1028606 1303123 := bstep (se 1 (by rfl) ⟨977342, by rfl⟩ : syracuseStep 1303123 = 1954685) B1954685
theorem B1237603 : Blo 1028606 1237603 := bstep (se 1 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 1237603 = 1856405) B1856405
theorem B2318993 : Blo 1028606 2318993 := bstep (se 2 (by rfl) ⟨869622, by rfl⟩ : syracuseStep 2318993 = 1739245) B1739245
theorem B2319011 : Blo 1028606 2319011 := bstep (se 1 (by rfl) ⟨1739258, by rfl⟩ : syracuseStep 2319011 = 3478517) B3478517
theorem B1303219 : Blo 1028606 1303219 := bstep (se 1 (by rfl) ⟨977414, by rfl⟩ : syracuseStep 1303219 = 1954829) B1954829
theorem B7824113 : Blo 1028606 7824113 := bstep (se 2 (by rfl) ⟨2934042, by rfl⟩ : syracuseStep 7824113 = 5868085) B5868085
theorem B2351857 : Blo 1028606 2351857 := bstep (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) B1763893
theorem B1958755 : Blo 1028606 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B2319281 : Blo 1028606 2319281 := bstep (se 2 (by rfl) ⟨869730, by rfl⟩ : syracuseStep 2319281 = 1739461) B1739461
theorem B2319299 : Blo 1028606 2319299 := bstep (se 1 (by rfl) ⟨1739474, by rfl⟩ : syracuseStep 2319299 = 3478949) B3478949
theorem B2089955 : Blo 1028606 2089955 := bstep (se 1 (by rfl) ⟨1567466, by rfl⟩ : syracuseStep 2089955 = 3134933) B3134933
theorem B1467409 : Blo 1028606 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B1467443 : Blo 1028606 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B1303715 : Blo 1028606 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B2319569 : Blo 1028606 2319569 := bstep (se 2 (by rfl) ⟨869838, by rfl⟩ : syracuseStep 2319569 = 1739677) B1739677
theorem B2319587 : Blo 1028606 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B1959203 : Blo 1028606 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B2319857 : Blo 1028606 2319857 := bstep (se 2 (by rfl) ⟨869946, by rfl⟩ : syracuseStep 2319857 = 1739893) B1739893
theorem B2319875 : Blo 1028606 2319875 := bstep (se 1 (by rfl) ⟨1739906, by rfl⟩ : syracuseStep 2319875 = 3479813) B3479813
theorem B1959491 : Blo 1028606 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B1468001 : Blo 1028606 1468001 := bstep (se 2 (by rfl) ⟨550500, by rfl⟩ : syracuseStep 1468001 = 1101001) B1101001
theorem B2385539 : Blo 1028606 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1762961 : Blo 1028606 1762961 := bstep (se 2 (by rfl) ⟨661110, by rfl⟩ : syracuseStep 1762961 = 1322221) B1322221
theorem B1468081 : Blo 1028606 1468081 := bstep (se 2 (by rfl) ⟨550530, by rfl⟩ : syracuseStep 1468081 = 1101061) B1101061
theorem B2320145 : Blo 1028606 2320145 := bstep (se 2 (by rfl) ⟨870054, by rfl⟩ : syracuseStep 2320145 = 1740109) B1740109
theorem B2320163 : Blo 1028606 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B1304419 : Blo 1028606 1304419 := bstep (se 1 (by rfl) ⟨978314, by rfl⟩ : syracuseStep 1304419 = 1956629) B1956629
theorem B1304515 : Blo 1028606 1304515 := bstep (se 1 (by rfl) ⟨978386, by rfl⟩ : syracuseStep 1304515 = 1956773) B1956773
theorem B3139555 : Blo 1028606 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B2320433 : Blo 1028606 2320433 := bstep (se 2 (by rfl) ⟨870162, by rfl⟩ : syracuseStep 2320433 = 1740325) B1740325
theorem B2320451 : Blo 1028606 2320451 := bstep (se 1 (by rfl) ⟨1740338, by rfl⟩ : syracuseStep 2320451 = 3480677) B3480677
theorem B25389283 : Blo 1028606 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B16705763 : Blo 1028606 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B8808689 : Blo 1028606 8808689 := bstep (se 2 (by rfl) ⟨3303258, by rfl⟩ : syracuseStep 8808689 = 6606517) B6606517
theorem B1042691 : Blo 1028606 1042691 := bstep (se 1 (by rfl) ⟨782018, by rfl⟩ : syracuseStep 1042691 = 1564037) B1564037
theorem B2320721 : Blo 1028606 2320721 := bstep (se 2 (by rfl) ⟨870270, by rfl⟩ : syracuseStep 2320721 = 1740541) B1740541
theorem B2320739 : Blo 1028606 2320739 := bstep (se 1 (by rfl) ⟨1740554, by rfl⟩ : syracuseStep 2320739 = 3481109) B3481109
theorem B1239395 : Blo 1028606 1239395 := bstep (se 1 (by rfl) ⟨929546, by rfl⟩ : syracuseStep 1239395 = 1859093) B1859093
theorem B1305011 : Blo 1028606 1305011 := bstep (se 1 (by rfl) ⟨978758, by rfl⟩ : syracuseStep 1305011 = 1957517) B1957517
theorem B1468867 : Blo 1028606 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B3304003 : Blo 1028606 3304003 := bstep (se 1 (by rfl) ⟨2478002, by rfl⟩ : syracuseStep 3304003 = 4956005) B4956005
theorem B2321009 : Blo 1028606 2321009 := bstep (se 2 (by rfl) ⟨870378, by rfl⟩ : syracuseStep 2321009 = 1740757) B1740757
theorem B2321027 : Blo 1028606 2321027 := bstep (se 1 (by rfl) ⟨1740770, by rfl⟩ : syracuseStep 2321027 = 3481541) B3481541
theorem B5565061 : Blo 1028606 5565061 := bstep (se 4 (by rfl) ⟨521724, by rfl⟩ : syracuseStep 5565061 = 1043449) B1043449
theorem B1174195 : Blo 1028606 1174195 := bstep (se 1 (by rfl) ⟨880646, by rfl⟩ : syracuseStep 1174195 = 1761293) B1761293
theorem B3304273 : Blo 1028606 3304273 := bstep (se 2 (by rfl) ⟨1239102, by rfl⟩ : syracuseStep 3304273 = 2478205) B2478205
theorem B2321297 : Blo 1028606 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B1469345 : Blo 1028606 1469345 := bstep (se 2 (by rfl) ⟨551004, by rfl⟩ : syracuseStep 1469345 = 1102009) B1102009
theorem B2321315 : Blo 1028606 2321315 := bstep (se 1 (by rfl) ⟨1740986, by rfl⟩ : syracuseStep 2321315 = 3481973) B3481973
theorem B1764275 : Blo 1028606 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B1469459 : Blo 1028606 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B1764385 : Blo 1028606 1764385 := bstep (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) B1323289
theorem B1469539 : Blo 1028606 1469539 := bstep (se 1 (by rfl) ⟨1102154, by rfl⟩ : syracuseStep 1469539 = 2204309) B2204309
theorem B1305715 : Blo 1028606 1305715 := bstep (se 1 (by rfl) ⟨979286, by rfl⟩ : syracuseStep 1305715 = 1958573) B1958573
theorem B2321585 : Blo 1028606 2321585 := bstep (se 2 (by rfl) ⟨870594, by rfl⟩ : syracuseStep 2321585 = 1741189) B1741189
theorem B2321603 : Blo 1028606 2321603 := bstep (se 1 (by rfl) ⟨1741202, by rfl⟩ : syracuseStep 2321603 = 3482405) B3482405
theorem B1305811 : Blo 1028606 1305811 := bstep (se 1 (by rfl) ⟨979358, by rfl⟩ : syracuseStep 1305811 = 1958717) B1958717
theorem B3960049 : Blo 1028606 3960049 := bstep (se 2 (by rfl) ⟨1485018, by rfl⟩ : syracuseStep 3960049 = 2970037) B2970037
theorem B5860613 : Blo 1028606 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B3009869 : Blo 1028606 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B5565773 : Blo 1028606 5565773 := bstep (se 3 (by rfl) ⟨1043582, by rfl⟩ : syracuseStep 5565773 = 2087165) B2087165
theorem B1764769 : Blo 1028606 1764769 := bstep (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) B1323577
theorem B1043875 : Blo 1028606 1043875 := bstep (se 1 (by rfl) ⟨782906, by rfl⟩ : syracuseStep 1043875 = 1565813) B1565813
theorem B2321873 : Blo 1028606 2321873 := bstep (se 2 (by rfl) ⟨870702, by rfl⟩ : syracuseStep 2321873 = 1741405) B1741405
theorem B2321891 : Blo 1028606 2321891 := bstep (se 1 (by rfl) ⟨1741418, by rfl⟩ : syracuseStep 2321891 = 3482837) B3482837
theorem B2977357 : Blo 1028606 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B1470097 : Blo 1028606 1470097 := bstep (se 2 (by rfl) ⟨551286, by rfl⟩ : syracuseStep 1470097 = 1102573) B1102573
theorem B1306307 : Blo 1028606 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B5861069 : Blo 1028606 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B2322161 : Blo 1028606 2322161 := bstep (se 2 (by rfl) ⟨870810, by rfl⟩ : syracuseStep 2322161 = 1741621) B1741621
theorem B2322179 : Blo 1028606 2322179 := bstep (se 1 (by rfl) ⟨1741634, by rfl⟩ : syracuseStep 2322179 = 3483269) B3483269
theorem B10579909 : Blo 1028606 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B2322449 : Blo 1028606 2322449 := bstep (se 2 (by rfl) ⟨870918, by rfl⟩ : syracuseStep 2322449 = 1741837) B1741837
theorem B2322467 : Blo 1028606 2322467 := bstep (se 1 (by rfl) ⟨1741850, by rfl⟩ : syracuseStep 2322467 = 3483701) B3483701
theorem B2977955 : Blo 1028606 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B2322737 : Blo 1028606 2322737 := bstep (se 2 (by rfl) ⟨871026, by rfl⟩ : syracuseStep 2322737 = 1742053) B1742053
theorem B2322755 : Blo 1028606 2322755 := bstep (se 1 (by rfl) ⟨1742066, by rfl⟩ : syracuseStep 2322755 = 3484133) B3484133
theorem B12513649 : Blo 1028606 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B3305873 : Blo 1028606 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2781677 : Blo 1028606 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B16740917 : Blo 1028606 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B2323025 : Blo 1028606 2323025 := bstep (se 2 (by rfl) ⟨871134, by rfl⟩ : syracuseStep 2323025 = 1742269) B1742269
theorem B11760227 : Blo 1028606 11760227 := bstep (se 1 (by rfl) ⟨8820170, by rfl⟩ : syracuseStep 11760227 = 17640341) B17640341
theorem B2323043 : Blo 1028606 2323043 := bstep (se 1 (by rfl) ⟨1742282, by rfl⟩ : syracuseStep 2323043 = 3484565) B3484565
theorem B20083427 : Blo 1028606 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B3306221 : Blo 1028606 3306221 := bstep (se 3 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 3306221 = 1239833) B1239833
theorem B4944739 : Blo 1028606 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B2323313 : Blo 1028606 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B2323331 : Blo 1028606 2323331 := bstep (se 1 (by rfl) ⟨1742498, by rfl⟩ : syracuseStep 2323331 = 3484997) B3484997
theorem B2978993 : Blo 1028606 2978993 := bstep (se 2 (by rfl) ⟨1117122, by rfl⟩ : syracuseStep 2978993 = 2234245) B2234245
theorem B12711221 : Blo 1028606 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B5207651 : Blo 1028606 5207651 := bstep (se 1 (by rfl) ⟨3905738, by rfl⟩ : syracuseStep 5207651 = 7811477) B7811477
theorem B3176077 : Blo 1028606 3176077 := bstep (se 3 (by rfl) ⟨595514, by rfl⟩ : syracuseStep 3176077 = 1191029) B1191029
theorem B1046531 : Blo 1028606 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B1046563 : Blo 1028606 1046563 := bstep (se 1 (by rfl) ⟨784922, by rfl⟩ : syracuseStep 1046563 = 1569845) B1569845
theorem B4945969 : Blo 1028606 4945969 := bstep (se 2 (by rfl) ⟨1854738, by rfl⟩ : syracuseStep 4945969 = 3709477) B3709477
theorem B4454669 : Blo 1028606 4454669 := bstep (se 3 (by rfl) ⟨835250, by rfl⟩ : syracuseStep 4454669 = 1670501) B1670501
theorem B5208461 : Blo 1028606 5208461 := bstep (se 3 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 5208461 = 1953173) B1953173
theorem B3471821 : Blo 1028606 3471821 := bstep (se 3 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 3471821 = 1301933) B1301933
theorem B3471875 : Blo 1028606 3471875 := bstep (se 1 (by rfl) ⟨2603906, by rfl⟩ : syracuseStep 3471875 = 5207813) B5207813
theorem B5863985 : Blo 1028606 5863985 := bstep (se 2 (by rfl) ⟨2198994, by rfl⟩ : syracuseStep 5863985 = 4397989) B4397989
theorem B8354501 : Blo 1028606 8354501 := bstep (se 4 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 8354501 = 1566469) B1566469
theorem B3472145 : Blo 1028606 3472145 := bstep (se 2 (by rfl) ⟨1302054, by rfl⟩ : syracuseStep 3472145 = 2604109) B2604109
theorem B4947085 : Blo 1028606 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B1735843 : Blo 1028606 1735843 := bstep (se 1 (by rfl) ⟨1301882, by rfl⟩ : syracuseStep 1735843 = 2603765) B2603765
theorem B3472685 : Blo 1028606 3472685 := bstep (se 3 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 3472685 = 1302257) B1302257
theorem B1735985 : Blo 1028606 1735985 := bstep (se 2 (by rfl) ⟨650994, by rfl⟩ : syracuseStep 1735985 = 1301989) B1301989
theorem B7044401 : Blo 1028606 7044401 := bstep (se 2 (by rfl) ⟨2641650, by rfl⟩ : syracuseStep 7044401 = 5283301) B5283301
theorem B3472739 : Blo 1028606 3472739 := bstep (se 1 (by rfl) ⟨2604554, by rfl⟩ : syracuseStep 3472739 = 5209109) B5209109
theorem B1736113 : Blo 1028606 1736113 := bstep (se 2 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 1736113 = 1302085) B1302085
theorem B1736147 : Blo 1028606 1736147 := bstep (se 1 (by rfl) ⟨1302110, by rfl⟩ : syracuseStep 1736147 = 2604221) B2604221
theorem B1736275 : Blo 1028606 1736275 := bstep (se 1 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 1736275 = 2604413) B2604413
theorem B3473009 : Blo 1028606 3473009 := bstep (se 2 (by rfl) ⟨1302378, by rfl⟩ : syracuseStep 3473009 = 2604757) B2604757
theorem B1736417 : Blo 1028606 1736417 := bstep (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) B1302313
theorem B1736545 : Blo 1028606 1736545 := bstep (se 2 (by rfl) ⟨651204, by rfl⟩ : syracuseStep 1736545 = 1302409) B1302409
theorem B1736579 : Blo 1028606 1736579 := bstep (se 1 (by rfl) ⟨1302434, by rfl⟩ : syracuseStep 1736579 = 2604869) B2604869
theorem B5865443 : Blo 1028606 5865443 := bstep (se 1 (by rfl) ⟨4399082, by rfl⟩ : syracuseStep 5865443 = 8798165) B8798165
theorem B5210243 : Blo 1028606 5210243 := bstep (se 1 (by rfl) ⟨3907682, by rfl⟩ : syracuseStep 5210243 = 7815365) B7815365
theorem B1737227 : Blo 1028606 1737227 := bstep (se 1 (by rfl) ⟨1302920, by rfl⟩ : syracuseStep 1737227 = 2605841) B2605841
theorem B1737355 : Blo 1028606 1737355 := bstep (se 1 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 1737355 = 2606033) B2606033
theorem B4358873 : Blo 1028606 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B1737497 : Blo 1028606 1737497 := bstep (se 2 (by rfl) ⟨651561, by rfl⟩ : syracuseStep 1737497 = 1303123) B1303123
theorem B3474251 : Blo 1028606 3474251 := bstep (se 1 (by rfl) ⟨2605688, by rfl⟩ : syracuseStep 3474251 = 5211377) B5211377
theorem B1737625 : Blo 1028606 1737625 := bstep (se 2 (by rfl) ⟨651609, by rfl⟩ : syracuseStep 1737625 = 1303219) B1303219
theorem B8815661 : Blo 1028606 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B3474521 : Blo 1028606 3474521 := bstep (se 2 (by rfl) ⟨1302945, by rfl⟩ : syracuseStep 3474521 = 2605891) B2605891
theorem B5866627 : Blo 1028606 5866627 := bstep (se 1 (by rfl) ⟨4399970, by rfl⟩ : syracuseStep 5866627 = 8799941) B8799941
theorem B1738199 : Blo 1028606 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2229811 : Blo 1028606 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B1738327 : Blo 1028606 1738327 := bstep (se 1 (by rfl) ⟨1303745, by rfl⟩ : syracuseStep 1738327 = 2607491) B2607491
theorem B2197081 : Blo 1028606 2197081 := bstep (se 2 (by rfl) ⟨823905, by rfl⟩ : syracuseStep 2197081 = 1647811) B1647811
theorem B24413789 : Blo 1028606 24413789 := bstep (se 3 (by rfl) ⟨4577585, by rfl⟩ : syracuseStep 24413789 = 9155171) B9155171
theorem B3475223 : Blo 1028606 3475223 := bstep (se 1 (by rfl) ⟨2606417, by rfl⟩ : syracuseStep 3475223 = 5212835) B5212835
theorem B5867585 : Blo 1028606 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B5572739 : Blo 1028606 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B1738955 : Blo 1028606 1738955 := bstep (se 1 (by rfl) ⟨1304216, by rfl⟩ : syracuseStep 1738955 = 2608433) B2608433
theorem B3475763 : Blo 1028606 3475763 := bstep (se 1 (by rfl) ⟨2606822, by rfl⟩ : syracuseStep 3475763 = 5213645) B5213645
theorem B1739083 : Blo 1028606 1739083 := bstep (se 1 (by rfl) ⟨1304312, by rfl⟩ : syracuseStep 1739083 = 2608625) B2608625
theorem B1739225 : Blo 1028606 1739225 := bstep (se 2 (by rfl) ⟨652209, by rfl⟩ : syracuseStep 1739225 = 1304419) B1304419
theorem B3476033 : Blo 1028606 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B5573195 : Blo 1028606 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B1739353 : Blo 1028606 1739353 := bstep (se 2 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 1739353 = 1304515) B1304515
theorem B1542923 : Blo 1028606 1542923 := bstep (se 1 (by rfl) ⟨1157192, by rfl⟩ : syracuseStep 1542923 = 2314385) B2314385
theorem B1542935 : Blo 1028606 1542935 := bstep (se 1 (by rfl) ⟨1157201, by rfl⟩ : syracuseStep 1542935 = 2314403) B2314403
theorem B1543001 : Blo 1028606 1543001 := bstep (se 2 (by rfl) ⟨578625, by rfl⟩ : syracuseStep 1543001 = 1157251) B1157251
theorem B1543115 : Blo 1028606 1543115 := bstep (se 1 (by rfl) ⟨1157336, by rfl⟩ : syracuseStep 1543115 = 2314673) B2314673
theorem B1543127 : Blo 1028606 1543127 := bstep (se 1 (by rfl) ⟨1157345, by rfl⟩ : syracuseStep 1543127 = 2314691) B2314691
theorem B33852377 : Blo 1028606 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B1543193 : Blo 1028606 1543193 := bstep (se 2 (by rfl) ⟨578697, by rfl⟩ : syracuseStep 1543193 = 1157395) B1157395
theorem B3476573 : Blo 1028606 3476573 := bstep (se 3 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 3476573 = 1303715) B1303715
theorem B1543307 : Blo 1028606 1543307 := bstep (se 1 (by rfl) ⟨1157480, by rfl⟩ : syracuseStep 1543307 = 2314961) B2314961
theorem B1543319 : Blo 1028606 1543319 := bstep (se 1 (by rfl) ⟨1157489, by rfl⟩ : syracuseStep 1543319 = 2314979) B2314979
theorem B1739927 : Blo 1028606 1739927 := bstep (se 1 (by rfl) ⟨1304945, by rfl⟩ : syracuseStep 1739927 = 2609891) B2609891
theorem B28183733 : Blo 1028606 28183733 := bstep (se 5 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 28183733 = 2642225) B2642225
theorem B1543385 : Blo 1028606 1543385 := bstep (se 2 (by rfl) ⟨578769, by rfl⟩ : syracuseStep 1543385 = 1157539) B1157539
theorem B1740055 : Blo 1028606 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B1543499 : Blo 1028606 1543499 := bstep (se 1 (by rfl) ⟨1157624, by rfl⟩ : syracuseStep 1543499 = 2315249) B2315249
theorem B1543511 : Blo 1028606 1543511 := bstep (se 1 (by rfl) ⟨1157633, by rfl⟩ : syracuseStep 1543511 = 2315267) B2315267
theorem B13208933 : Blo 1028606 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B2788759 : Blo 1028606 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B1543577 : Blo 1028606 1543577 := bstep (se 2 (by rfl) ⟨578841, by rfl⟩ : syracuseStep 1543577 = 1157683) B1157683
theorem B1543691 : Blo 1028606 1543691 := bstep (se 1 (by rfl) ⟨1157768, by rfl⟩ : syracuseStep 1543691 = 2315537) B2315537
theorem B1543703 : Blo 1028606 1543703 := bstep (se 1 (by rfl) ⟨1157777, by rfl⟩ : syracuseStep 1543703 = 2315555) B2315555
theorem B1543769 : Blo 1028606 1543769 := bstep (se 2 (by rfl) ⟨578913, by rfl⟩ : syracuseStep 1543769 = 1157827) B1157827
theorem B6262373 : Blo 1028606 6262373 := bstep (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) B1174195
theorem B5279363 : Blo 1028606 5279363 := bstep (se 1 (by rfl) ⟨3959522, by rfl⟩ : syracuseStep 5279363 = 7919045) B7919045
theorem B4394675 : Blo 1028606 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B1543883 : Blo 1028606 1543883 := bstep (se 1 (by rfl) ⟨1157912, by rfl⟩ : syracuseStep 1543883 = 2315825) B2315825
theorem B1543895 : Blo 1028606 1543895 := bstep (se 1 (by rfl) ⟨1157921, by rfl⟩ : syracuseStep 1543895 = 2315843) B2315843
theorem B5213969 : Blo 1028606 5213969 := bstep (se 2 (by rfl) ⟨1955238, by rfl⟩ : syracuseStep 5213969 = 3910477) B3910477
theorem B1543961 : Blo 1028606 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B1544075 : Blo 1028606 1544075 := bstep (se 1 (by rfl) ⟨1158056, by rfl⟩ : syracuseStep 1544075 = 2316113) B2316113
theorem B1740683 : Blo 1028606 1740683 := bstep (se 1 (by rfl) ⟨1305512, by rfl⟩ : syracuseStep 1740683 = 2611025) B2611025
theorem B1544087 : Blo 1028606 1544087 := bstep (se 1 (by rfl) ⟨1158065, by rfl⟩ : syracuseStep 1544087 = 2316131) B2316131
theorem B5214131 : Blo 1028606 5214131 := bstep (se 1 (by rfl) ⟨3910598, by rfl⟩ : syracuseStep 5214131 = 7821197) B7821197
theorem B1544153 : Blo 1028606 1544153 := bstep (se 2 (by rfl) ⟨579057, by rfl⟩ : syracuseStep 1544153 = 1158115) B1158115
theorem B1740811 : Blo 1028606 1740811 := bstep (se 1 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 1740811 = 2611217) B2611217
theorem B1544267 : Blo 1028606 1544267 := bstep (se 1 (by rfl) ⟨1158200, by rfl⟩ : syracuseStep 1544267 = 2316401) B2316401
theorem B1544279 : Blo 1028606 1544279 := bstep (se 1 (by rfl) ⟨1158209, by rfl⟩ : syracuseStep 1544279 = 2316419) B2316419
theorem B11145347 : Blo 1028606 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B1544345 : Blo 1028606 1544345 := bstep (se 2 (by rfl) ⟨579129, by rfl⟩ : syracuseStep 1544345 = 1158259) B1158259
theorem B1740953 : Blo 1028606 1740953 := bstep (se 2 (by rfl) ⟨652857, by rfl⟩ : syracuseStep 1740953 = 1305715) B1305715
theorem B3477707 : Blo 1028606 3477707 := bstep (se 1 (by rfl) ⟨2608280, by rfl⟩ : syracuseStep 3477707 = 5216561) B5216561
theorem B1544459 : Blo 1028606 1544459 := bstep (se 1 (by rfl) ⟨1158344, by rfl⟩ : syracuseStep 1544459 = 2316689) B2316689
theorem B1544471 : Blo 1028606 1544471 := bstep (se 1 (by rfl) ⟨1158353, by rfl⟩ : syracuseStep 1544471 = 2316707) B2316707
theorem B1741081 : Blo 1028606 1741081 := bstep (se 2 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 1741081 = 1305811) B1305811
theorem B5280065 : Blo 1028606 5280065 := bstep (se 2 (by rfl) ⟨1980024, by rfl⟩ : syracuseStep 5280065 = 3960049) B3960049
theorem B1544537 : Blo 1028606 1544537 := bstep (se 2 (by rfl) ⟨579201, by rfl⟩ : syracuseStep 1544537 = 1158403) B1158403
theorem B1544651 : Blo 1028606 1544651 := bstep (se 1 (by rfl) ⟨1158488, by rfl⟩ : syracuseStep 1544651 = 2316977) B2316977
theorem B1544663 : Blo 1028606 1544663 := bstep (se 1 (by rfl) ⟨1158497, by rfl⟩ : syracuseStep 1544663 = 2316995) B2316995
theorem B3477977 : Blo 1028606 3477977 := bstep (se 2 (by rfl) ⟨1304241, by rfl⟩ : syracuseStep 3477977 = 2608483) B2608483
theorem B1544729 : Blo 1028606 1544729 := bstep (se 2 (by rfl) ⟨579273, by rfl⟩ : syracuseStep 1544729 = 1158547) B1158547
theorem B2200115 : Blo 1028606 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B1544843 : Blo 1028606 1544843 := bstep (se 1 (by rfl) ⟨1158632, by rfl⟩ : syracuseStep 1544843 = 2317265) B2317265
theorem B1544855 : Blo 1028606 1544855 := bstep (se 1 (by rfl) ⟨1158641, by rfl⟩ : syracuseStep 1544855 = 2317283) B2317283
theorem B8819351 : Blo 1028606 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B1544921 : Blo 1028606 1544921 := bstep (se 2 (by rfl) ⟨579345, by rfl⟩ : syracuseStep 1544921 = 1158691) B1158691
theorem B3969809 : Blo 1028606 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B1545035 : Blo 1028606 1545035 := bstep (se 1 (by rfl) ⟨1158776, by rfl⟩ : syracuseStep 1545035 = 2317553) B2317553
theorem B1545047 : Blo 1028606 1545047 := bstep (se 1 (by rfl) ⟨1158785, by rfl⟩ : syracuseStep 1545047 = 2317571) B2317571
theorem B1741655 : Blo 1028606 1741655 := bstep (se 1 (by rfl) ⟨1306241, by rfl⟩ : syracuseStep 1741655 = 2612483) B2612483
theorem B1545113 : Blo 1028606 1545113 := bstep (se 2 (by rfl) ⟨579417, by rfl⟩ : syracuseStep 1545113 = 1158835) B1158835
theorem B1741783 : Blo 1028606 1741783 := bstep (se 1 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 1741783 = 2612675) B2612675
theorem B1545227 : Blo 1028606 1545227 := bstep (se 1 (by rfl) ⟨1158920, by rfl⟩ : syracuseStep 1545227 = 2317841) B2317841
theorem B1545239 : Blo 1028606 1545239 := bstep (se 1 (by rfl) ⟨1158929, by rfl⟩ : syracuseStep 1545239 = 2317859) B2317859
theorem B2200601 : Blo 1028606 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B1545305 : Blo 1028606 1545305 := bstep (se 2 (by rfl) ⟨579489, by rfl⟩ : syracuseStep 1545305 = 1158979) B1158979
theorem B3478679 : Blo 1028606 3478679 := bstep (se 1 (by rfl) ⟨2609009, by rfl⟩ : syracuseStep 3478679 = 5218019) B5218019
theorem B1545419 : Blo 1028606 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B13407437 : Blo 1028606 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1545431 : Blo 1028606 1545431 := bstep (se 1 (by rfl) ⟨1159073, by rfl⟩ : syracuseStep 1545431 = 2318147) B2318147
theorem B1545497 : Blo 1028606 1545497 := bstep (se 2 (by rfl) ⟨579561, by rfl⟩ : syracuseStep 1545497 = 1159123) B1159123
theorem B2790749 : Blo 1028606 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B1545611 : Blo 1028606 1545611 := bstep (se 1 (by rfl) ⟨1159208, by rfl⟩ : syracuseStep 1545611 = 2318417) B2318417
theorem B1545623 : Blo 1028606 1545623 := bstep (se 1 (by rfl) ⟨1159217, by rfl⟩ : syracuseStep 1545623 = 2318435) B2318435
theorem B1545689 : Blo 1028606 1545689 := bstep (se 2 (by rfl) ⟨579633, by rfl⟩ : syracuseStep 1545689 = 1159267) B1159267
theorem B9410053 : Blo 1028606 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B4396589 : Blo 1028606 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B1545803 : Blo 1028606 1545803 := bstep (se 1 (by rfl) ⟨1159352, by rfl⟩ : syracuseStep 1545803 = 2318705) B2318705
theorem B1742411 : Blo 1028606 1742411 := bstep (se 1 (by rfl) ⟨1306808, by rfl⟩ : syracuseStep 1742411 = 2613617) B2613617
theorem B1545815 : Blo 1028606 1545815 := bstep (se 1 (by rfl) ⟨1159361, by rfl⟩ : syracuseStep 1545815 = 2318723) B2318723
theorem B3348119 : Blo 1028606 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1545881 : Blo 1028606 1545881 := bstep (se 2 (by rfl) ⟨579705, by rfl⟩ : syracuseStep 1545881 = 1159411) B1159411
theorem B3479219 : Blo 1028606 3479219 := bstep (se 1 (by rfl) ⟨2609414, by rfl⟩ : syracuseStep 3479219 = 5218829) B5218829
theorem B16684805 : Blo 1028606 16684805 := bstep (se 4 (by rfl) ⟨1564200, by rfl⟩ : syracuseStep 16684805 = 3128401) B3128401
theorem B1545995 : Blo 1028606 1545995 := bstep (se 1 (by rfl) ⟨1159496, by rfl⟩ : syracuseStep 1545995 = 2318993) B2318993
theorem B1546007 : Blo 1028606 1546007 := bstep (se 1 (by rfl) ⟨1159505, by rfl⟩ : syracuseStep 1546007 = 2319011) B2319011
theorem B16684865 : Blo 1028606 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B5216075 : Blo 1028606 5216075 := bstep (se 1 (by rfl) ⟨3912056, by rfl⟩ : syracuseStep 5216075 = 7824113) B7824113
theorem B1546073 : Blo 1028606 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B3479489 : Blo 1028606 3479489 := bstep (se 2 (by rfl) ⟨1304808, by rfl⟩ : syracuseStep 3479489 = 2609617) B2609617
theorem B1546187 : Blo 1028606 1546187 := bstep (se 1 (by rfl) ⟨1159640, by rfl⟩ : syracuseStep 1546187 = 2319281) B2319281
theorem B1546199 : Blo 1028606 1546199 := bstep (se 1 (by rfl) ⟨1159649, by rfl⟩ : syracuseStep 1546199 = 2319299) B2319299
theorem B14882777 : Blo 1028606 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B1546265 : Blo 1028606 1546265 := bstep (se 2 (by rfl) ⟨579849, by rfl⟩ : syracuseStep 1546265 = 1159699) B1159699
theorem B1546379 : Blo 1028606 1546379 := bstep (se 1 (by rfl) ⟨1159784, by rfl⟩ : syracuseStep 1546379 = 2319569) B2319569
theorem B1546391 : Blo 1028606 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B4397273 : Blo 1028606 4397273 := bstep (se 2 (by rfl) ⟨1648977, by rfl⟩ : syracuseStep 4397273 = 3297955) B3297955
theorem B1546457 : Blo 1028606 1546457 := bstep (se 2 (by rfl) ⟨579921, by rfl⟩ : syracuseStep 1546457 = 1159843) B1159843
theorem B1906931 : Blo 1028606 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B13211909 : Blo 1028606 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B21174533 : Blo 1028606 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B1546571 : Blo 1028606 1546571 := bstep (se 1 (by rfl) ⟨1159928, by rfl⟩ : syracuseStep 1546571 = 2319857) B2319857
theorem B1546583 : Blo 1028606 1546583 := bstep (se 1 (by rfl) ⟨1159937, by rfl⟩ : syracuseStep 1546583 = 2319875) B2319875
theorem B1546649 : Blo 1028606 1546649 := bstep (se 2 (by rfl) ⟨579993, by rfl⟩ : syracuseStep 1546649 = 1159987) B1159987
theorem B6592985 : Blo 1028606 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B3480029 : Blo 1028606 3480029 := bstep (se 3 (by rfl) ⟨652505, by rfl⟩ : syracuseStep 3480029 = 1305011) B1305011
theorem B1546763 : Blo 1028606 1546763 := bstep (se 1 (by rfl) ⟨1160072, by rfl⟩ : syracuseStep 1546763 = 2320145) B2320145
theorem B1546775 : Blo 1028606 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1546841 : Blo 1028606 1546841 := bstep (se 2 (by rfl) ⟨580065, by rfl⟩ : syracuseStep 1546841 = 1160131) B1160131
theorem B2202241 : Blo 1028606 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B1546955 : Blo 1028606 1546955 := bstep (se 1 (by rfl) ⟨1160216, by rfl⟩ : syracuseStep 1546955 = 2320433) B2320433
theorem B1546967 : Blo 1028606 1546967 := bstep (se 1 (by rfl) ⟨1160225, by rfl⟩ : syracuseStep 1546967 = 2320451) B2320451
theorem B1547033 : Blo 1028606 1547033 := bstep (se 2 (by rfl) ⟨580137, by rfl⟩ : syracuseStep 1547033 = 1160275) B1160275
theorem B3873587 : Blo 1028606 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B5872459 : Blo 1028606 5872459 := bstep (se 1 (by rfl) ⟨4404344, by rfl⟩ : syracuseStep 5872459 = 8808689) B8808689
theorem B1547147 : Blo 1028606 1547147 := bstep (se 1 (by rfl) ⟨1160360, by rfl⟩ : syracuseStep 1547147 = 2320721) B2320721
theorem B1547159 : Blo 1028606 1547159 := bstep (se 1 (by rfl) ⟨1160369, by rfl⟩ : syracuseStep 1547159 = 2320739) B2320739
theorem B1547225 : Blo 1028606 1547225 := bstep (se 2 (by rfl) ⟨580209, by rfl⟩ : syracuseStep 1547225 = 1160419) B1160419
theorem B1547339 : Blo 1028606 1547339 := bstep (se 1 (by rfl) ⟨1160504, by rfl⟩ : syracuseStep 1547339 = 2321009) B2321009
theorem B1547351 : Blo 1028606 1547351 := bstep (se 1 (by rfl) ⟨1160513, by rfl⟩ : syracuseStep 1547351 = 2321027) B2321027
theorem B5872733 : Blo 1028606 5872733 := bstep (se 3 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 5872733 = 2202275) B2202275
theorem B1547417 : Blo 1028606 1547417 := bstep (se 2 (by rfl) ⟨580281, by rfl⟩ : syracuseStep 1547417 = 1160563) B1160563
theorem B1547531 : Blo 1028606 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B1547543 : Blo 1028606 1547543 := bstep (se 1 (by rfl) ⟨1160657, by rfl⟩ : syracuseStep 1547543 = 2321315) B2321315
theorem B1547609 : Blo 1028606 1547609 := bstep (se 2 (by rfl) ⟨580353, by rfl⟩ : syracuseStep 1547609 = 1160707) B1160707
theorem B1547723 : Blo 1028606 1547723 := bstep (se 1 (by rfl) ⟨1160792, by rfl⟩ : syracuseStep 1547723 = 2321585) B2321585
theorem B1547735 : Blo 1028606 1547735 := bstep (se 1 (by rfl) ⟨1160801, by rfl⟩ : syracuseStep 1547735 = 2321603) B2321603
theorem B3907075 : Blo 1028606 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B4234769 : Blo 1028606 4234769 := bstep (se 2 (by rfl) ⟨1588038, by rfl⟩ : syracuseStep 4234769 = 3176077) B3176077
theorem B1547801 : Blo 1028606 1547801 := bstep (se 2 (by rfl) ⟨580425, by rfl⟩ : syracuseStep 1547801 = 1160851) B1160851
theorem B2006579 : Blo 1028606 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B5217857 : Blo 1028606 5217857 := bstep (se 2 (by rfl) ⟨1956696, by rfl⟩ : syracuseStep 5217857 = 3913393) B3913393
theorem B3481163 : Blo 1028606 3481163 := bstep (se 1 (by rfl) ⟨2610872, by rfl⟩ : syracuseStep 3481163 = 5221745) B5221745
theorem B1547915 : Blo 1028606 1547915 := bstep (se 1 (by rfl) ⟨1160936, by rfl⟩ : syracuseStep 1547915 = 2321873) B2321873
theorem B1547927 : Blo 1028606 1547927 := bstep (se 1 (by rfl) ⟨1160945, by rfl⟩ : syracuseStep 1547927 = 2321891) B2321891
theorem B1547993 : Blo 1028606 1547993 := bstep (se 2 (by rfl) ⟨580497, by rfl⟩ : syracuseStep 1547993 = 1160995) B1160995
theorem B8789795 : Blo 1028606 8789795 := bstep (se 1 (by rfl) ⟨6592346, by rfl⟩ : syracuseStep 8789795 = 13184693) B13184693
theorem B3907379 : Blo 1028606 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B1548107 : Blo 1028606 1548107 := bstep (se 1 (by rfl) ⟨1161080, by rfl⟩ : syracuseStep 1548107 = 2322161) B2322161
theorem B1548119 : Blo 1028606 1548119 := bstep (se 1 (by rfl) ⟨1161089, by rfl⟩ : syracuseStep 1548119 = 2322179) B2322179
theorem B3481433 : Blo 1028606 3481433 := bstep (se 2 (by rfl) ⟨1305537, by rfl⟩ : syracuseStep 3481433 = 2611075) B2611075
theorem B1548185 : Blo 1028606 1548185 := bstep (se 2 (by rfl) ⟨580569, by rfl⟩ : syracuseStep 1548185 = 1161139) B1161139
theorem B7839665 : Blo 1028606 7839665 := bstep (se 2 (by rfl) ⟨2939874, by rfl⟩ : syracuseStep 7839665 = 5879749) B5879749
theorem B1548299 : Blo 1028606 1548299 := bstep (se 1 (by rfl) ⟨1161224, by rfl⟩ : syracuseStep 1548299 = 2322449) B2322449
theorem B1548311 : Blo 1028606 1548311 := bstep (se 1 (by rfl) ⟨1161233, by rfl⟩ : syracuseStep 1548311 = 2322467) B2322467
theorem B6594625 : Blo 1028606 6594625 := bstep (se 2 (by rfl) ⟨2472984, by rfl⟩ : syracuseStep 6594625 = 4945969) B4945969
theorem B4464715 : Blo 1028606 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B1548377 : Blo 1028606 1548377 := bstep (se 2 (by rfl) ⟨580641, by rfl⟩ : syracuseStep 1548377 = 1161283) B1161283
theorem B1548491 : Blo 1028606 1548491 := bstep (se 1 (by rfl) ⟨1161368, by rfl⟩ : syracuseStep 1548491 = 2322737) B2322737
theorem B1548503 : Blo 1028606 1548503 := bstep (se 1 (by rfl) ⟨1161377, by rfl⟩ : syracuseStep 1548503 = 2322755) B2322755
theorem B4235485 : Blo 1028606 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B1548569 : Blo 1028606 1548569 := bstep (se 2 (by rfl) ⟨580713, by rfl⟩ : syracuseStep 1548569 = 1161427) B1161427
theorem B1548683 : Blo 1028606 1548683 := bstep (se 1 (by rfl) ⟨1161512, by rfl⟩ : syracuseStep 1548683 = 2323025) B2323025
theorem B7840151 : Blo 1028606 7840151 := bstep (se 1 (by rfl) ⟨5880113, by rfl⟩ : syracuseStep 7840151 = 11760227) B11760227
theorem B1548695 : Blo 1028606 1548695 := bstep (se 1 (by rfl) ⟨1161521, by rfl⟩ : syracuseStep 1548695 = 2323043) B2323043
theorem B3908033 : Blo 1028606 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B1548761 : Blo 1028606 1548761 := bstep (se 2 (by rfl) ⟨580785, by rfl⟩ : syracuseStep 1548761 = 1161571) B1161571
theorem B2204147 : Blo 1028606 2204147 := bstep (se 1 (by rfl) ⟨1653110, by rfl⟩ : syracuseStep 2204147 = 3306221) B3306221
theorem B3482135 : Blo 1028606 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B1548875 : Blo 1028606 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1548887 : Blo 1028606 1548887 := bstep (se 1 (by rfl) ⟨1161665, by rfl⟩ : syracuseStep 1548887 = 2323331) B2323331
theorem B2204633 : Blo 1028606 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B3482675 : Blo 1028606 3482675 := bstep (se 1 (by rfl) ⟨2612006, by rfl⟩ : syracuseStep 3482675 = 5224013) B5224013
theorem B3482945 : Blo 1028606 3482945 := bstep (se 2 (by rfl) ⟨1306104, by rfl⟩ : syracuseStep 3482945 = 2612209) B2612209
theorem B5219801 : Blo 1028606 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B6596113 : Blo 1028606 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B3909293 : Blo 1028606 3909293 := bstep (se 3 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 3909293 = 1465985) B1465985
theorem B2205377 : Blo 1028606 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B3909323 : Blo 1028606 3909323 := bstep (se 1 (by rfl) ⟨2931992, by rfl⟩ : syracuseStep 3909323 = 5863985) B5863985
theorem B3483485 : Blo 1028606 3483485 := bstep (se 3 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 3483485 = 1306307) B1306307
theorem B1157323 : Blo 1028606 1157323 := bstep (se 1 (by rfl) ⟨867992, by rfl⟩ : syracuseStep 1157323 = 1735985) B1735985
theorem B4696267 : Blo 1028606 4696267 := bstep (se 1 (by rfl) ⟨3522200, by rfl⟩ : syracuseStep 4696267 = 7044401) B7044401
theorem B4958425 : Blo 1028606 4958425 := bstep (se 2 (by rfl) ⟨1859409, by rfl⟩ : syracuseStep 4958425 = 3718819) B3718819
theorem B16918769 : Blo 1028606 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B1157431 : Blo 1028606 1157431 := bstep (se 1 (by rfl) ⟨868073, by rfl⟩ : syracuseStep 1157431 = 1736147) B1736147
theorem B3909977 : Blo 1028606 3909977 := bstep (se 2 (by rfl) ⟨1466241, by rfl⟩ : syracuseStep 3909977 = 2932483) B2932483
theorem B4401611 : Blo 1028606 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B1157611 : Blo 1028606 1157611 := bstep (se 1 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 1157611 = 1736417) B1736417
theorem B1157719 : Blo 1028606 1157719 := bstep (se 1 (by rfl) ⟨868289, by rfl⟩ : syracuseStep 1157719 = 1736579) B1736579
theorem B3713629 : Blo 1028606 3713629 := bstep (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) B1392611
theorem B3910295 : Blo 1028606 3910295 := bstep (se 1 (by rfl) ⟨2932721, by rfl⟩ : syracuseStep 3910295 = 5865443) B5865443
theorem B1157899 : Blo 1028606 1157899 := bstep (se 1 (by rfl) ⟨868424, by rfl⟩ : syracuseStep 1157899 = 1736849) B1736849
theorem B5581669 : Blo 1028606 5581669 := bstep (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) B1046563
theorem B1158007 : Blo 1028606 1158007 := bstep (se 1 (by rfl) ⟨868505, by rfl⟩ : syracuseStep 1158007 = 1737011) B1737011
theorem B3484619 : Blo 1028606 3484619 := bstep (se 1 (by rfl) ⟨2613464, by rfl⟩ : syracuseStep 3484619 = 5226929) B5226929
theorem B1158187 : Blo 1028606 1158187 := bstep (se 1 (by rfl) ⟨868640, by rfl⟩ : syracuseStep 1158187 = 1737281) B1737281
theorem B5221421 : Blo 1028606 5221421 := bstep (se 3 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 5221421 = 1958033) B1958033
theorem B1158295 : Blo 1028606 1158295 := bstep (se 1 (by rfl) ⟨868721, by rfl⟩ : syracuseStep 1158295 = 1737443) B1737443
theorem B3484889 : Blo 1028606 3484889 := bstep (se 2 (by rfl) ⟨1306833, by rfl⟩ : syracuseStep 3484889 = 2613667) B2613667
theorem B3910963 : Blo 1028606 3910963 := bstep (se 1 (by rfl) ⟨2933222, by rfl⟩ : syracuseStep 3910963 = 5866445) B5866445
theorem B1158475 : Blo 1028606 1158475 := bstep (se 1 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 1158475 = 1737713) B1737713
theorem B1158583 : Blo 1028606 1158583 := bstep (se 1 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 1158583 = 1737875) B1737875
theorem B1650137 : Blo 1028606 1650137 := bstep (se 2 (by rfl) ⟨618801, by rfl⟩ : syracuseStep 1650137 = 1237603) B1237603
theorem B1322519 : Blo 1028606 1322519 := bstep (se 1 (by rfl) ⟨991889, by rfl⟩ : syracuseStep 1322519 = 1983779) B1983779
theorem B4959809 : Blo 1028606 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1158763 : Blo 1028606 1158763 := bstep (se 1 (by rfl) ⟨869072, by rfl⟩ : syracuseStep 1158763 = 1738145) B1738145
theorem B1158871 : Blo 1028606 1158871 := bstep (se 1 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 1158871 = 1738307) B1738307
theorem B1159051 : Blo 1028606 1159051 := bstep (se 1 (by rfl) ⟨869288, by rfl⟩ : syracuseStep 1159051 = 1738577) B1738577
theorem B1159159 : Blo 1028606 1159159 := bstep (se 1 (by rfl) ⟨869369, by rfl⟩ : syracuseStep 1159159 = 1738739) B1738739
theorem B11907107 : Blo 1028606 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B4403251 : Blo 1028606 4403251 := bstep (se 1 (by rfl) ⟨3302438, by rfl⟩ : syracuseStep 4403251 = 6604877) B6604877
theorem B4960349 : Blo 1028606 4960349 := bstep (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) B1860131
theorem B1159339 : Blo 1028606 1159339 := bstep (se 1 (by rfl) ⟨869504, by rfl⟩ : syracuseStep 1159339 = 1739009) B1739009
theorem B19771573 : Blo 1028606 19771573 := bstep (se 5 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 19771573 = 1853585) B1853585
theorem B7516433 : Blo 1028606 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B1159447 : Blo 1028606 1159447 := bstep (se 1 (by rfl) ⟨869585, by rfl⟩ : syracuseStep 1159447 = 1739171) B1739171
theorem B3715417 : Blo 1028606 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B5878109 : Blo 1028606 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B7418263 : Blo 1028606 7418263 := bstep (se 1 (by rfl) ⟨5563697, by rfl⟩ : syracuseStep 7418263 = 11127395) B11127395
theorem B1159627 : Blo 1028606 1159627 := bstep (se 1 (by rfl) ⟨869720, by rfl⟩ : syracuseStep 1159627 = 1739441) B1739441
theorem B1028619 : Blo 1028606 1028619 := bstep (se 1 (by rfl) ⟨771464, by rfl⟩ : syracuseStep 1028619 = 1542929) B1542929
theorem B3912209 : Blo 1028606 3912209 := bstep (se 2 (by rfl) ⟨1467078, by rfl⟩ : syracuseStep 3912209 = 2934157) B2934157
theorem B1028631 : Blo 1028606 1028631 := bstep (se 1 (by rfl) ⟨771473, by rfl⟩ : syracuseStep 1028631 = 1542947) B1542947
theorem B1028651 : Blo 1028606 1028651 := bstep (se 1 (by rfl) ⟨771488, by rfl⟩ : syracuseStep 1028651 = 1542977) B1542977
theorem B1028663 : Blo 1028606 1028663 := bstep (se 1 (by rfl) ⟨771497, by rfl⟩ : syracuseStep 1028663 = 1542995) B1542995
theorem B1159735 : Blo 1028606 1159735 := bstep (se 1 (by rfl) ⟨869801, by rfl⟩ : syracuseStep 1159735 = 1739603) B1739603
theorem B1028683 : Blo 1028606 1028683 := bstep (se 1 (by rfl) ⟨771512, by rfl⟩ : syracuseStep 1028683 = 1543025) B1543025
theorem B1028695 : Blo 1028606 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B1028715 : Blo 1028606 1028715 := bstep (se 1 (by rfl) ⟨771536, by rfl⟩ : syracuseStep 1028715 = 1543073) B1543073
theorem B1028727 : Blo 1028606 1028727 := bstep (se 1 (by rfl) ⟨771545, by rfl⟩ : syracuseStep 1028727 = 1543091) B1543091
theorem B4698755 : Blo 1028606 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B1028747 : Blo 1028606 1028747 := bstep (se 1 (by rfl) ⟨771560, by rfl⟩ : syracuseStep 1028747 = 1543121) B1543121
theorem B1028759 : Blo 1028606 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B1028779 : Blo 1028606 1028779 := bstep (se 1 (by rfl) ⟨771584, by rfl⟩ : syracuseStep 1028779 = 1543169) B1543169
theorem B1028791 : Blo 1028606 1028791 := bstep (se 1 (by rfl) ⟨771593, by rfl⟩ : syracuseStep 1028791 = 1543187) B1543187
theorem B1028811 : Blo 1028606 1028811 := bstep (se 1 (by rfl) ⟨771608, by rfl⟩ : syracuseStep 1028811 = 1543217) B1543217
theorem B1028823 : Blo 1028606 1028823 := bstep (se 1 (by rfl) ⟨771617, by rfl⟩ : syracuseStep 1028823 = 1543235) B1543235
theorem B1028843 : Blo 1028606 1028843 := bstep (se 1 (by rfl) ⟨771632, by rfl⟩ : syracuseStep 1028843 = 1543265) B1543265
theorem B1159915 : Blo 1028606 1159915 := bstep (se 1 (by rfl) ⟨869936, by rfl⟩ : syracuseStep 1159915 = 1739873) B1739873
theorem B1028855 : Blo 1028606 1028855 := bstep (se 1 (by rfl) ⟨771641, by rfl⟩ : syracuseStep 1028855 = 1543283) B1543283
theorem B1028875 : Blo 1028606 1028875 := bstep (se 1 (by rfl) ⟨771656, by rfl⟩ : syracuseStep 1028875 = 1543313) B1543313
theorem B1028887 : Blo 1028606 1028887 := bstep (se 1 (by rfl) ⟨771665, by rfl⟩ : syracuseStep 1028887 = 1543331) B1543331
theorem B1028907 : Blo 1028606 1028907 := bstep (se 1 (by rfl) ⟨771680, by rfl⟩ : syracuseStep 1028907 = 1543361) B1543361
theorem B1028919 : Blo 1028606 1028919 := bstep (se 1 (by rfl) ⟨771689, by rfl⟩ : syracuseStep 1028919 = 1543379) B1543379
theorem B7418699 : Blo 1028606 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B1028939 : Blo 1028606 1028939 := bstep (se 1 (by rfl) ⟨771704, by rfl⟩ : syracuseStep 1028939 = 1543409) B1543409
theorem B1028951 : Blo 1028606 1028951 := bstep (se 1 (by rfl) ⟨771713, by rfl⟩ : syracuseStep 1028951 = 1543427) B1543427
theorem B1160023 : Blo 1028606 1160023 := bstep (se 1 (by rfl) ⟨870017, by rfl⟩ : syracuseStep 1160023 = 1740035) B1740035
theorem B1028971 : Blo 1028606 1028971 := bstep (se 1 (by rfl) ⟨771728, by rfl⟩ : syracuseStep 1028971 = 1543457) B1543457
theorem B1028983 : Blo 1028606 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B1029003 : Blo 1028606 1029003 := bstep (se 1 (by rfl) ⟨771752, by rfl⟩ : syracuseStep 1029003 = 1543505) B1543505
theorem B1029015 : Blo 1028606 1029015 := bstep (se 1 (by rfl) ⟨771761, by rfl⟩ : syracuseStep 1029015 = 1543523) B1543523
theorem B1029035 : Blo 1028606 1029035 := bstep (se 1 (by rfl) ⟨771776, by rfl⟩ : syracuseStep 1029035 = 1543553) B1543553
theorem B1029047 : Blo 1028606 1029047 := bstep (se 1 (by rfl) ⟨771785, by rfl⟩ : syracuseStep 1029047 = 1543571) B1543571
theorem B2929601 : Blo 1028606 2929601 := bstep (se 2 (by rfl) ⟨1098600, by rfl⟩ : syracuseStep 2929601 = 2197201) B2197201
theorem B1029067 : Blo 1028606 1029067 := bstep (se 1 (by rfl) ⟨771800, by rfl⟩ : syracuseStep 1029067 = 1543601) B1543601
theorem B1029079 : Blo 1028606 1029079 := bstep (se 1 (by rfl) ⟨771809, by rfl⟩ : syracuseStep 1029079 = 1543619) B1543619
theorem B1029099 : Blo 1028606 1029099 := bstep (se 1 (by rfl) ⟨771824, by rfl⟩ : syracuseStep 1029099 = 1543649) B1543649
theorem B1029111 : Blo 1028606 1029111 := bstep (se 1 (by rfl) ⟨771833, by rfl⟩ : syracuseStep 1029111 = 1543667) B1543667
theorem B1029131 : Blo 1028606 1029131 := bstep (se 1 (by rfl) ⟨771848, by rfl⟩ : syracuseStep 1029131 = 1543697) B1543697
theorem B1160203 : Blo 1028606 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B1029143 : Blo 1028606 1029143 := bstep (se 1 (by rfl) ⟨771857, by rfl⟩ : syracuseStep 1029143 = 1543715) B1543715
theorem B1029163 : Blo 1028606 1029163 := bstep (se 1 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 1029163 = 1543745) B1543745
theorem B2929715 : Blo 1028606 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B1029175 : Blo 1028606 1029175 := bstep (se 1 (by rfl) ⟨771881, by rfl⟩ : syracuseStep 1029175 = 1543763) B1543763
theorem B1029195 : Blo 1028606 1029195 := bstep (se 1 (by rfl) ⟨771896, by rfl⟩ : syracuseStep 1029195 = 1543793) B1543793
theorem B1586251 : Blo 1028606 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B1029207 : Blo 1028606 1029207 := bstep (se 1 (by rfl) ⟨771905, by rfl⟩ : syracuseStep 1029207 = 1543811) B1543811
theorem B1029227 : Blo 1028606 1029227 := bstep (se 1 (by rfl) ⟨771920, by rfl⟩ : syracuseStep 1029227 = 1543841) B1543841
theorem B1029239 : Blo 1028606 1029239 := bstep (se 1 (by rfl) ⟨771929, by rfl⟩ : syracuseStep 1029239 = 1543859) B1543859
theorem B1160311 : Blo 1028606 1160311 := bstep (se 1 (by rfl) ⟨870233, by rfl⟩ : syracuseStep 1160311 = 1740467) B1740467
theorem B1029259 : Blo 1028606 1029259 := bstep (se 1 (by rfl) ⟨771944, by rfl⟩ : syracuseStep 1029259 = 1543889) B1543889
theorem B1029271 : Blo 1028606 1029271 := bstep (se 1 (by rfl) ⟨771953, by rfl⟩ : syracuseStep 1029271 = 1543907) B1543907
theorem B1029291 : Blo 1028606 1029291 := bstep (se 1 (by rfl) ⟨771968, by rfl⟩ : syracuseStep 1029291 = 1543937) B1543937
theorem B1029303 : Blo 1028606 1029303 := bstep (se 1 (by rfl) ⟨771977, by rfl⟩ : syracuseStep 1029303 = 1543955) B1543955
theorem B1029323 : Blo 1028606 1029323 := bstep (se 1 (by rfl) ⟨771992, by rfl⟩ : syracuseStep 1029323 = 1543985) B1543985
theorem B3912907 : Blo 1028606 3912907 := bstep (se 1 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 3912907 = 5869361) B5869361
theorem B1029335 : Blo 1028606 1029335 := bstep (se 1 (by rfl) ⟨772001, by rfl⟩ : syracuseStep 1029335 = 1544003) B1544003
theorem B1029355 : Blo 1028606 1029355 := bstep (se 1 (by rfl) ⟨772016, by rfl⟩ : syracuseStep 1029355 = 1544033) B1544033
theorem B1029367 : Blo 1028606 1029367 := bstep (se 1 (by rfl) ⟨772025, by rfl⟩ : syracuseStep 1029367 = 1544051) B1544051
theorem B1029387 : Blo 1028606 1029387 := bstep (se 1 (by rfl) ⟨772040, by rfl⟩ : syracuseStep 1029387 = 1544081) B1544081
theorem B1029399 : Blo 1028606 1029399 := bstep (se 1 (by rfl) ⟨772049, by rfl⟩ : syracuseStep 1029399 = 1544099) B1544099
theorem B1029419 : Blo 1028606 1029419 := bstep (se 1 (by rfl) ⟨772064, by rfl⟩ : syracuseStep 1029419 = 1544129) B1544129
theorem B1160491 : Blo 1028606 1160491 := bstep (se 1 (by rfl) ⟨870368, by rfl⟩ : syracuseStep 1160491 = 1740737) B1740737
theorem B1029431 : Blo 1028606 1029431 := bstep (se 1 (by rfl) ⟨772073, by rfl⟩ : syracuseStep 1029431 = 1544147) B1544147
theorem B1029451 : Blo 1028606 1029451 := bstep (se 1 (by rfl) ⟨772088, by rfl⟩ : syracuseStep 1029451 = 1544177) B1544177
theorem B1029463 : Blo 1028606 1029463 := bstep (se 1 (by rfl) ⟨772097, by rfl⟩ : syracuseStep 1029463 = 1544195) B1544195
theorem B1029483 : Blo 1028606 1029483 := bstep (se 1 (by rfl) ⟨772112, by rfl⟩ : syracuseStep 1029483 = 1544225) B1544225
theorem B1029495 : Blo 1028606 1029495 := bstep (se 1 (by rfl) ⟨772121, by rfl⟩ : syracuseStep 1029495 = 1544243) B1544243
theorem B1029515 : Blo 1028606 1029515 := bstep (se 1 (by rfl) ⟨772136, by rfl⟩ : syracuseStep 1029515 = 1544273) B1544273
theorem B1029527 : Blo 1028606 1029527 := bstep (se 1 (by rfl) ⟨772145, by rfl⟩ : syracuseStep 1029527 = 1544291) B1544291
theorem B1160599 : Blo 1028606 1160599 := bstep (se 1 (by rfl) ⟨870449, by rfl⟩ : syracuseStep 1160599 = 1740899) B1740899
theorem B1029547 : Blo 1028606 1029547 := bstep (se 1 (by rfl) ⟨772160, by rfl⟩ : syracuseStep 1029547 = 1544321) B1544321
theorem B1029559 : Blo 1028606 1029559 := bstep (se 1 (by rfl) ⟨772169, by rfl⟩ : syracuseStep 1029559 = 1544339) B1544339
theorem B1029579 : Blo 1028606 1029579 := bstep (se 1 (by rfl) ⟨772184, by rfl⟩ : syracuseStep 1029579 = 1544369) B1544369
theorem B1029591 : Blo 1028606 1029591 := bstep (se 1 (by rfl) ⟨772193, by rfl⟩ : syracuseStep 1029591 = 1544387) B1544387
theorem B3913181 : Blo 1028606 3913181 := bstep (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) B1467443
theorem B1029611 : Blo 1028606 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B1029623 : Blo 1028606 1029623 := bstep (se 1 (by rfl) ⟨772217, by rfl⟩ : syracuseStep 1029623 = 1544435) B1544435
theorem B4404739 : Blo 1028606 4404739 := bstep (se 1 (by rfl) ⟨3303554, by rfl⟩ : syracuseStep 4404739 = 6607109) B6607109
theorem B1029643 : Blo 1028606 1029643 := bstep (se 1 (by rfl) ⟨772232, by rfl⟩ : syracuseStep 1029643 = 1544465) B1544465
theorem B1029655 : Blo 1028606 1029655 := bstep (se 1 (by rfl) ⟨772241, by rfl⟩ : syracuseStep 1029655 = 1544483) B1544483
theorem B1029675 : Blo 1028606 1029675 := bstep (se 1 (by rfl) ⟨772256, by rfl⟩ : syracuseStep 1029675 = 1544513) B1544513
theorem B1029687 : Blo 1028606 1029687 := bstep (se 1 (by rfl) ⟨772265, by rfl⟩ : syracuseStep 1029687 = 1544531) B1544531
theorem B1029707 : Blo 1028606 1029707 := bstep (se 1 (by rfl) ⟨772280, by rfl⟩ : syracuseStep 1029707 = 1544561) B1544561
theorem B1160779 : Blo 1028606 1160779 := bstep (se 1 (by rfl) ⟨870584, by rfl⟩ : syracuseStep 1160779 = 1741169) B1741169
theorem B1029719 : Blo 1028606 1029719 := bstep (se 1 (by rfl) ⟨772289, by rfl⟩ : syracuseStep 1029719 = 1544579) B1544579
theorem B1029739 : Blo 1028606 1029739 := bstep (se 1 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 1029739 = 1544609) B1544609
theorem B1029751 : Blo 1028606 1029751 := bstep (se 1 (by rfl) ⟨772313, by rfl⟩ : syracuseStep 1029751 = 1544627) B1544627
theorem B1029771 : Blo 1028606 1029771 := bstep (se 1 (by rfl) ⟨772328, by rfl⟩ : syracuseStep 1029771 = 1544657) B1544657
theorem B1029783 : Blo 1028606 1029783 := bstep (se 1 (by rfl) ⟨772337, by rfl⟩ : syracuseStep 1029783 = 1544675) B1544675
theorem B1029803 : Blo 1028606 1029803 := bstep (se 1 (by rfl) ⟨772352, by rfl⟩ : syracuseStep 1029803 = 1544705) B1544705
theorem B1029815 : Blo 1028606 1029815 := bstep (se 1 (by rfl) ⟨772361, by rfl⟩ : syracuseStep 1029815 = 1544723) B1544723
theorem B1160887 : Blo 1028606 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B1029835 : Blo 1028606 1029835 := bstep (se 1 (by rfl) ⟨772376, by rfl⟩ : syracuseStep 1029835 = 1544753) B1544753
theorem B1029847 : Blo 1028606 1029847 := bstep (se 1 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 1029847 = 1544771) B1544771
theorem B1029867 : Blo 1028606 1029867 := bstep (se 1 (by rfl) ⟨772400, by rfl⟩ : syracuseStep 1029867 = 1544801) B1544801
theorem B1029879 : Blo 1028606 1029879 := bstep (se 1 (by rfl) ⟨772409, by rfl⟩ : syracuseStep 1029879 = 1544819) B1544819
theorem B1029899 : Blo 1028606 1029899 := bstep (se 1 (by rfl) ⟨772424, by rfl⟩ : syracuseStep 1029899 = 1544849) B1544849
theorem B1029911 : Blo 1028606 1029911 := bstep (se 1 (by rfl) ⟨772433, by rfl⟩ : syracuseStep 1029911 = 1544867) B1544867
theorem B1029931 : Blo 1028606 1029931 := bstep (se 1 (by rfl) ⟨772448, by rfl⟩ : syracuseStep 1029931 = 1544897) B1544897
theorem B1029943 : Blo 1028606 1029943 := bstep (se 1 (by rfl) ⟨772457, by rfl⟩ : syracuseStep 1029943 = 1544915) B1544915
theorem B1029963 : Blo 1028606 1029963 := bstep (se 1 (by rfl) ⟨772472, by rfl⟩ : syracuseStep 1029963 = 1544945) B1544945
theorem B1029975 : Blo 1028606 1029975 := bstep (se 1 (by rfl) ⟨772481, by rfl⟩ : syracuseStep 1029975 = 1544963) B1544963
theorem B1029995 : Blo 1028606 1029995 := bstep (se 1 (by rfl) ⟨772496, by rfl⟩ : syracuseStep 1029995 = 1544993) B1544993
theorem B1161067 : Blo 1028606 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B1030007 : Blo 1028606 1030007 := bstep (se 1 (by rfl) ⟨772505, by rfl⟩ : syracuseStep 1030007 = 1545011) B1545011
theorem B1030027 : Blo 1028606 1030027 := bstep (se 1 (by rfl) ⟨772520, by rfl⟩ : syracuseStep 1030027 = 1545041) B1545041
theorem B1030039 : Blo 1028606 1030039 := bstep (se 1 (by rfl) ⟨772529, by rfl⟩ : syracuseStep 1030039 = 1545059) B1545059
theorem B1030059 : Blo 1028606 1030059 := bstep (se 1 (by rfl) ⟨772544, by rfl⟩ : syracuseStep 1030059 = 1545089) B1545089
theorem B1030071 : Blo 1028606 1030071 := bstep (se 1 (by rfl) ⟨772553, by rfl⟩ : syracuseStep 1030071 = 1545107) B1545107
theorem B1030091 : Blo 1028606 1030091 := bstep (se 1 (by rfl) ⟨772568, by rfl⟩ : syracuseStep 1030091 = 1545137) B1545137
theorem B1030103 : Blo 1028606 1030103 := bstep (se 1 (by rfl) ⟨772577, by rfl⟩ : syracuseStep 1030103 = 1545155) B1545155
theorem B1161175 : Blo 1028606 1161175 := bstep (se 1 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 1161175 = 1741763) B1741763
theorem B1030123 : Blo 1028606 1030123 := bstep (se 1 (by rfl) ⟨772592, by rfl⟩ : syracuseStep 1030123 = 1545185) B1545185
theorem B1030135 : Blo 1028606 1030135 := bstep (se 1 (by rfl) ⟨772601, by rfl⟩ : syracuseStep 1030135 = 1545203) B1545203
theorem B1030155 : Blo 1028606 1030155 := bstep (se 1 (by rfl) ⟨772616, by rfl⟩ : syracuseStep 1030155 = 1545233) B1545233
theorem B1030167 : Blo 1028606 1030167 := bstep (se 1 (by rfl) ⟨772625, by rfl⟩ : syracuseStep 1030167 = 1545251) B1545251
theorem B1030187 : Blo 1028606 1030187 := bstep (se 1 (by rfl) ⟨772640, by rfl⟩ : syracuseStep 1030187 = 1545281) B1545281
theorem B1030199 : Blo 1028606 1030199 := bstep (se 1 (by rfl) ⟨772649, by rfl⟩ : syracuseStep 1030199 = 1545299) B1545299
theorem B1030219 : Blo 1028606 1030219 := bstep (se 1 (by rfl) ⟨772664, by rfl⟩ : syracuseStep 1030219 = 1545329) B1545329
theorem B1030231 : Blo 1028606 1030231 := bstep (se 1 (by rfl) ⟨772673, by rfl⟩ : syracuseStep 1030231 = 1545347) B1545347
theorem B4405337 : Blo 1028606 4405337 := bstep (se 2 (by rfl) ⟨1652001, by rfl⟩ : syracuseStep 4405337 = 3304003) B3304003
theorem B1030251 : Blo 1028606 1030251 := bstep (se 1 (by rfl) ⟨772688, by rfl⟩ : syracuseStep 1030251 = 1545377) B1545377
theorem B1030263 : Blo 1028606 1030263 := bstep (se 1 (by rfl) ⟨772697, by rfl⟩ : syracuseStep 1030263 = 1545395) B1545395
theorem B1030283 : Blo 1028606 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B1161355 : Blo 1028606 1161355 := bstep (se 1 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 1161355 = 1742033) B1742033
theorem B1030295 : Blo 1028606 1030295 := bstep (se 1 (by rfl) ⟨772721, by rfl⟩ : syracuseStep 1030295 = 1545443) B1545443
theorem B3913879 : Blo 1028606 3913879 := bstep (se 1 (by rfl) ⟨2935409, by rfl⟩ : syracuseStep 3913879 = 5870819) B5870819
theorem B1030315 : Blo 1028606 1030315 := bstep (se 1 (by rfl) ⟨772736, by rfl⟩ : syracuseStep 1030315 = 1545473) B1545473
theorem B7420081 : Blo 1028606 7420081 := bstep (se 2 (by rfl) ⟨2782530, by rfl⟩ : syracuseStep 7420081 = 5565061) B5565061
theorem B1030327 : Blo 1028606 1030327 := bstep (se 1 (by rfl) ⟨772745, by rfl⟩ : syracuseStep 1030327 = 1545491) B1545491
theorem B1030347 : Blo 1028606 1030347 := bstep (se 1 (by rfl) ⟨772760, by rfl⟩ : syracuseStep 1030347 = 1545521) B1545521
theorem B1030359 : Blo 1028606 1030359 := bstep (se 1 (by rfl) ⟨772769, by rfl⟩ : syracuseStep 1030359 = 1545539) B1545539
theorem B1030379 : Blo 1028606 1030379 := bstep (se 1 (by rfl) ⟨772784, by rfl⟩ : syracuseStep 1030379 = 1545569) B1545569
theorem B1030391 : Blo 1028606 1030391 := bstep (se 1 (by rfl) ⟨772793, by rfl⟩ : syracuseStep 1030391 = 1545587) B1545587
theorem B1161463 : Blo 1028606 1161463 := bstep (se 1 (by rfl) ⟨871097, by rfl⟩ : syracuseStep 1161463 = 1742195) B1742195
theorem B1030411 : Blo 1028606 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B1030423 : Blo 1028606 1030423 := bstep (se 1 (by rfl) ⟨772817, by rfl⟩ : syracuseStep 1030423 = 1545635) B1545635
theorem B1030443 : Blo 1028606 1030443 := bstep (se 1 (by rfl) ⟨772832, by rfl⟩ : syracuseStep 1030443 = 1545665) B1545665
theorem B7813421 : Blo 1028606 7813421 := bstep (se 3 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 7813421 = 2930033) B2930033
theorem B1030455 : Blo 1028606 1030455 := bstep (se 1 (by rfl) ⟨772841, by rfl⟩ : syracuseStep 1030455 = 1545683) B1545683
theorem B1030475 : Blo 1028606 1030475 := bstep (se 1 (by rfl) ⟨772856, by rfl⟩ : syracuseStep 1030475 = 1545713) B1545713
theorem B1030487 : Blo 1028606 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B1030507 : Blo 1028606 1030507 := bstep (se 1 (by rfl) ⟨772880, by rfl⟩ : syracuseStep 1030507 = 1545761) B1545761
theorem B1030519 : Blo 1028606 1030519 := bstep (se 1 (by rfl) ⟨772889, by rfl⟩ : syracuseStep 1030519 = 1545779) B1545779
theorem B1030539 : Blo 1028606 1030539 := bstep (se 1 (by rfl) ⟨772904, by rfl⟩ : syracuseStep 1030539 = 1545809) B1545809
theorem B1030551 : Blo 1028606 1030551 := bstep (se 1 (by rfl) ⟨772913, by rfl⟩ : syracuseStep 1030551 = 1545827) B1545827
theorem B1030571 : Blo 1028606 1030571 := bstep (se 1 (by rfl) ⟨772928, by rfl⟩ : syracuseStep 1030571 = 1545857) B1545857
theorem B1161643 : Blo 1028606 1161643 := bstep (se 1 (by rfl) ⟨871232, by rfl⟩ : syracuseStep 1161643 = 1742465) B1742465
theorem B1030583 : Blo 1028606 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B4405697 : Blo 1028606 4405697 := bstep (se 2 (by rfl) ⟨1652136, by rfl⟩ : syracuseStep 4405697 = 3304273) B3304273
theorem B1030603 : Blo 1028606 1030603 := bstep (se 1 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 1030603 = 1545905) B1545905
theorem B1030615 : Blo 1028606 1030615 := bstep (se 1 (by rfl) ⟨772961, by rfl⟩ : syracuseStep 1030615 = 1545923) B1545923
theorem B1030635 : Blo 1028606 1030635 := bstep (se 1 (by rfl) ⟨772976, by rfl⟩ : syracuseStep 1030635 = 1545953) B1545953
theorem B1030647 : Blo 1028606 1030647 := bstep (se 1 (by rfl) ⟨772985, by rfl⟩ : syracuseStep 1030647 = 1545971) B1545971
theorem B1030667 : Blo 1028606 1030667 := bstep (se 1 (by rfl) ⟨773000, by rfl⟩ : syracuseStep 1030667 = 1546001) B1546001
theorem B1030679 : Blo 1028606 1030679 := bstep (se 1 (by rfl) ⟨773009, by rfl⟩ : syracuseStep 1030679 = 1546019) B1546019
theorem B1030699 : Blo 1028606 1030699 := bstep (se 1 (by rfl) ⟨773024, by rfl⟩ : syracuseStep 1030699 = 1546049) B1546049
theorem B1030711 : Blo 1028606 1030711 := bstep (se 1 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 1030711 = 1546067) B1546067
theorem B1030731 : Blo 1028606 1030731 := bstep (se 1 (by rfl) ⟨773048, by rfl⟩ : syracuseStep 1030731 = 1546097) B1546097
theorem B1030743 : Blo 1028606 1030743 := bstep (se 1 (by rfl) ⟨773057, by rfl⟩ : syracuseStep 1030743 = 1546115) B1546115
theorem B1030763 : Blo 1028606 1030763 := bstep (se 1 (by rfl) ⟨773072, by rfl⟩ : syracuseStep 1030763 = 1546145) B1546145
theorem B1030775 : Blo 1028606 1030775 := bstep (se 1 (by rfl) ⟨773081, by rfl⟩ : syracuseStep 1030775 = 1546163) B1546163
theorem B1030795 : Blo 1028606 1030795 := bstep (se 1 (by rfl) ⟨773096, by rfl⟩ : syracuseStep 1030795 = 1546193) B1546193
theorem B1030807 : Blo 1028606 1030807 := bstep (se 1 (by rfl) ⟨773105, by rfl⟩ : syracuseStep 1030807 = 1546211) B1546211
theorem B1030827 : Blo 1028606 1030827 := bstep (se 1 (by rfl) ⟨773120, by rfl⟩ : syracuseStep 1030827 = 1546241) B1546241
theorem B1030839 : Blo 1028606 1030839 := bstep (se 1 (by rfl) ⟨773129, by rfl⟩ : syracuseStep 1030839 = 1546259) B1546259
theorem B1030859 : Blo 1028606 1030859 := bstep (se 1 (by rfl) ⟨773144, by rfl⟩ : syracuseStep 1030859 = 1546289) B1546289
theorem B1030871 : Blo 1028606 1030871 := bstep (se 1 (by rfl) ⟨773153, by rfl⟩ : syracuseStep 1030871 = 1546307) B1546307
theorem B1030891 : Blo 1028606 1030891 := bstep (se 1 (by rfl) ⟨773168, by rfl⟩ : syracuseStep 1030891 = 1546337) B1546337
theorem B1030903 : Blo 1028606 1030903 := bstep (se 1 (by rfl) ⟨773177, by rfl⟩ : syracuseStep 1030903 = 1546355) B1546355
theorem B1030923 : Blo 1028606 1030923 := bstep (se 1 (by rfl) ⟨773192, by rfl⟩ : syracuseStep 1030923 = 1546385) B1546385
theorem B1030935 : Blo 1028606 1030935 := bstep (se 1 (by rfl) ⟨773201, by rfl⟩ : syracuseStep 1030935 = 1546403) B1546403
theorem B1030955 : Blo 1028606 1030955 := bstep (se 1 (by rfl) ⟨773216, by rfl⟩ : syracuseStep 1030955 = 1546433) B1546433
theorem B1030967 : Blo 1028606 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B1030987 : Blo 1028606 1030987 := bstep (se 1 (by rfl) ⟨773240, by rfl⟩ : syracuseStep 1030987 = 1546481) B1546481
theorem B1030999 : Blo 1028606 1030999 := bstep (se 1 (by rfl) ⟨773249, by rfl⟩ : syracuseStep 1030999 = 1546499) B1546499
theorem B5225309 : Blo 1028606 5225309 := bstep (se 3 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 5225309 = 1959491) B1959491
theorem B1031019 : Blo 1028606 1031019 := bstep (se 1 (by rfl) ⟨773264, by rfl⟩ : syracuseStep 1031019 = 1546529) B1546529
theorem B1031031 : Blo 1028606 1031031 := bstep (se 1 (by rfl) ⟨773273, by rfl⟩ : syracuseStep 1031031 = 1546547) B1546547
theorem B5880707 : Blo 1028606 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B1031051 : Blo 1028606 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B2603927 : Blo 1028606 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B1031063 : Blo 1028606 1031063 := bstep (se 1 (by rfl) ⟨773297, by rfl⟩ : syracuseStep 1031063 = 1546595) B1546595
theorem B1031083 : Blo 1028606 1031083 := bstep (se 1 (by rfl) ⟨773312, by rfl⟩ : syracuseStep 1031083 = 1546625) B1546625
theorem B3914669 : Blo 1028606 3914669 := bstep (se 3 (by rfl) ⟨734000, by rfl⟩ : syracuseStep 3914669 = 1468001) B1468001
theorem B1031095 : Blo 1028606 1031095 := bstep (se 1 (by rfl) ⟨773321, by rfl⟩ : syracuseStep 1031095 = 1546643) B1546643
theorem B81476549 : Blo 1028606 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1031115 : Blo 1028606 1031115 := bstep (se 1 (by rfl) ⟨773336, by rfl⟩ : syracuseStep 1031115 = 1546673) B1546673
theorem B1031127 : Blo 1028606 1031127 := bstep (se 1 (by rfl) ⟨773345, by rfl⟩ : syracuseStep 1031127 = 1546691) B1546691
theorem B1031147 : Blo 1028606 1031147 := bstep (se 1 (by rfl) ⟨773360, by rfl⟩ : syracuseStep 1031147 = 1546721) B1546721
theorem B1031159 : Blo 1028606 1031159 := bstep (se 1 (by rfl) ⟨773369, by rfl⟩ : syracuseStep 1031159 = 1546739) B1546739
theorem B1031179 : Blo 1028606 1031179 := bstep (se 1 (by rfl) ⟨773384, by rfl⟩ : syracuseStep 1031179 = 1546769) B1546769
theorem B1031191 : Blo 1028606 1031191 := bstep (se 1 (by rfl) ⟨773393, by rfl⟩ : syracuseStep 1031191 = 1546787) B1546787
theorem B1031211 : Blo 1028606 1031211 := bstep (se 1 (by rfl) ⟨773408, by rfl⟩ : syracuseStep 1031211 = 1546817) B1546817
theorem B4701229 : Blo 1028606 4701229 := bstep (se 3 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 4701229 = 1762961) B1762961
theorem B1031223 : Blo 1028606 1031223 := bstep (se 1 (by rfl) ⟨773417, by rfl⟩ : syracuseStep 1031223 = 1546835) B1546835
theorem B1031243 : Blo 1028606 1031243 := bstep (se 1 (by rfl) ⟨773432, by rfl⟩ : syracuseStep 1031243 = 1546865) B1546865
theorem B1031255 : Blo 1028606 1031255 := bstep (se 1 (by rfl) ⟨773441, by rfl⟩ : syracuseStep 1031255 = 1546883) B1546883
theorem B1031275 : Blo 1028606 1031275 := bstep (se 1 (by rfl) ⟨773456, by rfl⟩ : syracuseStep 1031275 = 1546913) B1546913
theorem B1031287 : Blo 1028606 1031287 := bstep (se 1 (by rfl) ⟨773465, by rfl⟩ : syracuseStep 1031287 = 1546931) B1546931
theorem B1031307 : Blo 1028606 1031307 := bstep (se 1 (by rfl) ⟨773480, by rfl⟩ : syracuseStep 1031307 = 1546961) B1546961
theorem B1031319 : Blo 1028606 1031319 := bstep (se 1 (by rfl) ⟨773489, by rfl⟩ : syracuseStep 1031319 = 1546979) B1546979
theorem B1031339 : Blo 1028606 1031339 := bstep (se 1 (by rfl) ⟨773504, by rfl⟩ : syracuseStep 1031339 = 1547009) B1547009
theorem B2473139 : Blo 1028606 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B1031351 : Blo 1028606 1031351 := bstep (se 1 (by rfl) ⟨773513, by rfl⟩ : syracuseStep 1031351 = 1547027) B1547027
theorem B1031371 : Blo 1028606 1031371 := bstep (se 1 (by rfl) ⟨773528, by rfl⟩ : syracuseStep 1031371 = 1547057) B1547057
theorem B1031383 : Blo 1028606 1031383 := bstep (se 1 (by rfl) ⟨773537, by rfl⟩ : syracuseStep 1031383 = 1547075) B1547075
theorem B1391833 : Blo 1028606 1391833 := bstep (se 2 (by rfl) ⟨521937, by rfl⟩ : syracuseStep 1391833 = 1043875) B1043875
theorem B1031403 : Blo 1028606 1031403 := bstep (se 1 (by rfl) ⟨773552, by rfl⟩ : syracuseStep 1031403 = 1547105) B1547105
theorem B1031415 : Blo 1028606 1031415 := bstep (se 1 (by rfl) ⟨773561, by rfl⟩ : syracuseStep 1031415 = 1547123) B1547123
theorem B1031435 : Blo 1028606 1031435 := bstep (se 1 (by rfl) ⟨773576, by rfl⟩ : syracuseStep 1031435 = 1547153) B1547153
theorem B1031447 : Blo 1028606 1031447 := bstep (se 1 (by rfl) ⟨773585, by rfl⟩ : syracuseStep 1031447 = 1547171) B1547171
theorem B1031467 : Blo 1028606 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B1031479 : Blo 1028606 1031479 := bstep (se 1 (by rfl) ⟨773609, by rfl⟩ : syracuseStep 1031479 = 1547219) B1547219
theorem B1031499 : Blo 1028606 1031499 := bstep (se 1 (by rfl) ⟨773624, by rfl⟩ : syracuseStep 1031499 = 1547249) B1547249
theorem B1031511 : Blo 1028606 1031511 := bstep (se 1 (by rfl) ⟨773633, by rfl⟩ : syracuseStep 1031511 = 1547267) B1547267
theorem B1031531 : Blo 1028606 1031531 := bstep (se 1 (by rfl) ⟨773648, by rfl⟩ : syracuseStep 1031531 = 1547297) B1547297
theorem B1031543 : Blo 1028606 1031543 := bstep (se 1 (by rfl) ⟨773657, by rfl⟩ : syracuseStep 1031543 = 1547315) B1547315
theorem B1031563 : Blo 1028606 1031563 := bstep (se 1 (by rfl) ⟨773672, by rfl⟩ : syracuseStep 1031563 = 1547345) B1547345
theorem B1031575 : Blo 1028606 1031575 := bstep (se 1 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 1031575 = 1547363) B1547363
theorem B1031595 : Blo 1028606 1031595 := bstep (se 1 (by rfl) ⟨773696, by rfl⟩ : syracuseStep 1031595 = 1547393) B1547393
theorem B1031607 : Blo 1028606 1031607 := bstep (se 1 (by rfl) ⟨773705, by rfl⟩ : syracuseStep 1031607 = 1547411) B1547411
theorem B2473409 : Blo 1028606 2473409 := bstep (se 2 (by rfl) ⟨927528, by rfl⟩ : syracuseStep 2473409 = 1855057) B1855057
theorem B1031627 : Blo 1028606 1031627 := bstep (se 1 (by rfl) ⟨773720, by rfl⟩ : syracuseStep 1031627 = 1547441) B1547441
theorem B1031639 : Blo 1028606 1031639 := bstep (se 1 (by rfl) ⟨773729, by rfl⟩ : syracuseStep 1031639 = 1547459) B1547459
theorem B1031659 : Blo 1028606 1031659 := bstep (se 1 (by rfl) ⟨773744, by rfl⟩ : syracuseStep 1031659 = 1547489) B1547489
theorem B1031671 : Blo 1028606 1031671 := bstep (se 1 (by rfl) ⟨773753, by rfl⟩ : syracuseStep 1031671 = 1547507) B1547507
theorem B1031691 : Blo 1028606 1031691 := bstep (se 1 (by rfl) ⟨773768, by rfl⟩ : syracuseStep 1031691 = 1547537) B1547537
theorem B1031703 : Blo 1028606 1031703 := bstep (se 1 (by rfl) ⟨773777, by rfl⟩ : syracuseStep 1031703 = 1547555) B1547555
theorem B1031723 : Blo 1028606 1031723 := bstep (se 1 (by rfl) ⟨773792, by rfl⟩ : syracuseStep 1031723 = 1547585) B1547585
theorem B2604595 : Blo 1028606 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B1031735 : Blo 1028606 1031735 := bstep (se 1 (by rfl) ⟨773801, by rfl⟩ : syracuseStep 1031735 = 1547603) B1547603
theorem B1031755 : Blo 1028606 1031755 := bstep (se 1 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 1031755 = 1547633) B1547633
theorem B1031767 : Blo 1028606 1031767 := bstep (se 1 (by rfl) ⟨773825, by rfl⟩ : syracuseStep 1031767 = 1547651) B1547651
theorem B1031787 : Blo 1028606 1031787 := bstep (se 1 (by rfl) ⟨773840, by rfl⟩ : syracuseStep 1031787 = 1547681) B1547681
theorem B1031799 : Blo 1028606 1031799 := bstep (se 1 (by rfl) ⟨773849, by rfl⟩ : syracuseStep 1031799 = 1547699) B1547699
theorem B1031819 : Blo 1028606 1031819 := bstep (se 1 (by rfl) ⟨773864, by rfl⟩ : syracuseStep 1031819 = 1547729) B1547729
theorem B1031831 : Blo 1028606 1031831 := bstep (se 1 (by rfl) ⟨773873, by rfl⟩ : syracuseStep 1031831 = 1547747) B1547747
theorem B1031851 : Blo 1028606 1031851 := bstep (se 1 (by rfl) ⟨773888, by rfl⟩ : syracuseStep 1031851 = 1547777) B1547777
theorem B1031863 : Blo 1028606 1031863 := bstep (se 1 (by rfl) ⟨773897, by rfl⟩ : syracuseStep 1031863 = 1547795) B1547795
theorem B2604737 : Blo 1028606 2604737 := bstep (se 2 (by rfl) ⟨976776, by rfl⟩ : syracuseStep 2604737 = 1953553) B1953553
theorem B1392331 : Blo 1028606 1392331 := bstep (se 1 (by rfl) ⟨1044248, by rfl⟩ : syracuseStep 1392331 = 2088497) B2088497
theorem B1031883 : Blo 1028606 1031883 := bstep (se 1 (by rfl) ⟨773912, by rfl⟩ : syracuseStep 1031883 = 1547825) B1547825
theorem B1031895 : Blo 1028606 1031895 := bstep (se 1 (by rfl) ⟨773921, by rfl⟩ : syracuseStep 1031895 = 1547843) B1547843
theorem B1031915 : Blo 1028606 1031915 := bstep (se 1 (by rfl) ⟨773936, by rfl⟩ : syracuseStep 1031915 = 1547873) B1547873
theorem B1031927 : Blo 1028606 1031927 := bstep (se 1 (by rfl) ⟨773945, by rfl⟩ : syracuseStep 1031927 = 1547891) B1547891
theorem B1031947 : Blo 1028606 1031947 := bstep (se 1 (by rfl) ⟨773960, by rfl⟩ : syracuseStep 1031947 = 1547921) B1547921
theorem B1031959 : Blo 1028606 1031959 := bstep (se 1 (by rfl) ⟨773969, by rfl⟩ : syracuseStep 1031959 = 1547939) B1547939
theorem B1031979 : Blo 1028606 1031979 := bstep (se 1 (by rfl) ⟨773984, by rfl⟩ : syracuseStep 1031979 = 1547969) B1547969
theorem B1031991 : Blo 1028606 1031991 := bstep (se 1 (by rfl) ⟨773993, by rfl⟩ : syracuseStep 1031991 = 1547987) B1547987
theorem B1032011 : Blo 1028606 1032011 := bstep (se 1 (by rfl) ⟨774008, by rfl⟩ : syracuseStep 1032011 = 1548017) B1548017
theorem B1032023 : Blo 1028606 1032023 := bstep (se 1 (by rfl) ⟨774017, by rfl⟩ : syracuseStep 1032023 = 1548035) B1548035
theorem B1032043 : Blo 1028606 1032043 := bstep (se 1 (by rfl) ⟨774032, by rfl⟩ : syracuseStep 1032043 = 1548065) B1548065
theorem B1032055 : Blo 1028606 1032055 := bstep (se 1 (by rfl) ⟨774041, by rfl⟩ : syracuseStep 1032055 = 1548083) B1548083
theorem B1032075 : Blo 1028606 1032075 := bstep (se 1 (by rfl) ⟨774056, by rfl⟩ : syracuseStep 1032075 = 1548113) B1548113
theorem B2932631 : Blo 1028606 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B1032087 : Blo 1028606 1032087 := bstep (se 1 (by rfl) ⟨774065, by rfl⟩ : syracuseStep 1032087 = 1548131) B1548131
theorem B1032107 : Blo 1028606 1032107 := bstep (se 1 (by rfl) ⟨774080, by rfl⟩ : syracuseStep 1032107 = 1548161) B1548161
theorem B14106545 : Blo 1028606 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B2473907 : Blo 1028606 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1032119 : Blo 1028606 1032119 := bstep (se 1 (by rfl) ⟨774089, by rfl⟩ : syracuseStep 1032119 = 1548179) B1548179
theorem B1032139 : Blo 1028606 1032139 := bstep (se 1 (by rfl) ⟨774104, by rfl⟩ : syracuseStep 1032139 = 1548209) B1548209
theorem B1032151 : Blo 1028606 1032151 := bstep (se 1 (by rfl) ⟨774113, by rfl⟩ : syracuseStep 1032151 = 1548227) B1548227
theorem B1032171 : Blo 1028606 1032171 := bstep (se 1 (by rfl) ⟨774128, by rfl⟩ : syracuseStep 1032171 = 1548257) B1548257
theorem B1032183 : Blo 1028606 1032183 := bstep (se 1 (by rfl) ⟨774137, by rfl⟩ : syracuseStep 1032183 = 1548275) B1548275
theorem B1032203 : Blo 1028606 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B1032215 : Blo 1028606 1032215 := bstep (se 1 (by rfl) ⟨774161, by rfl⟩ : syracuseStep 1032215 = 1548323) B1548323
theorem B1032235 : Blo 1028606 1032235 := bstep (se 1 (by rfl) ⟨774176, by rfl⟩ : syracuseStep 1032235 = 1548353) B1548353
theorem B1032247 : Blo 1028606 1032247 := bstep (se 1 (by rfl) ⟨774185, by rfl⟩ : syracuseStep 1032247 = 1548371) B1548371
theorem B1032267 : Blo 1028606 1032267 := bstep (se 1 (by rfl) ⟨774200, by rfl⟩ : syracuseStep 1032267 = 1548401) B1548401
theorem B1032279 : Blo 1028606 1032279 := bstep (se 1 (by rfl) ⟨774209, by rfl⟩ : syracuseStep 1032279 = 1548419) B1548419
theorem B4243549 : Blo 1028606 4243549 := bstep (se 3 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 4243549 = 1591331) B1591331
theorem B1032299 : Blo 1028606 1032299 := bstep (se 1 (by rfl) ⟨774224, by rfl⟩ : syracuseStep 1032299 = 1548449) B1548449
theorem B1032311 : Blo 1028606 1032311 := bstep (se 1 (by rfl) ⟨774233, by rfl⟩ : syracuseStep 1032311 = 1548467) B1548467
theorem B1032331 : Blo 1028606 1032331 := bstep (se 1 (by rfl) ⟨774248, by rfl⟩ : syracuseStep 1032331 = 1548497) B1548497
theorem B1032343 : Blo 1028606 1032343 := bstep (se 1 (by rfl) ⟨774257, by rfl⟩ : syracuseStep 1032343 = 1548515) B1548515
theorem B1032363 : Blo 1028606 1032363 := bstep (se 1 (by rfl) ⟨774272, by rfl⟩ : syracuseStep 1032363 = 1548545) B1548545
theorem B1032375 : Blo 1028606 1032375 := bstep (se 1 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 1032375 = 1548563) B1548563
theorem B1032395 : Blo 1028606 1032395 := bstep (se 1 (by rfl) ⟨774296, by rfl⟩ : syracuseStep 1032395 = 1548593) B1548593
theorem B1032407 : Blo 1028606 1032407 := bstep (se 1 (by rfl) ⟨774305, by rfl⟩ : syracuseStep 1032407 = 1548611) B1548611
theorem B1032427 : Blo 1028606 1032427 := bstep (se 1 (by rfl) ⟨774320, by rfl⟩ : syracuseStep 1032427 = 1548641) B1548641
theorem B1032439 : Blo 1028606 1032439 := bstep (se 1 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 1032439 = 1548659) B1548659
theorem B1032459 : Blo 1028606 1032459 := bstep (se 1 (by rfl) ⟨774344, by rfl⟩ : syracuseStep 1032459 = 1548689) B1548689
theorem B1032471 : Blo 1028606 1032471 := bstep (se 1 (by rfl) ⟨774353, by rfl⟩ : syracuseStep 1032471 = 1548707) B1548707
theorem B1032491 : Blo 1028606 1032491 := bstep (se 1 (by rfl) ⟨774368, by rfl⟩ : syracuseStep 1032491 = 1548737) B1548737
theorem B1032503 : Blo 1028606 1032503 := bstep (se 1 (by rfl) ⟨774377, by rfl⟩ : syracuseStep 1032503 = 1548755) B1548755
theorem B3916097 : Blo 1028606 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B1032523 : Blo 1028606 1032523 := bstep (se 1 (by rfl) ⟨774392, by rfl⟩ : syracuseStep 1032523 = 1548785) B1548785
theorem B1032535 : Blo 1028606 1032535 := bstep (se 1 (by rfl) ⟨774401, by rfl⟩ : syracuseStep 1032535 = 1548803) B1548803
theorem B1032555 : Blo 1028606 1032555 := bstep (se 1 (by rfl) ⟨774416, by rfl⟩ : syracuseStep 1032555 = 1548833) B1548833
theorem B1032567 : Blo 1028606 1032567 := bstep (se 1 (by rfl) ⟨774425, by rfl⟩ : syracuseStep 1032567 = 1548851) B1548851
theorem B1032587 : Blo 1028606 1032587 := bstep (se 1 (by rfl) ⟨774440, by rfl⟩ : syracuseStep 1032587 = 1548881) B1548881
theorem B1032599 : Blo 1028606 1032599 := bstep (se 1 (by rfl) ⟨774449, by rfl⟩ : syracuseStep 1032599 = 1548899) B1548899
theorem B3719627 : Blo 1028606 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B1393303 : Blo 1028606 1393303 := bstep (se 1 (by rfl) ⟨1044977, by rfl⟩ : syracuseStep 1393303 = 2089955) B2089955
theorem B4178611 : Blo 1028606 4178611 := bstep (se 1 (by rfl) ⟨3133958, by rfl⟩ : syracuseStep 4178611 = 6267917) B6267917
theorem B6603443 : Blo 1028606 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B1098455 : Blo 1028606 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B5227415 : Blo 1028606 5227415 := bstep (se 1 (by rfl) ⟨3920561, by rfl⟩ : syracuseStep 5227415 = 7841123) B7841123
theorem B2606003 : Blo 1028606 2606003 := bstep (se 1 (by rfl) ⟨1954502, by rfl⟩ : syracuseStep 2606003 = 3909005) B3909005
theorem B1590359 : Blo 1028606 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1099019 : Blo 1028606 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B2606539 : Blo 1028606 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B2606681 : Blo 1028606 2606681 := bstep (se 2 (by rfl) ⟨977505, by rfl⟩ : syracuseStep 2606681 = 1955011) B1955011
theorem B3917585 : Blo 1028606 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B7817309 : Blo 1028606 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B4409437 : Blo 1028606 4409437 := bstep (se 3 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 4409437 = 1653539) B1653539
theorem B3918041 : Blo 1028606 3918041 := bstep (se 2 (by rfl) ⟨1469265, by rfl⟩ : syracuseStep 3918041 = 2938531) B2938531
theorem B2935091 : Blo 1028606 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B2607511 : Blo 1028606 2607511 := bstep (se 1 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 2607511 = 3911267) B3911267
theorem B3918253 : Blo 1028606 3918253 := bstep (se 3 (by rfl) ⟨734672, by rfl⟩ : syracuseStep 3918253 = 1469345) B1469345
theorem B4704733 : Blo 1028606 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B2476619 : Blo 1028606 2476619 := bstep (se 1 (by rfl) ⟨1857464, by rfl⟩ : syracuseStep 2476619 = 3714929) B3714929
theorem B1100471 : Blo 1028606 1100471 := bstep (se 1 (by rfl) ⟨825353, by rfl⟩ : syracuseStep 1100471 = 1650707) B1650707
theorem B3918557 : Blo 1028606 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B1985303 : Blo 1028606 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B2607947 : Blo 1028606 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B1854451 : Blo 1028606 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B11160611 : Blo 1028606 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B13388951 : Blo 1028606 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B2608321 : Blo 1028606 2608321 := bstep (se 2 (by rfl) ⟨978120, by rfl⟩ : syracuseStep 2608321 = 1956241) B1956241
theorem B3132695 : Blo 1028606 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B8801581 : Blo 1028606 8801581 := bstep (se 3 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 8801581 = 3300593) B3300593
theorem B1854913 : Blo 1028606 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B1953227 : Blo 1028606 1953227 := bstep (se 1 (by rfl) ⟨1464920, by rfl⟩ : syracuseStep 1953227 = 2929841) B2929841
theorem B1985995 : Blo 1028606 1985995 := bstep (se 1 (by rfl) ⟨1489496, by rfl⟩ : syracuseStep 1985995 = 2978993) B2978993
theorem B2117081 : Blo 1028606 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B2477591 : Blo 1028606 2477591 := bstep (se 1 (by rfl) ⟨1858193, by rfl⟩ : syracuseStep 2477591 = 3716387) B3716387
theorem B8474147 : Blo 1028606 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B1953409 : Blo 1028606 1953409 := bstep (se 2 (by rfl) ⟨732528, by rfl⟩ : syracuseStep 1953409 = 1465057) B1465057
theorem B2608919 : Blo 1028606 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B1855489 : Blo 1028606 1855489 := bstep (se 2 (by rfl) ⟨695808, by rfl⟩ : syracuseStep 1855489 = 1391617) B1391617
theorem B1953857 : Blo 1028606 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B2969779 : Blo 1028606 2969779 := bstep (se 1 (by rfl) ⟨2227334, by rfl⟩ : syracuseStep 2969779 = 4454669) B4454669
theorem B2314457 : Blo 1028606 2314457 := bstep (se 2 (by rfl) ⟨867921, by rfl⟩ : syracuseStep 2314457 = 1735843) B1735843
theorem B2314547 : Blo 1028606 2314547 := bstep (se 1 (by rfl) ⟨1735910, by rfl⟩ : syracuseStep 2314547 = 3471821) B3471821
theorem B2314583 : Blo 1028606 2314583 := bstep (se 1 (by rfl) ⟨1735937, by rfl⟩ : syracuseStep 2314583 = 3471875) B3471875
theorem B2871641 : Blo 1028606 2871641 := bstep (se 2 (by rfl) ⟨1076865, by rfl⟩ : syracuseStep 2871641 = 2153731) B2153731
theorem B1986905 : Blo 1028606 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B1954199 : Blo 1028606 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B1102231 : Blo 1028606 1102231 := bstep (se 1 (by rfl) ⟨826673, by rfl⟩ : syracuseStep 1102231 = 1653347) B1653347
theorem B2314763 : Blo 1028606 2314763 := bstep (se 1 (by rfl) ⟨1736072, by rfl⟩ : syracuseStep 2314763 = 3472145) B3472145
theorem B2314817 : Blo 1028606 2314817 := bstep (se 2 (by rfl) ⟨868056, by rfl⟩ : syracuseStep 2314817 = 1736113) B1736113
theorem B2609729 : Blo 1028606 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B8802917 : Blo 1028606 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B2315033 : Blo 1028606 2315033 := bstep (se 2 (by rfl) ⟨868137, by rfl⟩ : syracuseStep 2315033 = 1736275) B1736275
theorem B2315123 : Blo 1028606 2315123 := bstep (se 1 (by rfl) ⟨1736342, by rfl⟩ : syracuseStep 2315123 = 3472685) B3472685
theorem B6607747 : Blo 1028606 6607747 := bstep (se 1 (by rfl) ⟨4955810, by rfl⟩ : syracuseStep 6607747 = 9911621) B9911621
theorem B2315159 : Blo 1028606 2315159 := bstep (se 1 (by rfl) ⟨1736369, by rfl⟩ : syracuseStep 2315159 = 3472739) B3472739
theorem B2937779 : Blo 1028606 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B51434531 : Blo 1028606 51434531 := bstep (se 1 (by rfl) ⟨38575898, by rfl⟩ : syracuseStep 51434531 = 77151797) B77151797
theorem B1954867 : Blo 1028606 1954867 := bstep (se 1 (by rfl) ⟨1466150, by rfl⟩ : syracuseStep 1954867 = 2932301) B2932301
theorem B2315339 : Blo 1028606 2315339 := bstep (se 1 (by rfl) ⟨1736504, by rfl⟩ : syracuseStep 2315339 = 3473009) B3473009
theorem B2610265 : Blo 1028606 2610265 := bstep (se 2 (by rfl) ⟨978849, by rfl⟩ : syracuseStep 2610265 = 1957699) B1957699
theorem B2315393 : Blo 1028606 2315393 := bstep (se 2 (by rfl) ⟨868272, by rfl⟩ : syracuseStep 2315393 = 1736545) B1736545
theorem B2938007 : Blo 1028606 2938007 := bstep (se 1 (by rfl) ⟨2203505, by rfl⟩ : syracuseStep 2938007 = 4407011) B4407011
theorem B1856729 : Blo 1028606 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B2315609 : Blo 1028606 2315609 := bstep (se 2 (by rfl) ⟨868353, by rfl⟩ : syracuseStep 2315609 = 1736707) B1736707
theorem B28202357 : Blo 1028606 28202357 := bstep (se 5 (by rfl) ⟨1321985, by rfl⟩ : syracuseStep 28202357 = 2643971) B2643971
theorem B4183447 : Blo 1028606 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2315699 : Blo 1028606 2315699 := bstep (se 1 (by rfl) ⟨1736774, by rfl⟩ : syracuseStep 2315699 = 3473549) B3473549
theorem B2938315 : Blo 1028606 2938315 := bstep (se 1 (by rfl) ⟨2203736, by rfl⟩ : syracuseStep 2938315 = 4407473) B4407473
theorem B2315735 : Blo 1028606 2315735 := bstep (se 1 (by rfl) ⟨1736801, by rfl⟩ : syracuseStep 2315735 = 3473603) B3473603
theorem B1955315 : Blo 1028606 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B1955353 : Blo 1028606 1955353 := bstep (se 2 (by rfl) ⟨733257, by rfl⟩ : syracuseStep 1955353 = 1466515) B1466515
theorem B2315915 : Blo 1028606 2315915 := bstep (se 1 (by rfl) ⟨1736936, by rfl⟩ : syracuseStep 2315915 = 3473873) B3473873
theorem B2315969 : Blo 1028606 2315969 := bstep (se 2 (by rfl) ⟨868488, by rfl⟩ : syracuseStep 2315969 = 1736977) B1736977
theorem B2938589 : Blo 1028606 2938589 := bstep (se 3 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 2938589 = 1101971) B1101971
theorem B2316185 : Blo 1028606 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B2480051 : Blo 1028606 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B1955801 : Blo 1028606 1955801 := bstep (se 2 (by rfl) ⟨733425, by rfl⟩ : syracuseStep 1955801 = 1466851) B1466851
theorem B2316275 : Blo 1028606 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B2316311 : Blo 1028606 2316311 := bstep (se 1 (by rfl) ⟨1737233, by rfl⟩ : syracuseStep 2316311 = 3474467) B3474467
theorem B2349121 : Blo 1028606 2349121 := bstep (se 2 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 2349121 = 1761841) B1761841
theorem B2611379 : Blo 1028606 2611379 := bstep (se 1 (by rfl) ⟨1958534, by rfl⟩ : syracuseStep 2611379 = 3917069) B3917069
theorem B2316491 : Blo 1028606 2316491 := bstep (se 1 (by rfl) ⟨1737368, by rfl⟩ : syracuseStep 2316491 = 3474737) B3474737
theorem B2316545 : Blo 1028606 2316545 := bstep (se 2 (by rfl) ⟨868704, by rfl⟩ : syracuseStep 2316545 = 1737409) B1737409
theorem B2480435 : Blo 1028606 2480435 := bstep (se 1 (by rfl) ⟨1860326, by rfl⟩ : syracuseStep 2480435 = 3720653) B3720653
theorem B3135809 : Blo 1028606 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B2316761 : Blo 1028606 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B2611673 : Blo 1028606 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B13195811 : Blo 1028606 13195811 := bstep (se 1 (by rfl) ⟨9896858, by rfl⟩ : syracuseStep 13195811 = 19793717) B19793717
theorem B2316851 : Blo 1028606 2316851 := bstep (se 1 (by rfl) ⟨1737638, by rfl⟩ : syracuseStep 2316851 = 3475277) B3475277
theorem B2316887 : Blo 1028606 2316887 := bstep (se 1 (by rfl) ⟨1737665, by rfl⟩ : syracuseStep 2316887 = 3475331) B3475331
theorem B1464971 : Blo 1028606 1464971 := bstep (se 1 (by rfl) ⟨1098728, by rfl⟩ : syracuseStep 1464971 = 2197457) B2197457
theorem B1956545 : Blo 1028606 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B2317067 : Blo 1028606 2317067 := bstep (se 1 (by rfl) ⟨1737800, by rfl⟩ : syracuseStep 2317067 = 3475601) B3475601
theorem B1858315 : Blo 1028606 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B2317121 : Blo 1028606 2317121 := bstep (se 2 (by rfl) ⟨868920, by rfl⟩ : syracuseStep 2317121 = 1737841) B1737841
theorem B2087831 : Blo 1028606 2087831 := bstep (se 1 (by rfl) ⟨1565873, by rfl⟩ : syracuseStep 2087831 = 3131747) B3131747
theorem B1956811 : Blo 1028606 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B2317337 : Blo 1028606 2317337 := bstep (se 2 (by rfl) ⟨869001, by rfl⟩ : syracuseStep 2317337 = 1738003) B1738003
theorem B2317427 : Blo 1028606 2317427 := bstep (se 1 (by rfl) ⟨1738070, by rfl⟩ : syracuseStep 2317427 = 3476141) B3476141
theorem B2317463 : Blo 1028606 2317463 := bstep (se 1 (by rfl) ⟨1738097, by rfl⟩ : syracuseStep 2317463 = 3476195) B3476195
theorem B1858711 : Blo 1028606 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B2088139 : Blo 1028606 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B4185395 : Blo 1028606 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B2317643 : Blo 1028606 2317643 := bstep (se 1 (by rfl) ⟨1738232, by rfl⟩ : syracuseStep 2317643 = 3476465) B3476465
theorem B1858891 : Blo 1028606 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B2317697 : Blo 1028606 2317697 := bstep (se 2 (by rfl) ⟨869136, by rfl⟩ : syracuseStep 2317697 = 1738273) B1738273
theorem B1957259 : Blo 1028606 1957259 := bstep (se 1 (by rfl) ⟨1467944, by rfl⟩ : syracuseStep 1957259 = 2935889) B2935889
theorem B8347171 : Blo 1028606 8347171 := bstep (se 1 (by rfl) ⟨6260378, by rfl⟩ : syracuseStep 8347171 = 12520757) B12520757
theorem B1957441 : Blo 1028606 1957441 := bstep (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) B1468081
theorem B2317913 : Blo 1028606 2317913 := bstep (se 2 (by rfl) ⟨869217, by rfl⟩ : syracuseStep 2317913 = 1738435) B1738435
theorem B2121331 : Blo 1028606 2121331 := bstep (se 1 (by rfl) ⟨1590998, by rfl⟩ : syracuseStep 2121331 = 3181997) B3181997
theorem B2318003 : Blo 1028606 2318003 := bstep (se 1 (by rfl) ⟨1738502, by rfl⟩ : syracuseStep 2318003 = 3477005) B3477005
theorem B2318039 : Blo 1028606 2318039 := bstep (se 1 (by rfl) ⟨1738529, by rfl⟩ : syracuseStep 2318039 = 3477059) B3477059
theorem B2318219 : Blo 1028606 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B1957783 : Blo 1028606 1957783 := bstep (se 1 (by rfl) ⟨1468337, by rfl⟩ : syracuseStep 1957783 = 2936675) B2936675
theorem B2318273 : Blo 1028606 2318273 := bstep (se 2 (by rfl) ⟨869352, by rfl⟩ : syracuseStep 2318273 = 1738705) B1738705
theorem B1302475 : Blo 1028606 1302475 := bstep (se 1 (by rfl) ⟨976856, by rfl⟩ : syracuseStep 1302475 = 1953713) B1953713
theorem B3301337 : Blo 1028606 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B4186073 : Blo 1028606 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B2613323 : Blo 1028606 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1237079 : Blo 1028606 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B1958003 : Blo 1028606 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1859699 : Blo 1028606 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B2318489 : Blo 1028606 2318489 := bstep (se 2 (by rfl) ⟨869433, by rfl⟩ : syracuseStep 2318489 = 1738867) B1738867
theorem B1302743 : Blo 1028606 1302743 := bstep (se 1 (by rfl) ⟨977057, by rfl⟩ : syracuseStep 1302743 = 1954115) B1954115
theorem B2318579 : Blo 1028606 2318579 := bstep (se 1 (by rfl) ⟨1738934, by rfl⟩ : syracuseStep 2318579 = 3477869) B3477869
theorem B2318615 : Blo 1028606 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B1958231 : Blo 1028606 1958231 := bstep (se 1 (by rfl) ⟨1468673, by rfl⟩ : syracuseStep 1958231 = 2937347) B2937347
theorem B2318795 : Blo 1028606 2318795 := bstep (se 1 (by rfl) ⟨1739096, by rfl⟩ : syracuseStep 2318795 = 3478193) B3478193
theorem B1466839 : Blo 1028606 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B2318849 : Blo 1028606 2318849 := bstep (se 2 (by rfl) ⟨869568, by rfl⟩ : syracuseStep 2318849 = 1739137) B1739137
theorem B1958489 : Blo 1028606 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B1860275 : Blo 1028606 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B2319065 : Blo 1028606 2319065 := bstep (se 2 (by rfl) ⟨869649, by rfl⟩ : syracuseStep 2319065 = 1739299) B1739299
theorem B1237771 : Blo 1028606 1237771 := bstep (se 1 (by rfl) ⟨928328, by rfl⟩ : syracuseStep 1237771 = 1856657) B1856657
theorem B2319155 : Blo 1028606 2319155 := bstep (se 1 (by rfl) ⟨1739366, by rfl⟩ : syracuseStep 2319155 = 3478733) B3478733
theorem B2319191 : Blo 1028606 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B1303447 : Blo 1028606 1303447 := bstep (se 1 (by rfl) ⟨977585, by rfl⟩ : syracuseStep 1303447 = 1955171) B1955171
theorem B8479667 : Blo 1028606 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B1958899 : Blo 1028606 1958899 := bstep (se 1 (by rfl) ⟨1469174, by rfl⟩ : syracuseStep 1958899 = 2938349) B2938349
theorem B2319371 : Blo 1028606 2319371 := bstep (se 1 (by rfl) ⟨1739528, by rfl⟩ : syracuseStep 2319371 = 3479057) B3479057
theorem B2319425 : Blo 1028606 2319425 := bstep (se 2 (by rfl) ⟨869784, by rfl⟩ : syracuseStep 2319425 = 1739569) B1739569
theorem B5858405 : Blo 1028606 5858405 := bstep (se 4 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 5858405 = 1098451) B1098451
theorem B5563523 : Blo 1028606 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B2352331 : Blo 1028606 2352331 := bstep (se 1 (by rfl) ⟨1764248, by rfl⟩ : syracuseStep 2352331 = 3528497) B3528497
theorem B1762519 : Blo 1028606 1762519 := bstep (se 1 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 1762519 = 2643779) B2643779
theorem B2319641 : Blo 1028606 2319641 := bstep (se 2 (by rfl) ⟨869865, by rfl⟩ : syracuseStep 2319641 = 1739731) B1739731
theorem B2319731 : Blo 1028606 2319731 := bstep (se 1 (by rfl) ⟨1739798, by rfl⟩ : syracuseStep 2319731 = 3479597) B3479597
theorem B2319767 : Blo 1028606 2319767 := bstep (se 1 (by rfl) ⟨1739825, by rfl⟩ : syracuseStep 2319767 = 3479651) B3479651
theorem B3302849 : Blo 1028606 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B1959385 : Blo 1028606 1959385 := bstep (se 2 (by rfl) ⟨734769, by rfl⟩ : syracuseStep 1959385 = 1469539) B1469539
theorem B2319947 : Blo 1028606 2319947 := bstep (se 1 (by rfl) ⟨1739960, by rfl⟩ : syracuseStep 2319947 = 3479921) B3479921
theorem B2320001 : Blo 1028606 2320001 := bstep (se 2 (by rfl) ⟨870000, by rfl⟩ : syracuseStep 2320001 = 1740001) B1740001
theorem B2320217 : Blo 1028606 2320217 := bstep (se 2 (by rfl) ⟨870081, by rfl⟩ : syracuseStep 2320217 = 1740163) B1740163
theorem B2353025 : Blo 1028606 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B2320307 : Blo 1028606 2320307 := bstep (se 1 (by rfl) ⟨1740230, by rfl⟩ : syracuseStep 2320307 = 3480461) B3480461
theorem B3139507 : Blo 1028606 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B1238987 : Blo 1028606 1238987 := bstep (se 1 (by rfl) ⟨929240, by rfl⟩ : syracuseStep 1238987 = 1858481) B1858481
theorem B2320343 : Blo 1028606 2320343 := bstep (se 1 (by rfl) ⟨1740257, by rfl⟩ : syracuseStep 2320343 = 3480515) B3480515
theorem B1959947 : Blo 1028606 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B2320523 : Blo 1028606 2320523 := bstep (se 1 (by rfl) ⟨1740392, by rfl⟩ : syracuseStep 2320523 = 3480785) B3480785
theorem B2320577 : Blo 1028606 2320577 := bstep (se 2 (by rfl) ⟨870216, by rfl⟩ : syracuseStep 2320577 = 1740433) B1740433
theorem B1960129 : Blo 1028606 1960129 := bstep (se 2 (by rfl) ⟨735048, by rfl⟩ : syracuseStep 1960129 = 1470097) B1470097
theorem B1173739 : Blo 1028606 1173739 := bstep (se 1 (by rfl) ⟨880304, by rfl⟩ : syracuseStep 1173739 = 1760609) B1760609
theorem B9890093 : Blo 1028606 9890093 := bstep (se 3 (by rfl) ⟨1854392, by rfl⟩ : syracuseStep 9890093 = 3708785) B3708785
theorem B2320793 : Blo 1028606 2320793 := bstep (se 2 (by rfl) ⟨870297, by rfl⟩ : syracuseStep 2320793 = 1740595) B1740595
theorem B11725235 : Blo 1028606 11725235 := bstep (se 1 (by rfl) ⟨8793926, by rfl⟩ : syracuseStep 11725235 = 17587853) B17587853
theorem B2320883 : Blo 1028606 2320883 := bstep (se 1 (by rfl) ⟨1740662, by rfl⟩ : syracuseStep 2320883 = 3481325) B3481325
theorem B2320919 : Blo 1028606 2320919 := bstep (se 1 (by rfl) ⟨1740689, by rfl⟩ : syracuseStep 2320919 = 3481379) B3481379
theorem B1305163 : Blo 1028606 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B2321099 : Blo 1028606 2321099 := bstep (se 1 (by rfl) ⟨1740824, by rfl⟩ : syracuseStep 2321099 = 3481649) B3481649
theorem B2321153 : Blo 1028606 2321153 := bstep (se 2 (by rfl) ⟨870432, by rfl⟩ : syracuseStep 2321153 = 1740865) B1740865
theorem B1043275 : Blo 1028606 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B2321369 : Blo 1028606 2321369 := bstep (se 2 (by rfl) ⟨870513, by rfl⟩ : syracuseStep 2321369 = 1741027) B1741027
theorem B44559395 : Blo 1028606 44559395 := bstep (se 1 (by rfl) ⟨33419546, by rfl⟩ : syracuseStep 44559395 = 66839093) B66839093
theorem B2321459 : Blo 1028606 2321459 := bstep (se 1 (by rfl) ⟨1741094, by rfl⟩ : syracuseStep 2321459 = 3482189) B3482189
theorem B6614081 : Blo 1028606 6614081 := bstep (se 2 (by rfl) ⟨2480280, by rfl⟩ : syracuseStep 6614081 = 4960561) B4960561
theorem B2321495 : Blo 1028606 2321495 := bstep (se 1 (by rfl) ⟨1741121, by rfl⟩ : syracuseStep 2321495 = 3482243) B3482243
theorem B2321675 : Blo 1028606 2321675 := bstep (se 1 (by rfl) ⟨1741256, by rfl⟩ : syracuseStep 2321675 = 3482513) B3482513
theorem B2321729 : Blo 1028606 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B2780509 : Blo 1028606 2780509 := bstep (se 3 (by rfl) ⟨521345, by rfl⟩ : syracuseStep 2780509 = 1042691) B1042691
theorem B7433603 : Blo 1028606 7433603 := bstep (se 1 (by rfl) ⟨5575202, by rfl⟩ : syracuseStep 7433603 = 11150405) B11150405
theorem B1306135 : Blo 1028606 1306135 := bstep (se 1 (by rfl) ⟨979601, by rfl⟩ : syracuseStep 1306135 = 1959203) B1959203
theorem B2321945 : Blo 1028606 2321945 := bstep (se 2 (by rfl) ⟨870729, by rfl⟩ : syracuseStep 2321945 = 1741459) B1741459
theorem B3305053 : Blo 1028606 3305053 := bstep (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) B1239395
theorem B2322035 : Blo 1028606 2322035 := bstep (se 1 (by rfl) ⟨1741526, by rfl⟩ : syracuseStep 2322035 = 3483053) B3483053
theorem B2322071 : Blo 1028606 2322071 := bstep (se 1 (by rfl) ⟨1741553, by rfl⟩ : syracuseStep 2322071 = 3483107) B3483107
theorem B2322251 : Blo 1028606 2322251 := bstep (se 1 (by rfl) ⟨1741688, by rfl⟩ : syracuseStep 2322251 = 3483377) B3483377
theorem B11726693 : Blo 1028606 11726693 := bstep (se 4 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 11726693 = 2198755) B2198755
theorem B2322305 : Blo 1028606 2322305 := bstep (se 2 (by rfl) ⟨870864, by rfl⟩ : syracuseStep 2322305 = 1741729) B1741729
theorem B2322521 : Blo 1028606 2322521 := bstep (se 2 (by rfl) ⟨870945, by rfl⟩ : syracuseStep 2322521 = 1741891) B1741891
theorem B11137175 : Blo 1028606 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B2322611 : Blo 1028606 2322611 := bstep (se 1 (by rfl) ⟨1741958, by rfl⟩ : syracuseStep 2322611 = 3483917) B3483917
theorem B2322647 : Blo 1028606 2322647 := bstep (se 1 (by rfl) ⟨1741985, by rfl⟩ : syracuseStep 2322647 = 3483971) B3483971
theorem B2322827 : Blo 1028606 2322827 := bstep (se 1 (by rfl) ⟨1742120, by rfl⟩ : syracuseStep 2322827 = 3484241) B3484241
theorem B11891123 : Blo 1028606 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B2322881 : Blo 1028606 2322881 := bstep (se 2 (by rfl) ⟨871080, by rfl⟩ : syracuseStep 2322881 = 1742161) B1742161
theorem B2323097 : Blo 1028606 2323097 := bstep (se 2 (by rfl) ⟨871161, by rfl⟩ : syracuseStep 2323097 = 1742323) B1742323
theorem B2323187 : Blo 1028606 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B2323223 : Blo 1028606 2323223 := bstep (se 1 (by rfl) ⟨1742417, by rfl⟩ : syracuseStep 2323223 = 3484835) B3484835
theorem B3961675 : Blo 1028606 3961675 := bstep (se 1 (by rfl) ⟨2971256, by rfl⟩ : syracuseStep 3961675 = 5942513) B5942513
theorem B12547223 : Blo 1028606 12547223 := bstep (se 1 (by rfl) ⟨9410417, by rfl⟩ : syracuseStep 12547223 = 18820835) B18820835
theorem B7435793 : Blo 1028606 7435793 := bstep (se 2 (by rfl) ⟨2788422, by rfl⟩ : syracuseStep 7435793 = 5576845) B5576845
theorem B35682227 : Blo 1028606 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B9402317 : Blo 1028606 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B11303063 : Blo 1028606 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B14842061 : Blo 1028606 14842061 := bstep (se 3 (by rfl) ⟨2782886, by rfl⟩ : syracuseStep 14842061 = 5565773) B5565773
theorem B3471767 : Blo 1028606 3471767 := bstep (se 1 (by rfl) ⟨2603825, by rfl⟩ : syracuseStep 3471767 = 5207651) B5207651
theorem B16087565 : Blo 1028606 16087565 := bstep (se 3 (by rfl) ⟨3016418, by rfl⟩ : syracuseStep 16087565 = 6032837) B6032837
theorem B5864237 : Blo 1028606 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B20380517 : Blo 1028606 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B3472307 : Blo 1028606 3472307 := bstep (se 1 (by rfl) ⟨2604230, by rfl⟩ : syracuseStep 3472307 = 5208461) B5208461
theorem B5569667 : Blo 1028606 5569667 := bstep (se 1 (by rfl) ⟨4177250, by rfl⟩ : syracuseStep 5569667 = 8354501) B8354501
theorem B3472577 : Blo 1028606 3472577 := bstep (se 2 (by rfl) ⟨1302216, by rfl⟩ : syracuseStep 3472577 = 2604433) B2604433
theorem B1735897 : Blo 1028606 1735897 := bstep (se 2 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 1735897 = 1301923) B1301923
theorem B7437869 : Blo 1028606 7437869 := bstep (se 3 (by rfl) ⟨1394600, by rfl⟩ : syracuseStep 7437869 = 2789201) B2789201
theorem B4947587 : Blo 1028606 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B3473117 : Blo 1028606 3473117 := bstep (se 3 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 3473117 = 1302419) B1302419
theorem B1736471 : Blo 1028606 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B1736599 : Blo 1028606 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B3473495 : Blo 1028606 3473495 := bstep (se 1 (by rfl) ⟨2605121, by rfl⟩ : syracuseStep 3473495 = 5210243) B5210243
theorem B3473981 : Blo 1028606 3473981 := bstep (se 3 (by rfl) ⟨651371, by rfl⟩ : syracuseStep 3473981 = 1302743) B1302743
theorem B1737335 : Blo 1028606 1737335 := bstep (se 1 (by rfl) ⟨1303001, by rfl⟩ : syracuseStep 1737335 = 2606003) B2606003
theorem B1737787 : Blo 1028606 1737787 := bstep (se 1 (by rfl) ⟨1303340, by rfl⟩ : syracuseStep 1737787 = 2606681) B2606681
theorem B1737929 : Blo 1028606 1737929 := bstep (se 2 (by rfl) ⟨651723, by rfl⟩ : syracuseStep 1737929 = 1303447) B1303447
theorem B5211539 : Blo 1028606 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B1738631 : Blo 1028606 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B3475385 : Blo 1028606 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B7440407 : Blo 1028606 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B1411387 : Blo 1028606 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B3475979 : Blo 1028606 3475979 := bstep (se 1 (by rfl) ⟨2606984, by rfl⟩ : syracuseStep 3475979 = 5213969) B5213969
theorem B1739279 : Blo 1028606 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B3476087 : Blo 1028606 3476087 := bstep (se 1 (by rfl) ⟨2607065, by rfl⟩ : syracuseStep 3476087 = 5214131) B5214131
theorem B1542971 : Blo 1028606 1542971 := bstep (se 1 (by rfl) ⟨1157228, by rfl⟩ : syracuseStep 1542971 = 2314457) B2314457
theorem B1543031 : Blo 1028606 1543031 := bstep (se 1 (by rfl) ⟨1157273, by rfl⟩ : syracuseStep 1543031 = 2314547) B2314547
theorem B1543055 : Blo 1028606 1543055 := bstep (se 1 (by rfl) ⟨1157291, by rfl⟩ : syracuseStep 1543055 = 2314583) B2314583
theorem B1543097 : Blo 1028606 1543097 := bstep (se 2 (by rfl) ⟨578661, by rfl⟩ : syracuseStep 1543097 = 1157323) B1157323
theorem B6261689 : Blo 1028606 6261689 := bstep (se 2 (by rfl) ⟨2348133, by rfl⟩ : syracuseStep 6261689 = 4696267) B4696267
theorem B1543175 : Blo 1028606 1543175 := bstep (se 1 (by rfl) ⟨1157381, by rfl⟩ : syracuseStep 1543175 = 2314763) B2314763
theorem B1543211 : Blo 1028606 1543211 := bstep (se 1 (by rfl) ⟨1157408, by rfl⟩ : syracuseStep 1543211 = 2314817) B2314817
theorem B1739819 : Blo 1028606 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B5868611 : Blo 1028606 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B1543241 : Blo 1028606 1543241 := bstep (se 2 (by rfl) ⟨578715, by rfl⟩ : syracuseStep 1543241 = 1157431) B1157431
theorem B1543355 : Blo 1028606 1543355 := bstep (se 1 (by rfl) ⟨1157516, by rfl⟩ : syracuseStep 1543355 = 2315033) B2315033
theorem B3476681 : Blo 1028606 3476681 := bstep (se 2 (by rfl) ⟨1303755, by rfl⟩ : syracuseStep 3476681 = 2607511) B2607511
theorem B4951277 : Blo 1028606 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B1543415 : Blo 1028606 1543415 := bstep (se 1 (by rfl) ⟨1157561, by rfl⟩ : syracuseStep 1543415 = 2315123) B2315123
theorem B1543439 : Blo 1028606 1543439 := bstep (se 1 (by rfl) ⟨1157579, by rfl⟩ : syracuseStep 1543439 = 2315159) B2315159
theorem B1543481 : Blo 1028606 1543481 := bstep (se 2 (by rfl) ⟨578805, by rfl⟩ : syracuseStep 1543481 = 1157611) B1157611
theorem B1543559 : Blo 1028606 1543559 := bstep (se 1 (by rfl) ⟨1157669, by rfl⟩ : syracuseStep 1543559 = 2315339) B2315339
theorem B1543595 : Blo 1028606 1543595 := bstep (se 1 (by rfl) ⟨1157696, by rfl⟩ : syracuseStep 1543595 = 2315393) B2315393
theorem B1740217 : Blo 1028606 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B1543625 : Blo 1028606 1543625 := bstep (se 2 (by rfl) ⟨578859, by rfl⟩ : syracuseStep 1543625 = 1157719) B1157719
theorem B4951505 : Blo 1028606 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B1543739 : Blo 1028606 1543739 := bstep (se 1 (by rfl) ⟨1157804, by rfl⟩ : syracuseStep 1543739 = 2315609) B2315609
theorem B22285925 : Blo 1028606 22285925 := bstep (se 4 (by rfl) ⟨2089305, by rfl⟩ : syracuseStep 22285925 = 4178611) B4178611
theorem B1543799 : Blo 1028606 1543799 := bstep (se 1 (by rfl) ⟨1157849, by rfl⟩ : syracuseStep 1543799 = 2315699) B2315699
theorem B1543823 : Blo 1028606 1543823 := bstep (se 1 (by rfl) ⟨1157867, by rfl⟩ : syracuseStep 1543823 = 2315735) B2315735
theorem B1543865 : Blo 1028606 1543865 := bstep (se 2 (by rfl) ⟨578949, by rfl⟩ : syracuseStep 1543865 = 1157899) B1157899
theorem B1543943 : Blo 1028606 1543943 := bstep (se 1 (by rfl) ⟨1157957, by rfl⟩ : syracuseStep 1543943 = 2315915) B2315915
theorem B1543979 : Blo 1028606 1543979 := bstep (se 1 (by rfl) ⟨1157984, by rfl⟩ : syracuseStep 1543979 = 2315969) B2315969
theorem B7442225 : Blo 1028606 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B1544009 : Blo 1028606 1544009 := bstep (se 2 (by rfl) ⟨579003, by rfl⟩ : syracuseStep 1544009 = 1158007) B1158007
theorem B3477383 : Blo 1028606 3477383 := bstep (se 1 (by rfl) ⟨2608037, by rfl⟩ : syracuseStep 3477383 = 5216075) B5216075
theorem B1544123 : Blo 1028606 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B1544183 : Blo 1028606 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B1544207 : Blo 1028606 1544207 := bstep (se 1 (by rfl) ⟨1158155, by rfl⟩ : syracuseStep 1544207 = 2316311) B2316311
theorem B1544249 : Blo 1028606 1544249 := bstep (se 2 (by rfl) ⟨579093, by rfl⟩ : syracuseStep 1544249 = 1158187) B1158187
theorem B1740919 : Blo 1028606 1740919 := bstep (se 1 (by rfl) ⟨1305689, by rfl⟩ : syracuseStep 1740919 = 2611379) B2611379
theorem B1544327 : Blo 1028606 1544327 := bstep (se 1 (by rfl) ⟨1158245, by rfl⟩ : syracuseStep 1544327 = 2316491) B2316491
theorem B1544363 : Blo 1028606 1544363 := bstep (se 1 (by rfl) ⟨1158272, by rfl⟩ : syracuseStep 1544363 = 2316545) B2316545
theorem B1544393 : Blo 1028606 1544393 := bstep (se 2 (by rfl) ⟨579147, by rfl⟩ : syracuseStep 1544393 = 1158295) B1158295
theorem B3477761 : Blo 1028606 3477761 := bstep (se 2 (by rfl) ⟨1304160, by rfl⟩ : syracuseStep 3477761 = 2608321) B2608321
theorem B4395323 : Blo 1028606 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B1544507 : Blo 1028606 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B1741115 : Blo 1028606 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B1544567 : Blo 1028606 1544567 := bstep (se 1 (by rfl) ⟨1158425, by rfl⟩ : syracuseStep 1544567 = 2316851) B2316851
theorem B1544591 : Blo 1028606 1544591 := bstep (se 1 (by rfl) ⟨1158443, by rfl⟩ : syracuseStep 1544591 = 2316887) B2316887
theorem B11735441 : Blo 1028606 11735441 := bstep (se 2 (by rfl) ⟨4400790, by rfl⟩ : syracuseStep 11735441 = 8801581) B8801581
theorem B5214617 : Blo 1028606 5214617 := bstep (se 2 (by rfl) ⟨1955481, by rfl⟩ : syracuseStep 5214617 = 3910963) B3910963
theorem B1544633 : Blo 1028606 1544633 := bstep (se 2 (by rfl) ⟨579237, by rfl⟩ : syracuseStep 1544633 = 1158475) B1158475
theorem B3707345 : Blo 1028606 3707345 := bstep (se 2 (by rfl) ⟨1390254, by rfl⟩ : syracuseStep 3707345 = 2780509) B2780509
theorem B1544711 : Blo 1028606 1544711 := bstep (se 1 (by rfl) ⟨1158533, by rfl⟩ : syracuseStep 1544711 = 2317067) B2317067
theorem B1544747 : Blo 1028606 1544747 := bstep (se 1 (by rfl) ⟨1158560, by rfl⟩ : syracuseStep 1544747 = 2317121) B2317121
theorem B1544777 : Blo 1028606 1544777 := bstep (se 2 (by rfl) ⟨579291, by rfl⟩ : syracuseStep 1544777 = 1158583) B1158583
theorem B1544891 : Blo 1028606 1544891 := bstep (se 1 (by rfl) ⟨1158668, by rfl⟩ : syracuseStep 1544891 = 2317337) B2317337
theorem B1741513 : Blo 1028606 1741513 := bstep (se 2 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 1741513 = 1306135) B1306135
theorem B1544951 : Blo 1028606 1544951 := bstep (se 1 (by rfl) ⟨1158713, by rfl⟩ : syracuseStep 1544951 = 2317427) B2317427
theorem B1544975 : Blo 1028606 1544975 := bstep (se 1 (by rfl) ⟨1158731, by rfl⟩ : syracuseStep 1544975 = 2317463) B2317463
theorem B1545017 : Blo 1028606 1545017 := bstep (se 2 (by rfl) ⟨579381, by rfl⟩ : syracuseStep 1545017 = 1158763) B1158763
theorem B2790263 : Blo 1028606 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B1545095 : Blo 1028606 1545095 := bstep (se 1 (by rfl) ⟨1158821, by rfl⟩ : syracuseStep 1545095 = 2317643) B2317643
theorem B1545131 : Blo 1028606 1545131 := bstep (se 1 (by rfl) ⟨1158848, by rfl⟩ : syracuseStep 1545131 = 2317697) B2317697
theorem B1545161 : Blo 1028606 1545161 := bstep (se 2 (by rfl) ⟨579435, by rfl⟩ : syracuseStep 1545161 = 1158871) B1158871
theorem B2823179 : Blo 1028606 2823179 := bstep (se 1 (by rfl) ⟨2117384, by rfl⟩ : syracuseStep 2823179 = 4234769) B4234769
theorem B3478571 : Blo 1028606 3478571 := bstep (se 1 (by rfl) ⟨2608928, by rfl⟩ : syracuseStep 3478571 = 5217857) B5217857
theorem B1545275 : Blo 1028606 1545275 := bstep (se 1 (by rfl) ⟨1158956, by rfl⟩ : syracuseStep 1545275 = 2317913) B2317913
theorem B1545335 : Blo 1028606 1545335 := bstep (se 1 (by rfl) ⟨1159001, by rfl⟩ : syracuseStep 1545335 = 2318003) B2318003
theorem B1545359 : Blo 1028606 1545359 := bstep (se 1 (by rfl) ⟨1159019, by rfl⟩ : syracuseStep 1545359 = 2318039) B2318039
theorem B1545401 : Blo 1028606 1545401 := bstep (se 2 (by rfl) ⟨579525, by rfl⟩ : syracuseStep 1545401 = 1159051) B1159051
theorem B1545479 : Blo 1028606 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B1545515 : Blo 1028606 1545515 := bstep (se 1 (by rfl) ⟨1159136, by rfl⟩ : syracuseStep 1545515 = 2318273) B2318273
theorem B2790715 : Blo 1028606 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B1545545 : Blo 1028606 1545545 := bstep (se 2 (by rfl) ⟨579579, by rfl⟩ : syracuseStep 1545545 = 1159159) B1159159
theorem B1742215 : Blo 1028606 1742215 := bstep (se 1 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 1742215 = 2613323) B2613323
theorem B5871001 : Blo 1028606 5871001 := bstep (se 2 (by rfl) ⟨2201625, by rfl⟩ : syracuseStep 5871001 = 4403251) B4403251
theorem B1545659 : Blo 1028606 1545659 := bstep (se 1 (by rfl) ⟨1159244, by rfl⟩ : syracuseStep 1545659 = 2318489) B2318489
theorem B1545719 : Blo 1028606 1545719 := bstep (se 1 (by rfl) ⟨1159289, by rfl⟩ : syracuseStep 1545719 = 2318579) B2318579
theorem B1545743 : Blo 1028606 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B1545785 : Blo 1028606 1545785 := bstep (se 2 (by rfl) ⟨579669, by rfl⟩ : syracuseStep 1545785 = 1159339) B1159339
theorem B25073221 : Blo 1028606 25073221 := bstep (se 4 (by rfl) ⟨2350614, by rfl⟩ : syracuseStep 25073221 = 4701229) B4701229
theorem B1545863 : Blo 1028606 1545863 := bstep (se 1 (by rfl) ⟨1159397, by rfl⟩ : syracuseStep 1545863 = 2318795) B2318795
theorem B1545899 : Blo 1028606 1545899 := bstep (se 1 (by rfl) ⟨1159424, by rfl⟩ : syracuseStep 1545899 = 2318849) B2318849
theorem B1545929 : Blo 1028606 1545929 := bstep (se 2 (by rfl) ⟨579723, by rfl⟩ : syracuseStep 1545929 = 1159447) B1159447
theorem B4953889 : Blo 1028606 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B1546043 : Blo 1028606 1546043 := bstep (se 1 (by rfl) ⟨1159532, by rfl⟩ : syracuseStep 1546043 = 2319065) B2319065
theorem B1546103 : Blo 1028606 1546103 := bstep (se 1 (by rfl) ⟨1159577, by rfl⟩ : syracuseStep 1546103 = 2319155) B2319155
theorem B1546127 : Blo 1028606 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B1546169 : Blo 1028606 1546169 := bstep (se 2 (by rfl) ⟨579813, by rfl⟩ : syracuseStep 1546169 = 1159627) B1159627
theorem B5085149 : Blo 1028606 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B1546247 : Blo 1028606 1546247 := bstep (se 1 (by rfl) ⟨1159685, by rfl⟩ : syracuseStep 1546247 = 2319371) B2319371
theorem B1546283 : Blo 1028606 1546283 := bstep (se 1 (by rfl) ⟨1159712, by rfl⟩ : syracuseStep 1546283 = 2319425) B2319425
theorem B3905603 : Blo 1028606 3905603 := bstep (se 1 (by rfl) ⟨2929202, by rfl⟩ : syracuseStep 3905603 = 5858405) B5858405
theorem B1546313 : Blo 1028606 1546313 := bstep (se 2 (by rfl) ⟨579867, by rfl⟩ : syracuseStep 1546313 = 1159735) B1159735
theorem B1546427 : Blo 1028606 1546427 := bstep (se 1 (by rfl) ⟨1159820, by rfl⟩ : syracuseStep 1546427 = 2319641) B2319641
theorem B1546487 : Blo 1028606 1546487 := bstep (se 1 (by rfl) ⟨1159865, by rfl⟩ : syracuseStep 1546487 = 2319731) B2319731
theorem B1546511 : Blo 1028606 1546511 := bstep (se 1 (by rfl) ⟨1159883, by rfl⟩ : syracuseStep 1546511 = 2319767) B2319767
theorem B2201899 : Blo 1028606 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B1546553 : Blo 1028606 1546553 := bstep (se 2 (by rfl) ⟨579957, by rfl⟩ : syracuseStep 1546553 = 1159915) B1159915
theorem B3479867 : Blo 1028606 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B1546631 : Blo 1028606 1546631 := bstep (se 1 (by rfl) ⟨1159973, by rfl⟩ : syracuseStep 1546631 = 2319947) B2319947
theorem B1546667 : Blo 1028606 1546667 := bstep (se 1 (by rfl) ⟨1160000, by rfl⟩ : syracuseStep 1546667 = 2320001) B2320001
theorem B5282233 : Blo 1028606 5282233 := bstep (se 2 (by rfl) ⟨1980837, by rfl⟩ : syracuseStep 5282233 = 3961675) B3961675
theorem B1546697 : Blo 1028606 1546697 := bstep (se 2 (by rfl) ⟨580011, by rfl⟩ : syracuseStep 1546697 = 1160023) B1160023
theorem B1546811 : Blo 1028606 1546811 := bstep (se 1 (by rfl) ⟨1160108, by rfl⟩ : syracuseStep 1546811 = 2320217) B2320217
theorem B1546871 : Blo 1028606 1546871 := bstep (se 1 (by rfl) ⟨1160153, by rfl⟩ : syracuseStep 1546871 = 2320307) B2320307
theorem B1546895 : Blo 1028606 1546895 := bstep (se 1 (by rfl) ⟨1160171, by rfl⟩ : syracuseStep 1546895 = 2320343) B2320343
theorem B1546937 : Blo 1028606 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B1547015 : Blo 1028606 1547015 := bstep (se 1 (by rfl) ⟨1160261, by rfl⟩ : syracuseStep 1547015 = 2320523) B2320523
theorem B3480353 : Blo 1028606 3480353 := bstep (se 2 (by rfl) ⟨1305132, by rfl⟩ : syracuseStep 3480353 = 2610265) B2610265
theorem B1547051 : Blo 1028606 1547051 := bstep (se 1 (by rfl) ⟨1160288, by rfl⟩ : syracuseStep 1547051 = 2320577) B2320577
theorem B1547081 : Blo 1028606 1547081 := bstep (se 2 (by rfl) ⟨580155, by rfl⟩ : syracuseStep 1547081 = 1160311) B1160311
theorem B11279179 : Blo 1028606 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B6593395 : Blo 1028606 6593395 := bstep (se 1 (by rfl) ⟨4945046, by rfl⟩ : syracuseStep 6593395 = 9890093) B9890093
theorem B5217209 : Blo 1028606 5217209 := bstep (se 2 (by rfl) ⟨1956453, by rfl⟩ : syracuseStep 5217209 = 3912907) B3912907
theorem B1547195 : Blo 1028606 1547195 := bstep (se 1 (by rfl) ⟨1160396, by rfl⟩ : syracuseStep 1547195 = 2320793) B2320793
theorem B1547255 : Blo 1028606 1547255 := bstep (se 1 (by rfl) ⟨1160441, by rfl⟩ : syracuseStep 1547255 = 2320883) B2320883
theorem B1547279 : Blo 1028606 1547279 := bstep (se 1 (by rfl) ⟨1160459, by rfl⟩ : syracuseStep 1547279 = 2320919) B2320919
theorem B3906589 : Blo 1028606 3906589 := bstep (se 3 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 3906589 = 1464971) B1464971
theorem B1547321 : Blo 1028606 1547321 := bstep (se 2 (by rfl) ⟨580245, by rfl⟩ : syracuseStep 1547321 = 1160491) B1160491
theorem B1547399 : Blo 1028606 1547399 := bstep (se 1 (by rfl) ⟨1160549, by rfl⟩ : syracuseStep 1547399 = 2321099) B2321099
theorem B1547435 : Blo 1028606 1547435 := bstep (se 1 (by rfl) ⟨1160576, by rfl⟩ : syracuseStep 1547435 = 2321153) B2321153
theorem B1547465 : Blo 1028606 1547465 := bstep (se 2 (by rfl) ⟨580299, by rfl⟩ : syracuseStep 1547465 = 1160599) B1160599
theorem B5577929 : Blo 1028606 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B11738357 : Blo 1028606 11738357 := bstep (se 5 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 11738357 = 1100471) B1100471
theorem B1547579 : Blo 1028606 1547579 := bstep (se 1 (by rfl) ⟨1160684, by rfl⟩ : syracuseStep 1547579 = 2321369) B2321369
theorem B5872985 : Blo 1028606 5872985 := bstep (se 2 (by rfl) ⟨2202369, by rfl⟩ : syracuseStep 5872985 = 4404739) B4404739
theorem B3480947 : Blo 1028606 3480947 := bstep (se 1 (by rfl) ⟨2610710, by rfl⟩ : syracuseStep 3480947 = 5221421) B5221421
theorem B1547639 : Blo 1028606 1547639 := bstep (se 1 (by rfl) ⟨1160729, by rfl⟩ : syracuseStep 1547639 = 2321459) B2321459
theorem B1547663 : Blo 1028606 1547663 := bstep (se 1 (by rfl) ⟨1160747, by rfl⟩ : syracuseStep 1547663 = 2321495) B2321495
theorem B1547705 : Blo 1028606 1547705 := bstep (se 2 (by rfl) ⟨580389, by rfl⟩ : syracuseStep 1547705 = 1160779) B1160779
theorem B1547783 : Blo 1028606 1547783 := bstep (se 1 (by rfl) ⟨1160837, by rfl⟩ : syracuseStep 1547783 = 2321675) B2321675
theorem B1547819 : Blo 1028606 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B1547849 : Blo 1028606 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B4955735 : Blo 1028606 4955735 := bstep (se 1 (by rfl) ⟨3716801, by rfl⟩ : syracuseStep 4955735 = 7433603) B7433603
theorem B1547963 : Blo 1028606 1547963 := bstep (se 1 (by rfl) ⟨1160972, by rfl⟩ : syracuseStep 1547963 = 2321945) B2321945
theorem B10591973 : Blo 1028606 10591973 := bstep (se 4 (by rfl) ⟨992997, by rfl⟩ : syracuseStep 10591973 = 1985995) B1985995
theorem B1548023 : Blo 1028606 1548023 := bstep (se 1 (by rfl) ⟨1161017, by rfl⟩ : syracuseStep 1548023 = 2322035) B2322035
theorem B1548047 : Blo 1028606 1548047 := bstep (se 1 (by rfl) ⟨1161035, by rfl⟩ : syracuseStep 1548047 = 2322071) B2322071
theorem B1548089 : Blo 1028606 1548089 := bstep (se 2 (by rfl) ⟨580533, by rfl⟩ : syracuseStep 1548089 = 1161067) B1161067
theorem B1548167 : Blo 1028606 1548167 := bstep (se 1 (by rfl) ⟨1161125, by rfl⟩ : syracuseStep 1548167 = 2322251) B2322251
theorem B1548203 : Blo 1028606 1548203 := bstep (se 1 (by rfl) ⟨1161152, by rfl⟩ : syracuseStep 1548203 = 2322305) B2322305
theorem B1548233 : Blo 1028606 1548233 := bstep (se 2 (by rfl) ⟨580587, by rfl⟩ : syracuseStep 1548233 = 1161175) B1161175
theorem B7938071 : Blo 1028606 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B1548347 : Blo 1028606 1548347 := bstep (se 1 (by rfl) ⟨1161260, by rfl⟩ : syracuseStep 1548347 = 2322521) B2322521
theorem B1548407 : Blo 1028606 1548407 := bstep (se 1 (by rfl) ⟨1161305, by rfl⟩ : syracuseStep 1548407 = 2322611) B2322611
theorem B1548431 : Blo 1028606 1548431 := bstep (se 1 (by rfl) ⟨1161323, by rfl⟩ : syracuseStep 1548431 = 2322647) B2322647
theorem B1548473 : Blo 1028606 1548473 := bstep (se 2 (by rfl) ⟨580677, by rfl⟩ : syracuseStep 1548473 = 1161355) B1161355
theorem B5218505 : Blo 1028606 5218505 := bstep (se 2 (by rfl) ⟨1956939, by rfl⟩ : syracuseStep 5218505 = 3913879) B3913879
theorem B1548551 : Blo 1028606 1548551 := bstep (se 1 (by rfl) ⟨1161413, by rfl⟩ : syracuseStep 1548551 = 2322827) B2322827
theorem B1548587 : Blo 1028606 1548587 := bstep (se 1 (by rfl) ⟨1161440, by rfl⟩ : syracuseStep 1548587 = 2322881) B2322881
theorem B1548617 : Blo 1028606 1548617 := bstep (se 2 (by rfl) ⟨580731, by rfl⟩ : syracuseStep 1548617 = 1161463) B1161463
theorem B1548731 : Blo 1028606 1548731 := bstep (se 1 (by rfl) ⟨1161548, by rfl⟩ : syracuseStep 1548731 = 2323097) B2323097
theorem B1548791 : Blo 1028606 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B1548815 : Blo 1028606 1548815 := bstep (se 1 (by rfl) ⟨1161611, by rfl⟩ : syracuseStep 1548815 = 2323223) B2323223
theorem B1548857 : Blo 1028606 1548857 := bstep (se 2 (by rfl) ⟨580821, by rfl⟩ : syracuseStep 1548857 = 1161643) B1161643
theorem B8364815 : Blo 1028606 8364815 := bstep (se 1 (by rfl) ⟨6273611, by rfl⟩ : syracuseStep 8364815 = 12547223) B12547223
theorem B4957195 : Blo 1028606 4957195 := bstep (se 1 (by rfl) ⟨3717896, by rfl⟩ : syracuseStep 4957195 = 7435793) B7435793
theorem B4400365 : Blo 1028606 4400365 := bstep (se 3 (by rfl) ⟨825068, by rfl⟩ : syracuseStep 4400365 = 1650137) B1650137
theorem B6268211 : Blo 1028606 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B10725043 : Blo 1028606 10725043 := bstep (se 1 (by rfl) ⟨8043782, by rfl⟩ : syracuseStep 10725043 = 16087565) B16087565
theorem B3909491 : Blo 1028606 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B26388341 : Blo 1028606 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B3483539 : Blo 1028606 3483539 := bstep (se 1 (by rfl) ⟨2612654, by rfl⟩ : syracuseStep 3483539 = 5225309) B5225309
theorem B3713111 : Blo 1028606 3713111 := bstep (se 1 (by rfl) ⟨2784833, by rfl⟩ : syracuseStep 3713111 = 5569667) B5569667
theorem B1648759 : Blo 1028606 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B2828441 : Blo 1028606 2828441 := bstep (se 2 (by rfl) ⟨1060665, by rfl⟩ : syracuseStep 2828441 = 2121331) B2121331
theorem B1648939 : Blo 1028606 1648939 := bstep (se 1 (by rfl) ⟨1236704, by rfl⟩ : syracuseStep 1648939 = 2473409) B2473409
theorem B4958579 : Blo 1028606 4958579 := bstep (se 1 (by rfl) ⟨3718934, by rfl⟩ : syracuseStep 4958579 = 7437869) B7437869
theorem B1157647 : Blo 1028606 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B8792833 : Blo 1028606 8792833 := bstep (se 2 (by rfl) ⟨3297312, by rfl⟩ : syracuseStep 8792833 = 6594625) B6594625
theorem B5647313 : Blo 1028606 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1158151 : Blo 1028606 1158151 := bstep (se 1 (by rfl) ⟨868613, by rfl⟩ : syracuseStep 1158151 = 1737227) B1737227
theorem B4402295 : Blo 1028606 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B1158331 : Blo 1028606 1158331 := bstep (se 1 (by rfl) ⟨868748, by rfl⟩ : syracuseStep 1158331 = 1737497) B1737497
theorem B3484943 : Blo 1028606 3484943 := bstep (se 1 (by rfl) ⟨2613707, by rfl⟩ : syracuseStep 3484943 = 5227415) B5227415
theorem B5877107 : Blo 1028606 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B1158799 : Blo 1028606 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B3911723 : Blo 1028606 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B3715159 : Blo 1028606 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B1159303 : Blo 1028606 1159303 := bstep (se 1 (by rfl) ⟨869477, by rfl⟩ : syracuseStep 1159303 = 1738955) B1738955
theorem B1159483 : Blo 1028606 1159483 := bstep (se 1 (by rfl) ⟨869612, by rfl⟩ : syracuseStep 1159483 = 1739225) B1739225
theorem B1651079 : Blo 1028606 1651079 := bstep (se 1 (by rfl) ⟨1238309, by rfl⟩ : syracuseStep 1651079 = 2476619) B2476619
theorem B3715463 : Blo 1028606 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B1028615 : Blo 1028606 1028615 := bstep (se 1 (by rfl) ⟨771461, by rfl⟩ : syracuseStep 1028615 = 1542923) B1542923
theorem B1028623 : Blo 1028606 1028623 := bstep (se 1 (by rfl) ⟨771467, by rfl⟩ : syracuseStep 1028623 = 1542935) B1542935
theorem B1323535 : Blo 1028606 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B1028667 : Blo 1028606 1028667 := bstep (se 1 (by rfl) ⟨771500, by rfl⟩ : syracuseStep 1028667 = 1543001) B1543001
theorem B2929213 : Blo 1028606 2929213 := bstep (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) B1098455
theorem B1028743 : Blo 1028606 1028743 := bstep (se 1 (by rfl) ⟨771557, by rfl⟩ : syracuseStep 1028743 = 1543115) B1543115
theorem B1028751 : Blo 1028606 1028751 := bstep (se 1 (by rfl) ⟨771563, by rfl⟩ : syracuseStep 1028751 = 1543127) B1543127
theorem B1028795 : Blo 1028606 1028795 := bstep (se 1 (by rfl) ⟨771596, by rfl⟩ : syracuseStep 1028795 = 1543193) B1543193
theorem B8794817 : Blo 1028606 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B1028871 : Blo 1028606 1028871 := bstep (se 1 (by rfl) ⟨771653, by rfl⟩ : syracuseStep 1028871 = 1543307) B1543307
theorem B1028879 : Blo 1028606 1028879 := bstep (se 1 (by rfl) ⟨771659, by rfl⟩ : syracuseStep 1028879 = 1543319) B1543319
theorem B8925967 : Blo 1028606 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B1159951 : Blo 1028606 1159951 := bstep (se 1 (by rfl) ⟨869963, by rfl⟩ : syracuseStep 1159951 = 1739927) B1739927
theorem B2929441 : Blo 1028606 2929441 := bstep (se 2 (by rfl) ⟨1098540, by rfl⟩ : syracuseStep 2929441 = 2197081) B2197081
theorem B18789155 : Blo 1028606 18789155 := bstep (se 1 (by rfl) ⟨14091866, by rfl⟩ : syracuseStep 18789155 = 28183733) B28183733
theorem B5878565 : Blo 1028606 5878565 := bstep (se 4 (by rfl) ⟨551115, by rfl⟩ : syracuseStep 5878565 = 1102231) B1102231
theorem B1028923 : Blo 1028606 1028923 := bstep (se 1 (by rfl) ⟨771692, by rfl⟩ : syracuseStep 1028923 = 1543385) B1543385
theorem B1028999 : Blo 1028606 1028999 := bstep (se 1 (by rfl) ⟨771749, by rfl⟩ : syracuseStep 1028999 = 1543499) B1543499
theorem B1029007 : Blo 1028606 1029007 := bstep (se 1 (by rfl) ⟨771755, by rfl⟩ : syracuseStep 1029007 = 1543511) B1543511
theorem B1029051 : Blo 1028606 1029051 := bstep (se 1 (by rfl) ⟨771788, by rfl⟩ : syracuseStep 1029051 = 1543577) B1543577
theorem B1029127 : Blo 1028606 1029127 := bstep (se 1 (by rfl) ⟨771845, by rfl⟩ : syracuseStep 1029127 = 1543691) B1543691
theorem B1029135 : Blo 1028606 1029135 := bstep (se 1 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 1029135 = 1543703) B1543703
theorem B1651727 : Blo 1028606 1651727 := bstep (se 1 (by rfl) ⟨1238795, by rfl⟩ : syracuseStep 1651727 = 2477591) B2477591
theorem B5649431 : Blo 1028606 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B1029179 : Blo 1028606 1029179 := bstep (se 1 (by rfl) ⟨771884, by rfl⟩ : syracuseStep 1029179 = 1543769) B1543769
theorem B4174915 : Blo 1028606 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B3519575 : Blo 1028606 3519575 := bstep (se 1 (by rfl) ⟨2639681, by rfl⟩ : syracuseStep 3519575 = 5279363) B5279363
theorem B2929783 : Blo 1028606 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B1029255 : Blo 1028606 1029255 := bstep (se 1 (by rfl) ⟨771941, by rfl⟩ : syracuseStep 1029255 = 1543883) B1543883
theorem B1029263 : Blo 1028606 1029263 := bstep (se 1 (by rfl) ⟨771947, by rfl⟩ : syracuseStep 1029263 = 1543895) B1543895
theorem B1029307 : Blo 1028606 1029307 := bstep (se 1 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 1029307 = 1543961) B1543961
theorem B1029383 : Blo 1028606 1029383 := bstep (se 1 (by rfl) ⟨772037, by rfl⟩ : syracuseStep 1029383 = 1544075) B1544075
theorem B1160455 : Blo 1028606 1160455 := bstep (se 1 (by rfl) ⟨870341, by rfl⟩ : syracuseStep 1160455 = 1740683) B1740683
theorem B1029391 : Blo 1028606 1029391 := bstep (se 1 (by rfl) ⟨772043, by rfl⟩ : syracuseStep 1029391 = 1544087) B1544087
theorem B1029435 : Blo 1028606 1029435 := bstep (se 1 (by rfl) ⟨772076, by rfl⟩ : syracuseStep 1029435 = 1544153) B1544153
theorem B1029511 : Blo 1028606 1029511 := bstep (se 1 (by rfl) ⟨772133, by rfl⟩ : syracuseStep 1029511 = 1544267) B1544267
theorem B1029519 : Blo 1028606 1029519 := bstep (se 1 (by rfl) ⟨772139, by rfl⟩ : syracuseStep 1029519 = 1544279) B1544279
theorem B1029563 : Blo 1028606 1029563 := bstep (se 1 (by rfl) ⟨772172, by rfl⟩ : syracuseStep 1029563 = 1544345) B1544345
theorem B1160635 : Blo 1028606 1160635 := bstep (se 1 (by rfl) ⟨870476, by rfl⟩ : syracuseStep 1160635 = 1740953) B1740953
theorem B5879249 : Blo 1028606 5879249 := bstep (se 2 (by rfl) ⟨2204718, by rfl⟩ : syracuseStep 5879249 = 4409437) B4409437
theorem B1029639 : Blo 1028606 1029639 := bstep (se 1 (by rfl) ⟨772229, by rfl⟩ : syracuseStep 1029639 = 1544459) B1544459
theorem B1029647 : Blo 1028606 1029647 := bstep (se 1 (by rfl) ⟨772235, by rfl⟩ : syracuseStep 1029647 = 1544471) B1544471
theorem B3520043 : Blo 1028606 3520043 := bstep (se 1 (by rfl) ⟨2640032, by rfl⟩ : syracuseStep 3520043 = 5280065) B5280065
theorem B1029691 : Blo 1028606 1029691 := bstep (se 1 (by rfl) ⟨772268, by rfl⟩ : syracuseStep 1029691 = 1544537) B1544537
theorem B1914427 : Blo 1028606 1914427 := bstep (se 1 (by rfl) ⟨1435820, by rfl⟩ : syracuseStep 1914427 = 2871641) B2871641
theorem B1324603 : Blo 1028606 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B1029767 : Blo 1028606 1029767 := bstep (se 1 (by rfl) ⟨772325, by rfl⟩ : syracuseStep 1029767 = 1544651) B1544651
theorem B1029775 : Blo 1028606 1029775 := bstep (se 1 (by rfl) ⟨772331, by rfl⟩ : syracuseStep 1029775 = 1544663) B1544663
theorem B1029819 : Blo 1028606 1029819 := bstep (se 1 (by rfl) ⟨772364, by rfl⟩ : syracuseStep 1029819 = 1544729) B1544729
theorem B1029895 : Blo 1028606 1029895 := bstep (se 1 (by rfl) ⟨772421, by rfl⟩ : syracuseStep 1029895 = 1544843) B1544843
theorem B1029903 : Blo 1028606 1029903 := bstep (se 1 (by rfl) ⟨772427, by rfl⟩ : syracuseStep 1029903 = 1544855) B1544855
theorem B5879567 : Blo 1028606 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B1029947 : Blo 1028606 1029947 := bstep (se 1 (by rfl) ⟨772460, by rfl⟩ : syracuseStep 1029947 = 1544921) B1544921
theorem B1030023 : Blo 1028606 1030023 := bstep (se 1 (by rfl) ⟨772517, by rfl⟩ : syracuseStep 1030023 = 1545035) B1545035
theorem B1030031 : Blo 1028606 1030031 := bstep (se 1 (by rfl) ⟨772523, by rfl⟩ : syracuseStep 1030031 = 1545047) B1545047
theorem B1161103 : Blo 1028606 1161103 := bstep (se 1 (by rfl) ⟨870827, by rfl⟩ : syracuseStep 1161103 = 1741655) B1741655
theorem B5224337 : Blo 1028606 5224337 := bstep (se 2 (by rfl) ⟨1959126, by rfl⟩ : syracuseStep 5224337 = 3918253) B3918253
theorem B1030075 : Blo 1028606 1030075 := bstep (se 1 (by rfl) ⟨772556, by rfl⟩ : syracuseStep 1030075 = 1545113) B1545113
theorem B6272977 : Blo 1028606 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B1030151 : Blo 1028606 1030151 := bstep (se 1 (by rfl) ⟨772613, by rfl⟩ : syracuseStep 1030151 = 1545227) B1545227
theorem B1030159 : Blo 1028606 1030159 := bstep (se 1 (by rfl) ⟨772619, by rfl⟩ : syracuseStep 1030159 = 1545239) B1545239
theorem B34289687 : Blo 1028606 34289687 := bstep (se 1 (by rfl) ⟨25717265, by rfl⟩ : syracuseStep 34289687 = 51434531) B51434531
theorem B2930717 : Blo 1028606 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B1030203 : Blo 1028606 1030203 := bstep (se 1 (by rfl) ⟨772652, by rfl⟩ : syracuseStep 1030203 = 1545305) B1545305
theorem B1030279 : Blo 1028606 1030279 := bstep (se 1 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 1030279 = 1545419) B1545419
theorem B1030287 : Blo 1028606 1030287 := bstep (se 1 (by rfl) ⟨772715, by rfl⟩ : syracuseStep 1030287 = 1545431) B1545431
theorem B1030331 : Blo 1028606 1030331 := bstep (se 1 (by rfl) ⟨772748, by rfl⟩ : syracuseStep 1030331 = 1545497) B1545497
theorem B1030407 : Blo 1028606 1030407 := bstep (se 1 (by rfl) ⟨772805, by rfl⟩ : syracuseStep 1030407 = 1545611) B1545611
theorem B1030415 : Blo 1028606 1030415 := bstep (se 1 (by rfl) ⟨772811, by rfl⟩ : syracuseStep 1030415 = 1545623) B1545623
theorem B1030459 : Blo 1028606 1030459 := bstep (se 1 (by rfl) ⟨772844, by rfl⟩ : syracuseStep 1030459 = 1545689) B1545689
theorem B2931059 : Blo 1028606 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B1030535 : Blo 1028606 1030535 := bstep (se 1 (by rfl) ⟨772901, by rfl⟩ : syracuseStep 1030535 = 1545803) B1545803
theorem B1161607 : Blo 1028606 1161607 := bstep (se 1 (by rfl) ⟨871205, by rfl⟩ : syracuseStep 1161607 = 1742411) B1742411
theorem B1030543 : Blo 1028606 1030543 := bstep (se 1 (by rfl) ⟨772907, by rfl⟩ : syracuseStep 1030543 = 1545815) B1545815
theorem B1391033 : Blo 1028606 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B1030587 : Blo 1028606 1030587 := bstep (se 1 (by rfl) ⟨772940, by rfl⟩ : syracuseStep 1030587 = 1545881) B1545881
theorem B11123203 : Blo 1028606 11123203 := bstep (se 1 (by rfl) ⟨8342402, by rfl⟩ : syracuseStep 11123203 = 16684805) B16684805
theorem B1030663 : Blo 1028606 1030663 := bstep (se 1 (by rfl) ⟨772997, by rfl⟩ : syracuseStep 1030663 = 1545995) B1545995
theorem B1030671 : Blo 1028606 1030671 := bstep (se 1 (by rfl) ⟨773003, by rfl⟩ : syracuseStep 1030671 = 1546007) B1546007
theorem B11123243 : Blo 1028606 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B1030715 : Blo 1028606 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B1653367 : Blo 1028606 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B1030791 : Blo 1028606 1030791 := bstep (se 1 (by rfl) ⟨773093, by rfl⟩ : syracuseStep 1030791 = 1546187) B1546187
theorem B1030799 : Blo 1028606 1030799 := bstep (se 1 (by rfl) ⟨773099, by rfl⟩ : syracuseStep 1030799 = 1546199) B1546199
theorem B2472601 : Blo 1028606 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B1030843 : Blo 1028606 1030843 := bstep (se 1 (by rfl) ⟨773132, by rfl⟩ : syracuseStep 1030843 = 1546265) B1546265
theorem B6601445 : Blo 1028606 6601445 := bstep (se 4 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 6601445 = 1237771) B1237771
theorem B1030919 : Blo 1028606 1030919 := bstep (se 1 (by rfl) ⟨773189, by rfl⟩ : syracuseStep 1030919 = 1546379) B1546379
theorem B1030927 : Blo 1028606 1030927 := bstep (se 1 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 1030927 = 1546391) B1546391
theorem B2931515 : Blo 1028606 2931515 := bstep (se 1 (by rfl) ⟨2198636, by rfl⟩ : syracuseStep 2931515 = 4397273) B4397273
theorem B1030971 : Blo 1028606 1030971 := bstep (se 1 (by rfl) ⟨773228, by rfl⟩ : syracuseStep 1030971 = 1546457) B1546457
theorem B1653623 : Blo 1028606 1653623 := bstep (se 1 (by rfl) ⟨1240217, by rfl⟩ : syracuseStep 1653623 = 2480435) B2480435
theorem B1031047 : Blo 1028606 1031047 := bstep (se 1 (by rfl) ⟨773285, by rfl⟩ : syracuseStep 1031047 = 1546571) B1546571
theorem B1031055 : Blo 1028606 1031055 := bstep (se 1 (by rfl) ⟨773291, by rfl⟩ : syracuseStep 1031055 = 1546583) B1546583
theorem B1031099 : Blo 1028606 1031099 := bstep (se 1 (by rfl) ⟨773324, by rfl⟩ : syracuseStep 1031099 = 1546649) B1546649
theorem B1031175 : Blo 1028606 1031175 := bstep (se 1 (by rfl) ⟨773381, by rfl⟩ : syracuseStep 1031175 = 1546763) B1546763
theorem B1031183 : Blo 1028606 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B8797207 : Blo 1028606 8797207 := bstep (se 1 (by rfl) ⟨6597905, by rfl⟩ : syracuseStep 8797207 = 13195811) B13195811
theorem B1031227 : Blo 1028606 1031227 := bstep (se 1 (by rfl) ⟨773420, by rfl⟩ : syracuseStep 1031227 = 1546841) B1546841
theorem B8928317 : Blo 1028606 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B1031303 : Blo 1028606 1031303 := bstep (se 1 (by rfl) ⟨773477, by rfl⟩ : syracuseStep 1031303 = 1546955) B1546955
theorem B1031311 : Blo 1028606 1031311 := bstep (se 1 (by rfl) ⟨773483, by rfl⟩ : syracuseStep 1031311 = 1546967) B1546967
theorem B1031355 : Blo 1028606 1031355 := bstep (se 1 (by rfl) ⟨773516, by rfl⟩ : syracuseStep 1031355 = 1547033) B1547033
theorem B3718345 : Blo 1028606 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B2473217 : Blo 1028606 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B1031431 : Blo 1028606 1031431 := bstep (se 1 (by rfl) ⟨773573, by rfl⟩ : syracuseStep 1031431 = 1547147) B1547147
theorem B1391887 : Blo 1028606 1391887 := bstep (se 1 (by rfl) ⟨1043915, by rfl⟩ : syracuseStep 1391887 = 2087831) B2087831
theorem B1031439 : Blo 1028606 1031439 := bstep (se 1 (by rfl) ⟨773579, by rfl⟩ : syracuseStep 1031439 = 1547159) B1547159
theorem B1031483 : Blo 1028606 1031483 := bstep (se 1 (by rfl) ⟨773612, by rfl⟩ : syracuseStep 1031483 = 1547225) B1547225
theorem B1031559 : Blo 1028606 1031559 := bstep (se 1 (by rfl) ⟨773669, by rfl⟩ : syracuseStep 1031559 = 1547339) B1547339
theorem B1031567 : Blo 1028606 1031567 := bstep (se 1 (by rfl) ⟨773675, by rfl⟩ : syracuseStep 1031567 = 1547351) B1547351
theorem B3915155 : Blo 1028606 3915155 := bstep (se 1 (by rfl) ⟨2936366, by rfl⟩ : syracuseStep 3915155 = 5872733) B5872733
theorem B1031611 : Blo 1028606 1031611 := bstep (se 1 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 1031611 = 1547417) B1547417
theorem B4406737 : Blo 1028606 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B2604545 : Blo 1028606 2604545 := bstep (se 2 (by rfl) ⟨976704, by rfl⟩ : syracuseStep 2604545 = 1953409) B1953409
theorem B1031687 : Blo 1028606 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B1031695 : Blo 1028606 1031695 := bstep (se 1 (by rfl) ⟨773771, by rfl⟩ : syracuseStep 1031695 = 1547543) B1547543
theorem B1031739 : Blo 1028606 1031739 := bstep (se 1 (by rfl) ⟨773804, by rfl⟩ : syracuseStep 1031739 = 1547609) B1547609
theorem B1031815 : Blo 1028606 1031815 := bstep (se 1 (by rfl) ⟨773861, by rfl⟩ : syracuseStep 1031815 = 1547723) B1547723
theorem B1031823 : Blo 1028606 1031823 := bstep (se 1 (by rfl) ⟨773867, by rfl⟩ : syracuseStep 1031823 = 1547735) B1547735
theorem B1031867 : Blo 1028606 1031867 := bstep (se 1 (by rfl) ⟨773900, by rfl⟩ : syracuseStep 1031867 = 1547801) B1547801
theorem B1031943 : Blo 1028606 1031943 := bstep (se 1 (by rfl) ⟨773957, by rfl⟩ : syracuseStep 1031943 = 1547915) B1547915
theorem B1031951 : Blo 1028606 1031951 := bstep (se 1 (by rfl) ⟨773963, by rfl⟩ : syracuseStep 1031951 = 1547927) B1547927
theorem B1031995 : Blo 1028606 1031995 := bstep (se 1 (by rfl) ⟨773996, by rfl⟩ : syracuseStep 1031995 = 1547993) B1547993
theorem B2604919 : Blo 1028606 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B1032071 : Blo 1028606 1032071 := bstep (se 1 (by rfl) ⟨774053, by rfl⟩ : syracuseStep 1032071 = 1548107) B1548107
theorem B1032079 : Blo 1028606 1032079 := bstep (se 1 (by rfl) ⟨774059, by rfl⟩ : syracuseStep 1032079 = 1548119) B1548119
theorem B1032123 : Blo 1028606 1032123 := bstep (se 1 (by rfl) ⟨774092, by rfl⟩ : syracuseStep 1032123 = 1548185) B1548185
theorem B5226443 : Blo 1028606 5226443 := bstep (se 1 (by rfl) ⟨3919832, by rfl⟩ : syracuseStep 5226443 = 7839665) B7839665
theorem B2473985 : Blo 1028606 2473985 := bstep (se 2 (by rfl) ⟨927744, by rfl⟩ : syracuseStep 2473985 = 1855489) B1855489
theorem B1032199 : Blo 1028606 1032199 := bstep (se 1 (by rfl) ⟨774149, by rfl⟩ : syracuseStep 1032199 = 1548299) B1548299
theorem B1032207 : Blo 1028606 1032207 := bstep (se 1 (by rfl) ⟨774155, by rfl⟩ : syracuseStep 1032207 = 1548311) B1548311
theorem B1032251 : Blo 1028606 1032251 := bstep (se 1 (by rfl) ⟨774188, by rfl⟩ : syracuseStep 1032251 = 1548377) B1548377
theorem B1032327 : Blo 1028606 1032327 := bstep (se 1 (by rfl) ⟨774245, by rfl⟩ : syracuseStep 1032327 = 1548491) B1548491
theorem B1032335 : Blo 1028606 1032335 := bstep (se 1 (by rfl) ⟨774251, by rfl⟩ : syracuseStep 1032335 = 1548503) B1548503
theorem B1032379 : Blo 1028606 1032379 := bstep (se 1 (by rfl) ⟨774284, by rfl⟩ : syracuseStep 1032379 = 1548569) B1548569
theorem B26362097 : Blo 1028606 26362097 := bstep (se 2 (by rfl) ⟨9885786, by rfl⟩ : syracuseStep 26362097 = 19771573) B19771573
theorem B14106869 : Blo 1028606 14106869 := bstep (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) B1322519
theorem B1032455 : Blo 1028606 1032455 := bstep (se 1 (by rfl) ⟨774341, by rfl⟩ : syracuseStep 1032455 = 1548683) B1548683
theorem B5226767 : Blo 1028606 5226767 := bstep (se 1 (by rfl) ⟨3920075, by rfl⟩ : syracuseStep 5226767 = 7840151) B7840151
theorem B1032463 : Blo 1028606 1032463 := bstep (se 1 (by rfl) ⟨774347, by rfl⟩ : syracuseStep 1032463 = 1548695) B1548695
theorem B2605355 : Blo 1028606 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B1032507 : Blo 1028606 1032507 := bstep (se 1 (by rfl) ⟨774380, by rfl⟩ : syracuseStep 1032507 = 1548761) B1548761
theorem B1032583 : Blo 1028606 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B1032591 : Blo 1028606 1032591 := bstep (se 1 (by rfl) ⟨774443, by rfl⟩ : syracuseStep 1032591 = 1548887) B1548887
theorem B5653111 : Blo 1028606 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B2606195 : Blo 1028606 2606195 := bstep (se 1 (by rfl) ⟨1954646, by rfl⟩ : syracuseStep 2606195 = 3909293) B3909293
theorem B2606215 : Blo 1028606 2606215 := bstep (se 1 (by rfl) ⟨1954661, by rfl⟩ : syracuseStep 2606215 = 3909323) B3909323
theorem B2606489 : Blo 1028606 2606489 := bstep (se 2 (by rfl) ⟨977433, by rfl⟩ : syracuseStep 2606489 = 1954867) B1954867
theorem B2115001 : Blo 1028606 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B2606651 : Blo 1028606 2606651 := bstep (se 1 (by rfl) ⟨1954988, by rfl⟩ : syracuseStep 2606651 = 3909977) B3909977
theorem B7816823 : Blo 1028606 7816823 := bstep (se 1 (by rfl) ⟨5862617, by rfl⟩ : syracuseStep 7816823 = 11725235) B11725235
theorem B2934407 : Blo 1028606 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2606863 : Blo 1028606 2606863 := bstep (se 1 (by rfl) ⟨1955147, by rfl⟩ : syracuseStep 2606863 = 3910295) B3910295
theorem B3917753 : Blo 1028606 3917753 := bstep (se 2 (by rfl) ⟨1469157, by rfl⟩ : syracuseStep 3917753 = 2938315) B2938315
theorem B29706263 : Blo 1028606 29706263 := bstep (se 1 (by rfl) ⟨22279697, by rfl⟩ : syracuseStep 29706263 = 44559395) B44559395
theorem B2607137 : Blo 1028606 2607137 := bstep (se 2 (by rfl) ⟨977676, by rfl⟩ : syracuseStep 2607137 = 1955353) B1955353
theorem B4409387 : Blo 1028606 4409387 := bstep (se 1 (by rfl) ⟨3307040, by rfl⟩ : syracuseStep 4409387 = 6614081) B6614081
theorem B7817795 : Blo 1028606 7817795 := bstep (se 1 (by rfl) ⟨5863346, by rfl⟩ : syracuseStep 7817795 = 11726693) B11726693
theorem B3132161 : Blo 1028606 3132161 := bstep (se 2 (by rfl) ⟨1174560, by rfl⟩ : syracuseStep 3132161 = 2349121) B2349121
theorem B7424783 : Blo 1028606 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B3918739 : Blo 1028606 3918739 := bstep (se 1 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 3918739 = 5878109) B5878109
theorem B2608139 : Blo 1028606 2608139 := bstep (se 1 (by rfl) ⟨1956104, by rfl⟩ : syracuseStep 2608139 = 3912209) B3912209
theorem B3132503 : Blo 1028606 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B1953067 : Blo 1028606 1953067 := bstep (se 1 (by rfl) ⟨1464800, by rfl⟩ : syracuseStep 1953067 = 2929601) B2929601
theorem B1953143 : Blo 1028606 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B2936321 : Blo 1028606 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B2608787 : Blo 1028606 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B2477753 : Blo 1028606 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2609081 : Blo 1028606 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B2936891 : Blo 1028606 2936891 := bstep (se 1 (by rfl) ⟨2202668, by rfl⟩ : syracuseStep 2936891 = 4405337) B4405337
theorem B2478281 : Blo 1028606 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B2314511 : Blo 1028606 2314511 := bstep (se 1 (by rfl) ⟨1735883, by rfl⟩ : syracuseStep 2314511 = 3471767) B3471767
theorem B2314529 : Blo 1028606 2314529 := bstep (se 2 (by rfl) ⟨867948, by rfl⟩ : syracuseStep 2314529 = 1735897) B1735897
theorem B1855777 : Blo 1028606 1855777 := bstep (se 2 (by rfl) ⟨695916, by rfl⟩ : syracuseStep 1855777 = 1391833) B1391833
theorem B2937131 : Blo 1028606 2937131 := bstep (se 1 (by rfl) ⟨2202848, by rfl⟩ : syracuseStep 2937131 = 4405697) B4405697
theorem B2478521 : Blo 1028606 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B13587011 : Blo 1028606 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B3920471 : Blo 1028606 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B2609779 : Blo 1028606 2609779 := bstep (se 1 (by rfl) ⟨1957334, by rfl⟩ : syracuseStep 2609779 = 3914669) B3914669
theorem B2314871 : Blo 1028606 2314871 := bstep (se 1 (by rfl) ⟨1736153, by rfl⟩ : syracuseStep 2314871 = 3472307) B3472307
theorem B54317699 : Blo 1028606 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B11129561 : Blo 1028606 11129561 := bstep (se 2 (by rfl) ⟨4173585, by rfl⟩ : syracuseStep 11129561 = 8347171) B8347171
theorem B2609921 : Blo 1028606 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B2315051 : Blo 1028606 2315051 := bstep (se 1 (by rfl) ⟨1736288, by rfl⟩ : syracuseStep 2315051 = 3472577) B3472577
theorem B1856441 : Blo 1028606 1856441 := bstep (se 2 (by rfl) ⟨696165, by rfl⟩ : syracuseStep 1856441 = 1392331) B1392331
theorem B3298391 : Blo 1028606 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B2315411 : Blo 1028606 2315411 := bstep (se 1 (by rfl) ⟨1736558, by rfl⟩ : syracuseStep 2315411 = 3473117) B3473117
theorem B2315465 : Blo 1028606 2315465 := bstep (se 2 (by rfl) ⟨868299, by rfl⟩ : syracuseStep 2315465 = 1736599) B1736599
theorem B2610377 : Blo 1028606 2610377 := bstep (se 2 (by rfl) ⟨978891, by rfl⟩ : syracuseStep 2610377 = 1957783) B1957783
theorem B8803565 : Blo 1028606 8803565 := bstep (se 3 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 8803565 = 3301337) B3301337
theorem B1955087 : Blo 1028606 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B5952953 : Blo 1028606 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B5658065 : Blo 1028606 5658065 := bstep (se 2 (by rfl) ⟨2121774, by rfl⟩ : syracuseStep 5658065 = 4243549) B4243549
theorem B2610731 : Blo 1028606 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B3298877 : Blo 1028606 3298877 := bstep (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) B1237079
theorem B2479751 : Blo 1028606 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B2905915 : Blo 1028606 2905915 := bstep (se 1 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 2905915 = 4358873) B4358873
theorem B2316167 : Blo 1028606 2316167 := bstep (se 1 (by rfl) ⟨1737125, by rfl⟩ : syracuseStep 2316167 = 3474251) B3474251
theorem B20043821 : Blo 1028606 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B2316347 : Blo 1028606 2316347 := bstep (se 1 (by rfl) ⟨1737260, by rfl⟩ : syracuseStep 2316347 = 3474521) B3474521
theorem B2316473 : Blo 1028606 2316473 := bstep (se 2 (by rfl) ⟨868677, by rfl⟩ : syracuseStep 2316473 = 1737355) B1737355
theorem B1857737 : Blo 1028606 1857737 := bstep (se 2 (by rfl) ⟨696651, by rfl⟩ : syracuseStep 1857737 = 1393303) B1393303
theorem B16963829 : Blo 1028606 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B47569301 : Blo 1028606 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B2611723 : Blo 1028606 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B2316815 : Blo 1028606 2316815 := bstep (se 1 (by rfl) ⟨1737611, by rfl⟩ : syracuseStep 2316815 = 3475223) B3475223
theorem B2316833 : Blo 1028606 2316833 := bstep (se 2 (by rfl) ⟨868812, by rfl⟩ : syracuseStep 2316833 = 1737625) B1737625
theorem B2611865 : Blo 1028606 2611865 := bstep (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) B1958899
theorem B2612027 : Blo 1028606 2612027 := bstep (se 1 (by rfl) ⟨1959020, by rfl⟩ : syracuseStep 2612027 = 3918041) B3918041
theorem B7822169 : Blo 1028606 7822169 := bstep (se 2 (by rfl) ⟨2933313, by rfl⟩ : syracuseStep 7822169 = 5866627) B5866627
theorem B2317175 : Blo 1028606 2317175 := bstep (se 1 (by rfl) ⟨1737881, by rfl⟩ : syracuseStep 2317175 = 3475763) B3475763
theorem B1956727 : Blo 1028606 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B3136441 : Blo 1028606 3136441 := bstep (se 2 (by rfl) ⟨1176165, by rfl⟩ : syracuseStep 3136441 = 2352331) B2352331
theorem B2350025 : Blo 1028606 2350025 := bstep (se 2 (by rfl) ⟨881259, by rfl⟩ : syracuseStep 2350025 = 1762519) B1762519
theorem B2317355 : Blo 1028606 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B2612371 : Blo 1028606 2612371 := bstep (se 1 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 2612371 = 3918557) B3918557
theorem B2612513 : Blo 1028606 2612513 := bstep (se 2 (by rfl) ⟨979692, by rfl⟩ : syracuseStep 2612513 = 1959385) B1959385
theorem B2317715 : Blo 1028606 2317715 := bstep (se 1 (by rfl) ⟨1738286, by rfl⟩ : syracuseStep 2317715 = 3476573) B3476573
theorem B2317769 : Blo 1028606 2317769 := bstep (se 2 (by rfl) ⟨869163, by rfl⟩ : syracuseStep 2317769 = 1738327) B1738327
theorem B8805955 : Blo 1028606 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B1302151 : Blo 1028606 1302151 := bstep (se 1 (by rfl) ⟨976613, by rfl⟩ : syracuseStep 1302151 = 1953227) B1953227
theorem B7823141 : Blo 1028606 7823141 := bstep (se 4 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 7823141 = 1466839) B1466839
theorem B4186009 : Blo 1028606 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B1302571 : Blo 1028606 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B7430231 : Blo 1028606 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B2318471 : Blo 1028606 2318471 := bstep (se 1 (by rfl) ⟨1738853, by rfl⟩ : syracuseStep 2318471 = 3477707) B3477707
theorem B2613505 : Blo 1028606 2613505 := bstep (se 2 (by rfl) ⟨980064, by rfl⟩ : syracuseStep 2613505 = 1960129) B1960129
theorem B1302799 : Blo 1028606 1302799 := bstep (se 1 (by rfl) ⟨977099, by rfl⟩ : syracuseStep 1302799 = 1954199) B1954199
theorem B6611233 : Blo 1028606 6611233 := bstep (se 2 (by rfl) ⟨2479212, by rfl⟩ : syracuseStep 6611233 = 4958425) B4958425
theorem B1564985 : Blo 1028606 1564985 := bstep (se 2 (by rfl) ⟨586869, by rfl⟩ : syracuseStep 1564985 = 1173739) B1173739
theorem B2318651 : Blo 1028606 2318651 := bstep (se 1 (by rfl) ⟨1738988, by rfl⟩ : syracuseStep 2318651 = 3477977) B3477977
theorem B14836061 : Blo 1028606 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B1466743 : Blo 1028606 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B2318777 : Blo 1028606 2318777 := bstep (se 2 (by rfl) ⟨869541, by rfl⟩ : syracuseStep 2318777 = 1739083) B1739083
theorem B2646539 : Blo 1028606 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B1958519 : Blo 1028606 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1467067 : Blo 1028606 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B2319119 : Blo 1028606 2319119 := bstep (se 1 (by rfl) ⟨1739339, by rfl⟩ : syracuseStep 2319119 = 3478679) B3478679
theorem B1958671 : Blo 1028606 1958671 := bstep (se 1 (by rfl) ⟨1469003, by rfl⟩ : syracuseStep 1958671 = 2938007) B2938007
theorem B2319137 : Blo 1028606 2319137 := bstep (se 2 (by rfl) ⟨869676, by rfl⟩ : syracuseStep 2319137 = 1739353) B1739353
theorem B8938291 : Blo 1028606 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1860499 : Blo 1028606 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B18801571 : Blo 1028606 18801571 := bstep (se 1 (by rfl) ⟨14101178, by rfl⟩ : syracuseStep 18801571 = 28202357) B28202357
theorem B1303543 : Blo 1028606 1303543 := bstep (se 1 (by rfl) ⟨977657, by rfl⟩ : syracuseStep 1303543 = 1955315) B1955315
theorem B2319479 : Blo 1028606 2319479 := bstep (se 1 (by rfl) ⟨1739609, by rfl⟩ : syracuseStep 2319479 = 3479219) B3479219
theorem B1959059 : Blo 1028606 1959059 := bstep (se 1 (by rfl) ⟨1469294, by rfl⟩ : syracuseStep 1959059 = 2938589) B2938589
theorem B2319659 : Blo 1028606 2319659 := bstep (se 1 (by rfl) ⟨1739744, by rfl⟩ : syracuseStep 2319659 = 3479489) B3479489
theorem B1303867 : Blo 1028606 1303867 := bstep (se 1 (by rfl) ⟨977900, by rfl⟩ : syracuseStep 1303867 = 1955801) B1955801
theorem B9921851 : Blo 1028606 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B8807939 : Blo 1028606 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B14116355 : Blo 1028606 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B2090539 : Blo 1028606 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B65103437 : Blo 1028606 65103437 := bstep (se 3 (by rfl) ⟨12206894, by rfl⟩ : syracuseStep 65103437 = 24413789) B24413789
theorem B2320019 : Blo 1028606 2320019 := bstep (se 1 (by rfl) ⟨1740014, by rfl⟩ : syracuseStep 2320019 = 3480029) B3480029
theorem B2320073 : Blo 1028606 2320073 := bstep (se 2 (by rfl) ⟨870027, by rfl⟩ : syracuseStep 2320073 = 1740055) B1740055
theorem B1304363 : Blo 1028606 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B1304839 : Blo 1028606 1304839 := bstep (se 1 (by rfl) ⟨978629, by rfl⟩ : syracuseStep 1304839 = 1957259) B1957259
theorem B1337719 : Blo 1028606 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B2320775 : Blo 1028606 2320775 := bstep (se 1 (by rfl) ⟨1740581, by rfl⟩ : syracuseStep 2320775 = 3481163) B3481163
theorem B5859863 : Blo 1028606 5859863 := bstep (se 1 (by rfl) ⟨4394897, by rfl⟩ : syracuseStep 5859863 = 8789795) B8789795
theorem B3303965 : Blo 1028606 3303965 := bstep (se 3 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 3303965 = 1238987) B1238987
theorem B2320955 : Blo 1028606 2320955 := bstep (se 1 (by rfl) ⟨1740716, by rfl⟩ : syracuseStep 2320955 = 3481433) B3481433
theorem B2321081 : Blo 1028606 2321081 := bstep (se 2 (by rfl) ⟨870405, by rfl⟩ : syracuseStep 2321081 = 1740811) B1740811
theorem B1305335 : Blo 1028606 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1239799 : Blo 1028606 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B1305487 : Blo 1028606 1305487 := bstep (se 1 (by rfl) ⟨979115, by rfl⟩ : syracuseStep 1305487 = 1958231) B1958231
theorem B3959705 : Blo 1028606 3959705 := bstep (se 2 (by rfl) ⟨1484889, by rfl⟩ : syracuseStep 3959705 = 2969779) B2969779
theorem B1469431 : Blo 1028606 1469431 := bstep (se 1 (by rfl) ⟨1102073, by rfl⟩ : syracuseStep 1469431 = 2204147) B2204147
theorem B2321423 : Blo 1028606 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B2321441 : Blo 1028606 2321441 := bstep (se 2 (by rfl) ⟨870540, by rfl⟩ : syracuseStep 2321441 = 1741081) B1741081
theorem B1305659 : Blo 1028606 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B1240183 : Blo 1028606 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B9891017 : Blo 1028606 9891017 := bstep (se 2 (by rfl) ⟨3709131, by rfl⟩ : syracuseStep 9891017 = 7418263) B7418263
theorem B1469755 : Blo 1028606 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B2321783 : Blo 1028606 2321783 := bstep (se 1 (by rfl) ⟨1741337, by rfl⟩ : syracuseStep 2321783 = 3482675) B3482675
theorem B2321963 : Blo 1028606 2321963 := bstep (se 1 (by rfl) ⟨1741472, by rfl⟩ : syracuseStep 2321963 = 3482945) B3482945
theorem B1470251 : Blo 1028606 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B8810329 : Blo 1028606 8810329 := bstep (se 2 (by rfl) ⟨3303873, by rfl⟩ : syracuseStep 8810329 = 6607747) B6607747
theorem B2322323 : Blo 1028606 2322323 := bstep (se 1 (by rfl) ⟨1741742, by rfl⟩ : syracuseStep 2322323 = 3483485) B3483485
theorem B1568683 : Blo 1028606 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B2322377 : Blo 1028606 2322377 := bstep (se 2 (by rfl) ⟨870891, by rfl⟩ : syracuseStep 2322377 = 1741783) B1741783
theorem B1306631 : Blo 1028606 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B2323079 : Blo 1028606 2323079 := bstep (se 1 (by rfl) ⟨1742309, by rfl⟩ : syracuseStep 2323079 = 3484619) B3484619
theorem B12546737 : Blo 1028606 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B2323259 : Blo 1028606 2323259 := bstep (se 1 (by rfl) ⟨1742444, by rfl⟩ : syracuseStep 2323259 = 3484889) B3484889
theorem B3306539 : Blo 1028606 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B90273005 : Blo 1028606 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B3306899 : Blo 1028606 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B9893441 : Blo 1028606 9893441 := bstep (se 2 (by rfl) ⟨3710040, by rfl⟩ : syracuseStep 9893441 = 7420081) B7420081
theorem B7927415 : Blo 1028606 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B41318261 : Blo 1028606 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B4945799 : Blo 1028606 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B8353853 : Blo 1028606 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B7829945 : Blo 1028606 7829945 := bstep (se 2 (by rfl) ⟨2936229, by rfl⟩ : syracuseStep 7829945 = 5872459) B5872459
theorem B23788151 : Blo 1028606 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B7535375 : Blo 1028606 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B9894707 : Blo 1028606 9894707 := bstep (se 1 (by rfl) ⟨7421030, by rfl⟩ : syracuseStep 9894707 = 14842061) B14842061
theorem B5208947 : Blo 1028606 5208947 := bstep (se 1 (by rfl) ⟨3906710, by rfl⟩ : syracuseStep 5208947 = 7813421) B7813421
theorem B2784185 : Blo 1028606 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B1735951 : Blo 1028606 1735951 := bstep (se 1 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 1735951 = 2603927) B2603927
theorem B5209433 : Blo 1028606 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B3472793 : Blo 1028606 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B1736491 : Blo 1028606 1736491 := bstep (se 1 (by rfl) ⟨1302368, by rfl⟩ : syracuseStep 1736491 = 2604737) B2604737
theorem B1736633 : Blo 1028606 1736633 := bstep (se 2 (by rfl) ⟨651237, by rfl⟩ : syracuseStep 1736633 = 1302475) B1302475
theorem B9404363 : Blo 1028606 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B1736761 : Blo 1028606 1736761 := bstep (se 2 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 1736761 = 1302571) B1302571
theorem B9404579 : Blo 1028606 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B1736903 : Blo 1028606 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B1737065 : Blo 1028606 1737065 := bstep (se 2 (by rfl) ⟨651399, by rfl⟩ : syracuseStep 1737065 = 1302799) B1302799
theorem B8814977 : Blo 1028606 8814977 := bstep (se 2 (by rfl) ⟨3305616, by rfl⟩ : syracuseStep 8814977 = 6611233) B6611233
theorem B1737463 : Blo 1028606 1737463 := bstep (se 1 (by rfl) ⟨1303097, by rfl⟩ : syracuseStep 1737463 = 2606195) B2606195
theorem B7537481 : Blo 1028606 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B3474359 : Blo 1028606 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B1737659 : Blo 1028606 1737659 := bstep (se 1 (by rfl) ⟨1303244, by rfl⟩ : syracuseStep 1737659 = 2606489) B2606489
theorem B1737767 : Blo 1028606 1737767 := bstep (se 1 (by rfl) ⟨1303325, by rfl⟩ : syracuseStep 1737767 = 2606651) B2606651
theorem B5211215 : Blo 1028606 5211215 := bstep (se 1 (by rfl) ⟨3908411, by rfl⟩ : syracuseStep 5211215 = 7816823) B7816823
theorem B25068761 : Blo 1028606 25068761 := bstep (se 2 (by rfl) ⟨9400785, by rfl⟩ : syracuseStep 25068761 = 18801571) B18801571
theorem B1738057 : Blo 1028606 1738057 := bstep (se 2 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 1738057 = 1303543) B1303543
theorem B1738091 : Blo 1028606 1738091 := bstep (se 1 (by rfl) ⟨1303568, by rfl⟩ : syracuseStep 1738091 = 2607137) B2607137
theorem B3474953 : Blo 1028606 3474953 := bstep (se 2 (by rfl) ⟨1303107, by rfl⟩ : syracuseStep 3474953 = 2606215) B2606215
theorem B5867153 : Blo 1028606 5867153 := bstep (se 2 (by rfl) ⟨2200182, by rfl⟩ : syracuseStep 5867153 = 4400365) B4400365
theorem B5211863 : Blo 1028606 5211863 := bstep (se 1 (by rfl) ⟨3908897, by rfl⟩ : syracuseStep 5211863 = 7817795) B7817795
theorem B1738489 : Blo 1028606 1738489 := bstep (se 2 (by rfl) ⟨651933, by rfl⟩ : syracuseStep 1738489 = 1303867) B1303867
theorem B4949855 : Blo 1028606 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B1738759 : Blo 1028606 1738759 := bstep (se 1 (by rfl) ⟨1304069, by rfl⟩ : syracuseStep 1738759 = 2608139) B2608139
theorem B2787385 : Blo 1028606 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B3475817 : Blo 1028606 3475817 := bstep (se 2 (by rfl) ⟨1303431, by rfl⟩ : syracuseStep 3475817 = 2606863) B2606863
theorem B1739191 : Blo 1028606 1739191 := bstep (se 1 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 1739191 = 2608787) B2608787
theorem B1739387 : Blo 1028606 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B8817437 : Blo 1028606 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B2198345 : Blo 1028606 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B1543007 : Blo 1028606 1543007 := bstep (se 1 (by rfl) ⟨1157255, by rfl⟩ : syracuseStep 1543007 = 2314511) B2314511
theorem B1543019 : Blo 1028606 1543019 := bstep (se 1 (by rfl) ⟨1157264, by rfl⟩ : syracuseStep 1543019 = 2314529) B2314529
theorem B3476411 : Blo 1028606 3476411 := bstep (se 1 (by rfl) ⟨2607308, by rfl⟩ : syracuseStep 3476411 = 5214617) B5214617
theorem B1739785 : Blo 1028606 1739785 := bstep (se 2 (by rfl) ⟨652419, by rfl⟩ : syracuseStep 1739785 = 1304839) B1304839
theorem B2198585 : Blo 1028606 2198585 := bstep (se 2 (by rfl) ⟨824469, by rfl⟩ : syracuseStep 2198585 = 1648939) B1648939
theorem B1543247 : Blo 1028606 1543247 := bstep (se 1 (by rfl) ⟨1157435, by rfl⟩ : syracuseStep 1543247 = 2314871) B2314871
theorem B36211799 : Blo 1028606 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B1739947 : Blo 1028606 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B1543367 : Blo 1028606 1543367 := bstep (se 1 (by rfl) ⟨1157525, by rfl⟩ : syracuseStep 1543367 = 2315051) B2315051
theorem B1543529 : Blo 1028606 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B2198927 : Blo 1028606 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B1543607 : Blo 1028606 1543607 := bstep (se 1 (by rfl) ⟨1157705, by rfl⟩ : syracuseStep 1543607 = 2315411) B2315411
theorem B1543643 : Blo 1028606 1543643 := bstep (se 1 (by rfl) ⟨1157732, by rfl⟩ : syracuseStep 1543643 = 2315465) B2315465
theorem B1740251 : Blo 1028606 1740251 := bstep (se 1 (by rfl) ⟨1305188, by rfl⟩ : syracuseStep 1740251 = 2610377) B2610377
theorem B5869043 : Blo 1028606 5869043 := bstep (se 1 (by rfl) ⟨4401782, by rfl⟩ : syracuseStep 5869043 = 8803565) B8803565
theorem B3968635 : Blo 1028606 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B3772043 : Blo 1028606 3772043 := bstep (se 1 (by rfl) ⟨2829032, by rfl⟩ : syracuseStep 3772043 = 5658065) B5658065
theorem B1740487 : Blo 1028606 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B2199251 : Blo 1028606 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B1740649 : Blo 1028606 1740649 := bstep (se 2 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 1740649 = 1305487) B1305487
theorem B1544111 : Blo 1028606 1544111 := bstep (se 1 (by rfl) ⟨1158083, by rfl⟩ : syracuseStep 1544111 = 2316167) B2316167
theorem B1544201 : Blo 1028606 1544201 := bstep (se 2 (by rfl) ⟨579075, by rfl⟩ : syracuseStep 1544201 = 1158151) B1158151
theorem B1544231 : Blo 1028606 1544231 := bstep (se 1 (by rfl) ⟨1158173, by rfl⟩ : syracuseStep 1544231 = 2316347) B2316347
theorem B1544315 : Blo 1028606 1544315 := bstep (se 1 (by rfl) ⟨1158236, by rfl⟩ : syracuseStep 1544315 = 2316473) B2316473
theorem B11309219 : Blo 1028606 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B1544441 : Blo 1028606 1544441 := bstep (se 2 (by rfl) ⟨579165, by rfl⟩ : syracuseStep 1544441 = 1158331) B1158331
theorem B1544543 : Blo 1028606 1544543 := bstep (se 1 (by rfl) ⟨1158407, by rfl⟩ : syracuseStep 1544543 = 2316815) B2316815
theorem B1544555 : Blo 1028606 1544555 := bstep (se 1 (by rfl) ⟨1158416, by rfl⟩ : syracuseStep 1544555 = 2316833) B2316833
theorem B1741243 : Blo 1028606 1741243 := bstep (se 1 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 1741243 = 2611865) B2611865
theorem B1741351 : Blo 1028606 1741351 := bstep (se 1 (by rfl) ⟨1306013, by rfl⟩ : syracuseStep 1741351 = 2612027) B2612027
theorem B5214779 : Blo 1028606 5214779 := bstep (se 1 (by rfl) ⟨3911084, by rfl⟩ : syracuseStep 5214779 = 7822169) B7822169
theorem B1544783 : Blo 1028606 1544783 := bstep (se 1 (by rfl) ⟨1158587, by rfl⟩ : syracuseStep 1544783 = 2317175) B2317175
theorem B3478139 : Blo 1028606 3478139 := bstep (se 1 (by rfl) ⟨2608604, by rfl⟩ : syracuseStep 3478139 = 5217209) B5217209
theorem B1544903 : Blo 1028606 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B3478301 : Blo 1028606 3478301 := bstep (se 3 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 3478301 = 1304363) B1304363
theorem B1545065 : Blo 1028606 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1741675 : Blo 1028606 1741675 := bstep (se 1 (by rfl) ⟨1306256, by rfl⟩ : syracuseStep 1741675 = 2612513) B2612513
theorem B1545143 : Blo 1028606 1545143 := bstep (se 1 (by rfl) ⟨1158857, by rfl⟩ : syracuseStep 1545143 = 2317715) B2317715
theorem B1545179 : Blo 1028606 1545179 := bstep (se 1 (by rfl) ⟨1158884, by rfl⟩ : syracuseStep 1545179 = 2317769) B2317769
theorem B5215427 : Blo 1028606 5215427 := bstep (se 1 (by rfl) ⟨3911570, by rfl⟩ : syracuseStep 5215427 = 7823141) B7823141
theorem B4953487 : Blo 1028606 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B1545647 : Blo 1028606 1545647 := bstep (se 1 (by rfl) ⟨1159235, by rfl⟩ : syracuseStep 1545647 = 2318471) B2318471
theorem B4953545 : Blo 1028606 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B53450189 : Blo 1028606 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B3479003 : Blo 1028606 3479003 := bstep (se 1 (by rfl) ⟨2609252, by rfl⟩ : syracuseStep 3479003 = 5218505) B5218505
theorem B1545737 : Blo 1028606 1545737 := bstep (se 2 (by rfl) ⟨579651, by rfl⟩ : syracuseStep 1545737 = 1159303) B1159303
theorem B1545767 : Blo 1028606 1545767 := bstep (se 1 (by rfl) ⟨1159325, by rfl⟩ : syracuseStep 1545767 = 2318651) B2318651
theorem B1545851 : Blo 1028606 1545851 := bstep (se 1 (by rfl) ⟨1159388, by rfl⟩ : syracuseStep 1545851 = 2318777) B2318777
theorem B1545977 : Blo 1028606 1545977 := bstep (se 2 (by rfl) ⟨579741, by rfl⟩ : syracuseStep 1545977 = 1159483) B1159483
theorem B1546079 : Blo 1028606 1546079 := bstep (se 1 (by rfl) ⟨1159559, by rfl⟩ : syracuseStep 1546079 = 2319119) B2319119
theorem B5576543 : Blo 1028606 5576543 := bstep (se 1 (by rfl) ⟨4182407, by rfl⟩ : syracuseStep 5576543 = 8364815) B8364815
theorem B1546091 : Blo 1028606 1546091 := bstep (se 1 (by rfl) ⟨1159568, by rfl⟩ : syracuseStep 1546091 = 2319137) B2319137
theorem B4953965 : Blo 1028606 4953965 := bstep (se 3 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 4953965 = 1857737) B1857737
theorem B1546319 : Blo 1028606 1546319 := bstep (se 1 (by rfl) ⟨1159739, by rfl⟩ : syracuseStep 1546319 = 2319479) B2319479
theorem B3905617 : Blo 1028606 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B3479705 : Blo 1028606 3479705 := bstep (se 2 (by rfl) ⟨1304889, by rfl⟩ : syracuseStep 3479705 = 2609779) B2609779
theorem B1546439 : Blo 1028606 1546439 := bstep (se 1 (by rfl) ⟨1159829, by rfl⟩ : syracuseStep 1546439 = 2319659) B2319659
theorem B5871959 : Blo 1028606 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B9410903 : Blo 1028606 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B11901289 : Blo 1028606 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B1546601 : Blo 1028606 1546601 := bstep (se 2 (by rfl) ⟨579975, by rfl⟩ : syracuseStep 1546601 = 1159951) B1159951
theorem B3905921 : Blo 1028606 3905921 := bstep (se 2 (by rfl) ⟨1464720, by rfl⟩ : syracuseStep 3905921 = 2929441) B2929441
theorem B1546679 : Blo 1028606 1546679 := bstep (se 1 (by rfl) ⟨1160009, by rfl⟩ : syracuseStep 1546679 = 2320019) B2320019
theorem B1546715 : Blo 1028606 1546715 := bstep (se 1 (by rfl) ⟨1160036, by rfl⟩ : syracuseStep 1546715 = 2320073) B2320073
theorem B3709421 : Blo 1028606 3709421 := bstep (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) B1391033
theorem B3906377 : Blo 1028606 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B1547183 : Blo 1028606 1547183 := bstep (se 1 (by rfl) ⟨1160387, by rfl⟩ : syracuseStep 1547183 = 2320775) B2320775
theorem B7838693 : Blo 1028606 7838693 := bstep (se 4 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 7838693 = 1469755) B1469755
theorem B1547273 : Blo 1028606 1547273 := bstep (se 2 (by rfl) ⟨580227, by rfl⟩ : syracuseStep 1547273 = 1160455) B1160455
theorem B3906575 : Blo 1028606 3906575 := bstep (se 1 (by rfl) ⟨2929931, by rfl⟩ : syracuseStep 3906575 = 5859863) B5859863
theorem B2202643 : Blo 1028606 2202643 := bstep (se 1 (by rfl) ⟨1651982, by rfl⟩ : syracuseStep 2202643 = 3303965) B3303965
theorem B1547303 : Blo 1028606 1547303 := bstep (se 1 (by rfl) ⟨1160477, by rfl⟩ : syracuseStep 1547303 = 2320955) B2320955
theorem B1547387 : Blo 1028606 1547387 := bstep (se 1 (by rfl) ⟨1160540, by rfl⟩ : syracuseStep 1547387 = 2321081) B2321081
theorem B1547513 : Blo 1028606 1547513 := bstep (se 2 (by rfl) ⟨580317, by rfl⟩ : syracuseStep 1547513 = 1160635) B1160635
theorem B3480893 : Blo 1028606 3480893 := bstep (se 3 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 3480893 = 1305335) B1305335
theorem B1547615 : Blo 1028606 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B1547627 : Blo 1028606 1547627 := bstep (se 1 (by rfl) ⟨1160720, by rfl⟩ : syracuseStep 1547627 = 2321441) B2321441
theorem B33430961 : Blo 1028606 33430961 := bstep (se 2 (by rfl) ⟨12536610, by rfl⟩ : syracuseStep 33430961 = 25073221) B25073221
theorem B6594011 : Blo 1028606 6594011 := bstep (se 1 (by rfl) ⟨4945508, by rfl⟩ : syracuseStep 6594011 = 9891017) B9891017
theorem B1547855 : Blo 1028606 1547855 := bstep (se 1 (by rfl) ⟨1160891, by rfl⟩ : syracuseStep 1547855 = 2321783) B2321783
theorem B11280005 : Blo 1028606 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B1547975 : Blo 1028606 1547975 := bstep (se 1 (by rfl) ⟨1160981, by rfl⟩ : syracuseStep 1547975 = 2321963) B2321963
theorem B10559213 : Blo 1028606 10559213 := bstep (se 3 (by rfl) ⟨1979852, by rfl⟩ : syracuseStep 10559213 = 3959705) B3959705
theorem B3874553 : Blo 1028606 3874553 := bstep (se 2 (by rfl) ⟨1452957, by rfl⟩ : syracuseStep 3874553 = 2905915) B2905915
theorem B1548137 : Blo 1028606 1548137 := bstep (se 2 (by rfl) ⟨580551, by rfl⟩ : syracuseStep 1548137 = 1161103) B1161103
theorem B1548215 : Blo 1028606 1548215 := bstep (se 1 (by rfl) ⟨1161161, by rfl⟩ : syracuseStep 1548215 = 2322323) B2322323
theorem B8363969 : Blo 1028606 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B1548251 : Blo 1028606 1548251 := bstep (se 1 (by rfl) ⟨1161188, by rfl⟩ : syracuseStep 1548251 = 2322377) B2322377
theorem B3481757 : Blo 1028606 3481757 := bstep (se 3 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 3481757 = 1305659) B1305659
theorem B1548719 : Blo 1028606 1548719 := bstep (se 1 (by rfl) ⟨1161539, by rfl⟩ : syracuseStep 1548719 = 2323079) B2323079
theorem B8364491 : Blo 1028606 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B1548809 : Blo 1028606 1548809 := bstep (se 2 (by rfl) ⟨580803, by rfl⟩ : syracuseStep 1548809 = 1161607) B1161607
theorem B12526103 : Blo 1028606 12526103 := bstep (se 1 (by rfl) ⟨9394577, by rfl⟩ : syracuseStep 12526103 = 18789155) B18789155
theorem B1548839 : Blo 1028606 1548839 := bstep (se 1 (by rfl) ⟨1161629, by rfl⟩ : syracuseStep 1548839 = 2323259) B2323259
theorem B3482297 : Blo 1028606 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B2204489 : Blo 1028606 2204489 := bstep (se 2 (by rfl) ⟨826683, by rfl⟩ : syracuseStep 2204489 = 1653367) B1653367
theorem B2204599 : Blo 1028606 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B6595627 : Blo 1028606 6595627 := bstep (se 1 (by rfl) ⟨4946720, by rfl⟩ : syracuseStep 6595627 = 9893441) B9893441
theorem B5284943 : Blo 1028606 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B8791193 : Blo 1028606 8791193 := bstep (se 2 (by rfl) ⟨3296697, by rfl⟩ : syracuseStep 8791193 = 6593395) B6593395
theorem B3482891 : Blo 1028606 3482891 := bstep (se 1 (by rfl) ⟨2612168, by rfl⟩ : syracuseStep 3482891 = 5224337) B5224337
theorem B3483161 : Blo 1028606 3483161 := bstep (se 2 (by rfl) ⟨1306185, by rfl⟩ : syracuseStep 3483161 = 2612371) B2612371
theorem B4957793 : Blo 1028606 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B5219963 : Blo 1028606 5219963 := bstep (se 1 (by rfl) ⟨3914972, by rfl⟩ : syracuseStep 5219963 = 7829945) B7829945
theorem B7415495 : Blo 1028606 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B4400963 : Blo 1028606 4400963 := bstep (se 1 (by rfl) ⟨3300722, by rfl⟩ : syracuseStep 4400963 = 6601445) B6601445
theorem B5023583 : Blo 1028606 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B6596471 : Blo 1028606 6596471 := bstep (se 1 (by rfl) ⟨4947353, by rfl⟩ : syracuseStep 6596471 = 9894707) B9894707
theorem B5875649 : Blo 1028606 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B11741273 : Blo 1028606 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B1648811 : Blo 1028606 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B54241589 : Blo 1028606 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B5581345 : Blo 1028606 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B1157755 : Blo 1028606 1157755 := bstep (se 1 (by rfl) ⟨868316, by rfl⟩ : syracuseStep 1157755 = 1736633) B1736633
theorem B6269575 : Blo 1028606 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B3484295 : Blo 1028606 3484295 := bstep (se 1 (by rfl) ⟨2613221, by rfl⟩ : syracuseStep 3484295 = 5226443) B5226443
theorem B1649323 : Blo 1028606 1649323 := bstep (se 1 (by rfl) ⟨1236992, by rfl⟩ : syracuseStep 1649323 = 2473985) B2473985
theorem B3484349 : Blo 1028606 3484349 := bstep (se 3 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 3484349 = 1306631) B1306631
theorem B17574731 : Blo 1028606 17574731 := bstep (se 1 (by rfl) ⟨13181048, by rfl⟩ : syracuseStep 17574731 = 26362097) B26362097
theorem B3484511 : Blo 1028606 3484511 := bstep (se 1 (by rfl) ⟨2613383, by rfl⟩ : syracuseStep 3484511 = 5226767) B5226767
theorem B3484673 : Blo 1028606 3484673 := bstep (se 2 (by rfl) ⟨1306752, by rfl⟩ : syracuseStep 3484673 = 2613505) B2613505
theorem B1158223 : Blo 1028606 1158223 := bstep (se 1 (by rfl) ⟨868667, by rfl⟩ : syracuseStep 1158223 = 1737335) B1737335
theorem B1158619 : Blo 1028606 1158619 := bstep (se 1 (by rfl) ⟨868964, by rfl⟩ : syracuseStep 1158619 = 1737929) B1737929
theorem B39562829 : Blo 1028606 39562829 := bstep (se 3 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 39562829 = 14836061) B14836061
theorem B1159087 : Blo 1028606 1159087 := bstep (se 1 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 1159087 = 1738631) B1738631
theorem B19804175 : Blo 1028606 19804175 := bstep (se 1 (by rfl) ⟨14853131, by rfl⟩ : syracuseStep 19804175 = 29706263) B29706263
theorem B4960271 : Blo 1028606 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B5222717 : Blo 1028606 5222717 := bstep (se 3 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 5222717 = 1958519) B1958519
theorem B1159519 : Blo 1028606 1159519 := bstep (se 1 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 1159519 = 1739279) B1739279
theorem B1028647 : Blo 1028606 1028647 := bstep (se 1 (by rfl) ⟨771485, by rfl⟩ : syracuseStep 1028647 = 1542971) B1542971
theorem B1028687 : Blo 1028606 1028687 := bstep (se 1 (by rfl) ⟨771515, by rfl⟩ : syracuseStep 1028687 = 1543031) B1543031
theorem B1028703 : Blo 1028606 1028703 := bstep (se 1 (by rfl) ⟨771527, by rfl⟩ : syracuseStep 1028703 = 1543055) B1543055
theorem B1028731 : Blo 1028606 1028731 := bstep (se 1 (by rfl) ⟨771548, by rfl⟩ : syracuseStep 1028731 = 1543097) B1543097
theorem B4174459 : Blo 1028606 4174459 := bstep (se 1 (by rfl) ⟨3130844, by rfl⟩ : syracuseStep 4174459 = 6261689) B6261689
theorem B1028783 : Blo 1028606 1028783 := bstep (se 1 (by rfl) ⟨771587, by rfl⟩ : syracuseStep 1028783 = 1543175) B1543175
theorem B1028807 : Blo 1028606 1028807 := bstep (se 1 (by rfl) ⟨771605, by rfl⟩ : syracuseStep 1028807 = 1543211) B1543211
theorem B1159879 : Blo 1028606 1159879 := bstep (se 1 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 1159879 = 1739819) B1739819
theorem B3912407 : Blo 1028606 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1028827 : Blo 1028606 1028827 := bstep (se 1 (by rfl) ⟨771620, by rfl⟩ : syracuseStep 1028827 = 1543241) B1543241
theorem B1028903 : Blo 1028606 1028903 := bstep (se 1 (by rfl) ⟨771677, by rfl⟩ : syracuseStep 1028903 = 1543355) B1543355
theorem B1028943 : Blo 1028606 1028943 := bstep (se 1 (by rfl) ⟨771707, by rfl⟩ : syracuseStep 1028943 = 1543415) B1543415
theorem B1028959 : Blo 1028606 1028959 := bstep (se 1 (by rfl) ⟨771719, by rfl⟩ : syracuseStep 1028959 = 1543439) B1543439
theorem B1028987 : Blo 1028606 1028987 := bstep (se 1 (by rfl) ⟨771740, by rfl⟩ : syracuseStep 1028987 = 1543481) B1543481
theorem B14300057 : Blo 1028606 14300057 := bstep (se 2 (by rfl) ⟨5362521, by rfl⟩ : syracuseStep 14300057 = 10725043) B10725043
theorem B1029039 : Blo 1028606 1029039 := bstep (se 1 (by rfl) ⟨771779, by rfl⟩ : syracuseStep 1029039 = 1543559) B1543559
theorem B1029063 : Blo 1028606 1029063 := bstep (se 1 (by rfl) ⟨771797, by rfl⟩ : syracuseStep 1029063 = 1543595) B1543595
theorem B1029083 : Blo 1028606 1029083 := bstep (se 1 (by rfl) ⟨771812, by rfl⟩ : syracuseStep 1029083 = 1543625) B1543625
theorem B1029159 : Blo 1028606 1029159 := bstep (se 1 (by rfl) ⟨771869, by rfl⟩ : syracuseStep 1029159 = 1543739) B1543739
theorem B14857283 : Blo 1028606 14857283 := bstep (se 1 (by rfl) ⟨11142962, by rfl⟩ : syracuseStep 14857283 = 22285925) B22285925
theorem B1029199 : Blo 1028606 1029199 := bstep (se 1 (by rfl) ⟨771899, by rfl⟩ : syracuseStep 1029199 = 1543799) B1543799
theorem B1029215 : Blo 1028606 1029215 := bstep (se 1 (by rfl) ⟨771911, by rfl⟩ : syracuseStep 1029215 = 1543823) B1543823
theorem B1029243 : Blo 1028606 1029243 := bstep (se 1 (by rfl) ⟨771932, by rfl⟩ : syracuseStep 1029243 = 1543865) B1543865
theorem B1651835 : Blo 1028606 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B1029295 : Blo 1028606 1029295 := bstep (se 1 (by rfl) ⟨771971, by rfl⟩ : syracuseStep 1029295 = 1543943) B1543943
theorem B1029319 : Blo 1028606 1029319 := bstep (se 1 (by rfl) ⟨771989, by rfl⟩ : syracuseStep 1029319 = 1543979) B1543979
theorem B4961483 : Blo 1028606 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B1029339 : Blo 1028606 1029339 := bstep (se 1 (by rfl) ⟨772004, by rfl⟩ : syracuseStep 1029339 = 1544009) B1544009
theorem B1029415 : Blo 1028606 1029415 := bstep (se 1 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 1029415 = 1544123) B1544123
theorem B1029455 : Blo 1028606 1029455 := bstep (se 1 (by rfl) ⟨772091, by rfl⟩ : syracuseStep 1029455 = 1544183) B1544183
theorem B1029471 : Blo 1028606 1029471 := bstep (se 1 (by rfl) ⟨772103, by rfl⟩ : syracuseStep 1029471 = 1544207) B1544207
theorem B1029499 : Blo 1028606 1029499 := bstep (se 1 (by rfl) ⟨772124, by rfl⟩ : syracuseStep 1029499 = 1544249) B1544249
theorem B1029551 : Blo 1028606 1029551 := bstep (se 1 (by rfl) ⟨772163, by rfl⟩ : syracuseStep 1029551 = 1544327) B1544327
theorem B1029575 : Blo 1028606 1029575 := bstep (se 1 (by rfl) ⟨772181, by rfl⟩ : syracuseStep 1029575 = 1544363) B1544363
theorem B1029595 : Blo 1028606 1029595 := bstep (se 1 (by rfl) ⟨772196, by rfl⟩ : syracuseStep 1029595 = 1544393) B1544393
theorem B1029671 : Blo 1028606 1029671 := bstep (se 1 (by rfl) ⟨772253, by rfl⟩ : syracuseStep 1029671 = 1544507) B1544507
theorem B1160743 : Blo 1028606 1160743 := bstep (se 1 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 1160743 = 1741115) B1741115
theorem B1029711 : Blo 1028606 1029711 := bstep (se 1 (by rfl) ⟨772283, by rfl⟩ : syracuseStep 1029711 = 1544567) B1544567
theorem B1029727 : Blo 1028606 1029727 := bstep (se 1 (by rfl) ⟨772295, by rfl⟩ : syracuseStep 1029727 = 1544591) B1544591
theorem B1029755 : Blo 1028606 1029755 := bstep (se 1 (by rfl) ⟨772316, by rfl⟩ : syracuseStep 1029755 = 1544633) B1544633
theorem B1652347 : Blo 1028606 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B2471563 : Blo 1028606 2471563 := bstep (se 1 (by rfl) ⟨1853672, by rfl⟩ : syracuseStep 2471563 = 3707345) B3707345
theorem B1029807 : Blo 1028606 1029807 := bstep (se 1 (by rfl) ⟨772355, by rfl⟩ : syracuseStep 1029807 = 1544711) B1544711
theorem B1029831 : Blo 1028606 1029831 := bstep (se 1 (by rfl) ⟨772373, by rfl⟩ : syracuseStep 1029831 = 1544747) B1544747
theorem B9058007 : Blo 1028606 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B1029851 : Blo 1028606 1029851 := bstep (se 1 (by rfl) ⟨772388, by rfl⟩ : syracuseStep 1029851 = 1544777) B1544777
theorem B1029927 : Blo 1028606 1029927 := bstep (se 1 (by rfl) ⟨772445, by rfl⟩ : syracuseStep 1029927 = 1544891) B1544891
theorem B7419707 : Blo 1028606 7419707 := bstep (se 1 (by rfl) ⟨5564780, by rfl⟩ : syracuseStep 7419707 = 11129561) B11129561
theorem B1783625 : Blo 1028606 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B1029967 : Blo 1028606 1029967 := bstep (se 1 (by rfl) ⟨772475, by rfl⟩ : syracuseStep 1029967 = 1544951) B1544951
theorem B1029983 : Blo 1028606 1029983 := bstep (se 1 (by rfl) ⟨772487, by rfl⟩ : syracuseStep 1029983 = 1544975) B1544975
theorem B1030011 : Blo 1028606 1030011 := bstep (se 1 (by rfl) ⟨772508, by rfl⟩ : syracuseStep 1030011 = 1545017) B1545017
theorem B1030063 : Blo 1028606 1030063 := bstep (se 1 (by rfl) ⟨772547, by rfl⟩ : syracuseStep 1030063 = 1545095) B1545095
theorem B1030087 : Blo 1028606 1030087 := bstep (se 1 (by rfl) ⟨772565, by rfl⟩ : syracuseStep 1030087 = 1545131) B1545131
theorem B1030107 : Blo 1028606 1030107 := bstep (se 1 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 1030107 = 1545161) B1545161
theorem B1030183 : Blo 1028606 1030183 := bstep (se 1 (by rfl) ⟨772637, by rfl⟩ : syracuseStep 1030183 = 1545275) B1545275
theorem B1030223 : Blo 1028606 1030223 := bstep (se 1 (by rfl) ⟨772667, by rfl⟩ : syracuseStep 1030223 = 1545335) B1545335
theorem B1030239 : Blo 1028606 1030239 := bstep (se 1 (by rfl) ⟨772679, by rfl⟩ : syracuseStep 1030239 = 1545359) B1545359
theorem B1030267 : Blo 1028606 1030267 := bstep (se 1 (by rfl) ⟨772700, by rfl⟩ : syracuseStep 1030267 = 1545401) B1545401
theorem B1030319 : Blo 1028606 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B1030343 : Blo 1028606 1030343 := bstep (se 1 (by rfl) ⟨772757, by rfl⟩ : syracuseStep 1030343 = 1545515) B1545515
theorem B1030363 : Blo 1028606 1030363 := bstep (se 1 (by rfl) ⟨772772, by rfl⟩ : syracuseStep 1030363 = 1545545) B1545545
theorem B1030439 : Blo 1028606 1030439 := bstep (se 1 (by rfl) ⟨772829, by rfl⟩ : syracuseStep 1030439 = 1545659) B1545659
theorem B1653065 : Blo 1028606 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1030479 : Blo 1028606 1030479 := bstep (se 1 (by rfl) ⟨772859, by rfl⟩ : syracuseStep 1030479 = 1545719) B1545719
theorem B1030495 : Blo 1028606 1030495 := bstep (se 1 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 1030495 = 1545743) B1545743
theorem B1030523 : Blo 1028606 1030523 := bstep (se 1 (by rfl) ⟨772892, by rfl⟩ : syracuseStep 1030523 = 1545785) B1545785
theorem B1030575 : Blo 1028606 1030575 := bstep (se 1 (by rfl) ⟨772931, by rfl⟩ : syracuseStep 1030575 = 1545863) B1545863
theorem B1653167 : Blo 1028606 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B1030599 : Blo 1028606 1030599 := bstep (se 1 (by rfl) ⟨772949, by rfl⟩ : syracuseStep 1030599 = 1545899) B1545899
theorem B1030619 : Blo 1028606 1030619 := bstep (se 1 (by rfl) ⟨772964, by rfl⟩ : syracuseStep 1030619 = 1545929) B1545929
theorem B5224985 : Blo 1028606 5224985 := bstep (se 2 (by rfl) ⟨1959369, by rfl⟩ : syracuseStep 5224985 = 3918739) B3918739
theorem B1030695 : Blo 1028606 1030695 := bstep (se 1 (by rfl) ⟨773021, by rfl⟩ : syracuseStep 1030695 = 1546043) B1546043
theorem B1030735 : Blo 1028606 1030735 := bstep (se 1 (by rfl) ⟨773051, by rfl⟩ : syracuseStep 1030735 = 1546103) B1546103
theorem B1030751 : Blo 1028606 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B1030779 : Blo 1028606 1030779 := bstep (se 1 (by rfl) ⟨773084, by rfl⟩ : syracuseStep 1030779 = 1546169) B1546169
theorem B1030831 : Blo 1028606 1030831 := bstep (se 1 (by rfl) ⟨773123, by rfl⟩ : syracuseStep 1030831 = 1546247) B1546247
theorem B1030855 : Blo 1028606 1030855 := bstep (se 1 (by rfl) ⟨773141, by rfl⟩ : syracuseStep 1030855 = 1546283) B1546283
theorem B2603735 : Blo 1028606 2603735 := bstep (se 1 (by rfl) ⟨1952801, by rfl⟩ : syracuseStep 2603735 = 3905603) B3905603
theorem B1030875 : Blo 1028606 1030875 := bstep (se 1 (by rfl) ⟨773156, by rfl⟩ : syracuseStep 1030875 = 1546313) B1546313
theorem B1030951 : Blo 1028606 1030951 := bstep (se 1 (by rfl) ⟨773213, by rfl⟩ : syracuseStep 1030951 = 1546427) B1546427
theorem B1653577 : Blo 1028606 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B1030991 : Blo 1028606 1030991 := bstep (se 1 (by rfl) ⟨773243, by rfl⟩ : syracuseStep 1030991 = 1546487) B1546487
theorem B1031007 : Blo 1028606 1031007 := bstep (se 1 (by rfl) ⟨773255, by rfl⟩ : syracuseStep 1031007 = 1546511) B1546511
theorem B1031035 : Blo 1028606 1031035 := bstep (se 1 (by rfl) ⟨773276, by rfl⟩ : syracuseStep 1031035 = 1546553) B1546553
theorem B1031087 : Blo 1028606 1031087 := bstep (se 1 (by rfl) ⟨773315, by rfl⟩ : syracuseStep 1031087 = 1546631) B1546631
theorem B1031111 : Blo 1028606 1031111 := bstep (se 1 (by rfl) ⟨773333, by rfl⟩ : syracuseStep 1031111 = 1546667) B1546667
theorem B1031131 : Blo 1028606 1031131 := bstep (se 1 (by rfl) ⟨773348, by rfl⟩ : syracuseStep 1031131 = 1546697) B1546697
theorem B1031207 : Blo 1028606 1031207 := bstep (se 1 (by rfl) ⟨773405, by rfl⟩ : syracuseStep 1031207 = 1546811) B1546811
theorem B2604089 : Blo 1028606 2604089 := bstep (se 2 (by rfl) ⟨976533, by rfl⟩ : syracuseStep 2604089 = 1953067) B1953067
theorem B1031247 : Blo 1028606 1031247 := bstep (se 1 (by rfl) ⟨773435, by rfl⟩ : syracuseStep 1031247 = 1546871) B1546871
theorem B1031263 : Blo 1028606 1031263 := bstep (se 1 (by rfl) ⟨773447, by rfl⟩ : syracuseStep 1031263 = 1546895) B1546895
theorem B1031291 : Blo 1028606 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B1031343 : Blo 1028606 1031343 := bstep (se 1 (by rfl) ⟨773507, by rfl⟩ : syracuseStep 1031343 = 1547015) B1547015
theorem B1031367 : Blo 1028606 1031367 := bstep (se 1 (by rfl) ⟨773525, by rfl⟩ : syracuseStep 1031367 = 1547051) B1547051
theorem B1031387 : Blo 1028606 1031387 := bstep (se 1 (by rfl) ⟨773540, by rfl⟩ : syracuseStep 1031387 = 1547081) B1547081
theorem B1031463 : Blo 1028606 1031463 := bstep (se 1 (by rfl) ⟨773597, by rfl⟩ : syracuseStep 1031463 = 1547195) B1547195
theorem B1031503 : Blo 1028606 1031503 := bstep (se 1 (by rfl) ⟨773627, by rfl⟩ : syracuseStep 1031503 = 1547255) B1547255
theorem B1031519 : Blo 1028606 1031519 := bstep (se 1 (by rfl) ⟨773639, by rfl⟩ : syracuseStep 1031519 = 1547279) B1547279
theorem B1031547 : Blo 1028606 1031547 := bstep (se 1 (by rfl) ⟨773660, by rfl⟩ : syracuseStep 1031547 = 1547321) B1547321
theorem B1031599 : Blo 1028606 1031599 := bstep (se 1 (by rfl) ⟨773699, by rfl⟩ : syracuseStep 1031599 = 1547399) B1547399
theorem B1031623 : Blo 1028606 1031623 := bstep (se 1 (by rfl) ⟨773717, by rfl⟩ : syracuseStep 1031623 = 1547435) B1547435
theorem B1031643 : Blo 1028606 1031643 := bstep (se 1 (by rfl) ⟨773732, by rfl⟩ : syracuseStep 1031643 = 1547465) B1547465
theorem B3718619 : Blo 1028606 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B1031719 : Blo 1028606 1031719 := bstep (se 1 (by rfl) ⟨773789, by rfl⟩ : syracuseStep 1031719 = 1547579) B1547579
theorem B3915323 : Blo 1028606 3915323 := bstep (se 1 (by rfl) ⟨2936492, by rfl⟩ : syracuseStep 3915323 = 5872985) B5872985
theorem B1031759 : Blo 1028606 1031759 := bstep (se 1 (by rfl) ⟨773819, by rfl⟩ : syracuseStep 1031759 = 1547639) B1547639
theorem B1031775 : Blo 1028606 1031775 := bstep (se 1 (by rfl) ⟨773831, by rfl⟩ : syracuseStep 1031775 = 1547663) B1547663
theorem B1031803 : Blo 1028606 1031803 := bstep (se 1 (by rfl) ⟨773852, by rfl⟩ : syracuseStep 1031803 = 1547705) B1547705
theorem B1031855 : Blo 1028606 1031855 := bstep (se 1 (by rfl) ⟨773891, by rfl⟩ : syracuseStep 1031855 = 1547783) B1547783
theorem B1031879 : Blo 1028606 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B1031899 : Blo 1028606 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B11747105 : Blo 1028606 11747105 := bstep (se 2 (by rfl) ⟨4405164, by rfl⟩ : syracuseStep 11747105 = 8810329) B8810329
theorem B1031975 : Blo 1028606 1031975 := bstep (se 1 (by rfl) ⟨773981, by rfl⟩ : syracuseStep 1031975 = 1547963) B1547963
theorem B7061315 : Blo 1028606 7061315 := bstep (se 1 (by rfl) ⟨5295986, by rfl⟩ : syracuseStep 7061315 = 10591973) B10591973
theorem B1032015 : Blo 1028606 1032015 := bstep (se 1 (by rfl) ⟨774011, by rfl⟩ : syracuseStep 1032015 = 1548023) B1548023
theorem B1032031 : Blo 1028606 1032031 := bstep (se 1 (by rfl) ⟨774023, by rfl⟩ : syracuseStep 1032031 = 1548047) B1548047
theorem B1032059 : Blo 1028606 1032059 := bstep (se 1 (by rfl) ⟨774044, by rfl⟩ : syracuseStep 1032059 = 1548089) B1548089
theorem B1032111 : Blo 1028606 1032111 := bstep (se 1 (by rfl) ⟨774083, by rfl⟩ : syracuseStep 1032111 = 1548167) B1548167
theorem B1032135 : Blo 1028606 1032135 := bstep (se 1 (by rfl) ⟨774101, by rfl⟩ : syracuseStep 1032135 = 1548203) B1548203
theorem B1032155 : Blo 1028606 1032155 := bstep (se 1 (by rfl) ⟨774116, by rfl⟩ : syracuseStep 1032155 = 1548233) B1548233
theorem B5292047 : Blo 1028606 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B1032231 : Blo 1028606 1032231 := bstep (se 1 (by rfl) ⟨774173, by rfl⟩ : syracuseStep 1032231 = 1548347) B1548347
theorem B91439165 : Blo 1028606 91439165 := bstep (se 3 (by rfl) ⟨17144843, by rfl⟩ : syracuseStep 91439165 = 34289687) B34289687
theorem B1032271 : Blo 1028606 1032271 := bstep (se 1 (by rfl) ⟨774203, by rfl⟩ : syracuseStep 1032271 = 1548407) B1548407
theorem B1032287 : Blo 1028606 1032287 := bstep (se 1 (by rfl) ⟨774215, by rfl⟩ : syracuseStep 1032287 = 1548431) B1548431
theorem B1032315 : Blo 1028606 1032315 := bstep (se 1 (by rfl) ⟨774236, by rfl⟩ : syracuseStep 1032315 = 1548473) B1548473
theorem B1032367 : Blo 1028606 1032367 := bstep (se 1 (by rfl) ⟨774275, by rfl⟩ : syracuseStep 1032367 = 1548551) B1548551
theorem B1032391 : Blo 1028606 1032391 := bstep (se 1 (by rfl) ⟨774293, by rfl⟩ : syracuseStep 1032391 = 1548587) B1548587
theorem B1032411 : Blo 1028606 1032411 := bstep (se 1 (by rfl) ⟨774308, by rfl⟩ : syracuseStep 1032411 = 1548617) B1548617
theorem B1032487 : Blo 1028606 1032487 := bstep (se 1 (by rfl) ⟨774365, by rfl⟩ : syracuseStep 1032487 = 1548731) B1548731
theorem B1032527 : Blo 1028606 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B1032543 : Blo 1028606 1032543 := bstep (se 1 (by rfl) ⟨774407, by rfl⟩ : syracuseStep 1032543 = 1548815) B1548815
theorem B1032571 : Blo 1028606 1032571 := bstep (se 1 (by rfl) ⟨774428, by rfl⟩ : syracuseStep 1032571 = 1548857) B1548857
theorem B2474369 : Blo 1028606 2474369 := bstep (se 2 (by rfl) ⟨927888, by rfl⟩ : syracuseStep 2474369 = 1855777) B1855777
theorem B4178807 : Blo 1028606 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B43402291 : Blo 1028606 43402291 := bstep (se 1 (by rfl) ⟨32551718, by rfl⟩ : syracuseStep 43402291 = 65103437) B65103437
theorem B2606327 : Blo 1028606 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B2475407 : Blo 1028606 2475407 := bstep (se 1 (by rfl) ⟨1856555, by rfl⟩ : syracuseStep 2475407 = 3713111) B3713111
theorem B7423397 : Blo 1028606 7423397 := bstep (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) B1391887
theorem B1885627 : Blo 1028606 1885627 := bstep (se 1 (by rfl) ⟨1414220, by rfl⟩ : syracuseStep 1885627 = 2828441) B2828441
theorem B3720953 : Blo 1028606 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B2934863 : Blo 1028606 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B3918071 : Blo 1028606 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B6605185 : Blo 1028606 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B2607815 : Blo 1028606 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B1100719 : Blo 1028606 1100719 := bstep (se 1 (by rfl) ⟨825539, by rfl⟩ : syracuseStep 1100719 = 1651079) B1651079
theorem B2476975 : Blo 1028606 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B10210277 : Blo 1028606 10210277 := bstep (se 4 (by rfl) ⟨957213, by rfl⟩ : syracuseStep 10210277 = 1914427) B1914427
theorem B2935865 : Blo 1028606 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B3919043 : Blo 1028606 3919043 := bstep (se 1 (by rfl) ⟨2939282, by rfl⟩ : syracuseStep 3919043 = 5878565) B5878565
theorem B14830937 : Blo 1028606 14830937 := bstep (se 2 (by rfl) ⟨5561601, by rfl⟩ : syracuseStep 14830937 = 11123203) B11123203
theorem B1101151 : Blo 1028606 1101151 := bstep (se 1 (by rfl) ⟨825863, by rfl⟩ : syracuseStep 1101151 = 1651727) B1651727
theorem B2346383 : Blo 1028606 2346383 := bstep (se 1 (by rfl) ⟨1759787, by rfl⟩ : syracuseStep 2346383 = 3519575) B3519575
theorem B60182003 : Blo 1028606 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B3296801 : Blo 1028606 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B3919499 : Blo 1028606 3919499 := bstep (se 1 (by rfl) ⟨2939624, by rfl⟩ : syracuseStep 3919499 = 5879249) B5879249
theorem B2346695 : Blo 1028606 2346695 := bstep (se 1 (by rfl) ⟨1760021, by rfl⟩ : syracuseStep 2346695 = 3520043) B3520043
theorem B2608969 : Blo 1028606 2608969 := bstep (se 2 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 2608969 = 1956727) B1956727
theorem B3919711 : Blo 1028606 3919711 := bstep (se 1 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 3919711 = 5879567) B5879567
theorem B4181921 : Blo 1028606 4181921 := bstep (se 2 (by rfl) ⟨1568220, by rfl⟩ : syracuseStep 4181921 = 3136441) B3136441
theorem B27545507 : Blo 1028606 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B3297199 : Blo 1028606 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B1953811 : Blo 1028606 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B1954039 : Blo 1028606 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B2314601 : Blo 1028606 2314601 := bstep (se 2 (by rfl) ⟨867975, by rfl⟩ : syracuseStep 2314601 = 1735951) B1735951
theorem B1954343 : Blo 1028606 1954343 := bstep (se 1 (by rfl) ⟨1465757, by rfl⟩ : syracuseStep 1954343 = 2931515) B2931515
theorem B1102415 : Blo 1028606 1102415 := bstep (se 1 (by rfl) ⟨826811, by rfl⟩ : syracuseStep 1102415 = 1653623) B1653623
theorem B1856123 : Blo 1028606 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B5952211 : Blo 1028606 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B3920669 : Blo 1028606 3920669 := bstep (se 3 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 3920669 = 1470251) B1470251
theorem B2610103 : Blo 1028606 2610103 := bstep (se 1 (by rfl) ⟨1957577, by rfl⟩ : syracuseStep 2610103 = 3915155) B3915155
theorem B2315195 : Blo 1028606 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B2315321 : Blo 1028606 2315321 := bstep (se 2 (by rfl) ⟨868245, by rfl⟩ : syracuseStep 2315321 = 1736491) B1736491
theorem B2315663 : Blo 1028606 2315663 := bstep (se 1 (by rfl) ⟨1736747, by rfl⟩ : syracuseStep 2315663 = 3473495) B3473495
theorem B2315987 : Blo 1028606 2315987 := bstep (se 1 (by rfl) ⟨1736990, by rfl⟩ : syracuseStep 2315987 = 3473981) B3473981
theorem B1955657 : Blo 1028606 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B6608749 : Blo 1028606 6608749 := bstep (se 3 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 6608749 = 2478281) B2478281
theorem B11720861 : Blo 1028606 11720861 := bstep (se 3 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 11720861 = 4395323) B4395323
theorem B1956089 : Blo 1028606 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B2611561 : Blo 1028606 2611561 := bstep (se 2 (by rfl) ⟨979335, by rfl⟩ : syracuseStep 2611561 = 1958671) B1958671
theorem B11917721 : Blo 1028606 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2611835 : Blo 1028606 2611835 := bstep (se 1 (by rfl) ⟨1958876, by rfl⟩ : syracuseStep 2611835 = 3917753) B3917753
theorem B2316923 : Blo 1028606 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B6609593 : Blo 1028606 6609593 := bstep (se 2 (by rfl) ⟨2478597, by rfl⟩ : syracuseStep 6609593 = 4957195) B4957195
theorem B2939591 : Blo 1028606 2939591 := bstep (se 1 (by rfl) ⟨2204693, by rfl⟩ : syracuseStep 2939591 = 4409387) B4409387
theorem B2317049 : Blo 1028606 2317049 := bstep (se 2 (by rfl) ⟨868893, by rfl⟩ : syracuseStep 2317049 = 1737787) B1737787
theorem B7527397 : Blo 1028606 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B2317319 : Blo 1028606 2317319 := bstep (se 1 (by rfl) ⟨1737989, by rfl⟩ : syracuseStep 2317319 = 3475979) B3475979
theorem B2317391 : Blo 1028606 2317391 := bstep (se 1 (by rfl) ⟨1738043, by rfl⟩ : syracuseStep 2317391 = 3476087) B3476087
theorem B2088107 : Blo 1028606 2088107 := bstep (se 1 (by rfl) ⟨1566080, by rfl⟩ : syracuseStep 2088107 = 3132161) B3132161
theorem B2088335 : Blo 1028606 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B2317787 : Blo 1028606 2317787 := bstep (se 1 (by rfl) ⟨1738340, by rfl⟩ : syracuseStep 2317787 = 3476681) B3476681
theorem B3300851 : Blo 1028606 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B1302095 : Blo 1028606 1302095 := bstep (se 1 (by rfl) ⟨976571, by rfl⟩ : syracuseStep 1302095 = 1953143) B1953143
theorem B28171909 : Blo 1028606 28171909 := bstep (se 4 (by rfl) ⟨2641116, by rfl⟩ : syracuseStep 28171909 = 5282233) B5282233
theorem B3301003 : Blo 1028606 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B1957547 : Blo 1028606 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B2318255 : Blo 1028606 2318255 := bstep (se 1 (by rfl) ⟨1738691, by rfl⟩ : syracuseStep 2318255 = 3477383) B3477383
theorem B7528477 : Blo 1028606 7528477 := bstep (se 3 (by rfl) ⟨1411589, by rfl⟩ : syracuseStep 7528477 = 2823179) B2823179
theorem B1957927 : Blo 1028606 1957927 := bstep (se 1 (by rfl) ⟨1468445, by rfl⟩ : syracuseStep 1957927 = 2936891) B2936891
theorem B15065149 : Blo 1028606 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B2318507 : Blo 1028606 2318507 := bstep (se 1 (by rfl) ⟨1738880, by rfl⟩ : syracuseStep 2318507 = 3477761) B3477761
theorem B1958087 : Blo 1028606 1958087 := bstep (se 1 (by rfl) ⟨1468565, by rfl⟩ : syracuseStep 1958087 = 2937131) B2937131
theorem B7823627 : Blo 1028606 7823627 := bstep (se 1 (by rfl) ⟨5867720, by rfl⟩ : syracuseStep 7823627 = 11735441) B11735441
theorem B2613647 : Blo 1028606 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B1860175 : Blo 1028606 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B1237627 : Blo 1028606 1237627 := bstep (se 1 (by rfl) ⟨928220, by rfl⟩ : syracuseStep 1237627 = 1856441) B1856441
theorem B2319047 : Blo 1028606 2319047 := bstep (se 1 (by rfl) ⟨1739285, by rfl⟩ : syracuseStep 2319047 = 3478571) B3478571
theorem B1303391 : Blo 1028606 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B11723777 : Blo 1028606 11723777 := bstep (se 2 (by rfl) ⟨4396416, by rfl⟩ : syracuseStep 11723777 = 8792833) B8792833
theorem B1959241 : Blo 1028606 1959241 := bstep (se 2 (by rfl) ⟨734715, by rfl⟩ : syracuseStep 1959241 = 1469431) B1469431
theorem B2319911 : Blo 1028606 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B31712867 : Blo 1028606 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B7825085 : Blo 1028606 7825085 := bstep (se 3 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 7825085 = 2934407) B2934407
theorem B2320235 : Blo 1028606 2320235 := bstep (se 1 (by rfl) ⟨1740176, by rfl⟩ : syracuseStep 2320235 = 3480353) B3480353
theorem B2320289 : Blo 1028606 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B1566683 : Blo 1028606 1566683 := bstep (se 1 (by rfl) ⟨1175012, by rfl⟩ : syracuseStep 1566683 = 2350025) B2350025
theorem B9922661 : Blo 1028606 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B7825571 : Blo 1028606 7825571 := bstep (se 1 (by rfl) ⟨5869178, by rfl⟩ : syracuseStep 7825571 = 11738357) B11738357
theorem B2320631 : Blo 1028606 2320631 := bstep (se 1 (by rfl) ⟨1740473, by rfl⟩ : syracuseStep 2320631 = 3480947) B3480947
theorem B3303823 : Blo 1028606 3303823 := bstep (se 1 (by rfl) ⟨2477867, by rfl⟩ : syracuseStep 3303823 = 4955735) B4955735
theorem B2091577 : Blo 1028606 2091577 := bstep (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) B1568683
theorem B2321225 : Blo 1028606 2321225 := bstep (se 2 (by rfl) ⟨870459, by rfl⟩ : syracuseStep 2321225 = 1740919) B1740919
theorem B1043323 : Blo 1028606 1043323 := bstep (se 1 (by rfl) ⟨782492, by rfl⟩ : syracuseStep 1043323 = 1564985) B1564985
theorem B1764359 : Blo 1028606 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B1764713 : Blo 1028606 1764713 := bstep (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) B1323535
theorem B1306039 : Blo 1028606 1306039 := bstep (se 1 (by rfl) ⟨979529, by rfl⟩ : syracuseStep 1306039 = 1959059) B1959059
theorem B6614567 : Blo 1028606 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B2322017 : Blo 1028606 2322017 := bstep (se 2 (by rfl) ⟨870756, by rfl⟩ : syracuseStep 2322017 = 1741513) B1741513
theorem B17592227 : Blo 1028606 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B2322359 : Blo 1028606 2322359 := bstep (se 1 (by rfl) ⟨1741769, by rfl⟩ : syracuseStep 2322359 = 3483539) B3483539
theorem B5566553 : Blo 1028606 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B3305719 : Blo 1028606 3305719 := bstep (se 1 (by rfl) ⟨2479289, by rfl⟩ : syracuseStep 3305719 = 4958579) B4958579
theorem B2322953 : Blo 1028606 2322953 := bstep (se 2 (by rfl) ⟨871107, by rfl⟩ : syracuseStep 2322953 = 1742215) B1742215
theorem B7828001 : Blo 1028606 7828001 := bstep (se 2 (by rfl) ⟨2935500, by rfl⟩ : syracuseStep 7828001 = 5871001) B5871001
theorem B3764875 : Blo 1028606 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B1766137 : Blo 1028606 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B2323295 : Blo 1028606 2323295 := bstep (se 1 (by rfl) ⟨1742471, by rfl⟩ : syracuseStep 2323295 = 3484943) B3484943
theorem B5863211 : Blo 1028606 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B15038905 : Blo 1028606 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B11729609 : Blo 1028606 11729609 := bstep (se 2 (by rfl) ⟨4398603, by rfl⟩ : syracuseStep 11729609 = 8797207) B8797207
theorem B5208785 : Blo 1028606 5208785 := bstep (se 2 (by rfl) ⟨1953294, by rfl⟩ : syracuseStep 5208785 = 3906589) B3906589
theorem B5569235 : Blo 1028606 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B15858767 : Blo 1028606 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B3472631 : Blo 1028606 3472631 := bstep (se 1 (by rfl) ⟨2604473, by rfl⟩ : syracuseStep 3472631 = 5208947) B5208947
theorem B1736201 : Blo 1028606 1736201 := bstep (se 2 (by rfl) ⟨651075, by rfl⟩ : syracuseStep 1736201 = 1302151) B1302151
theorem B3472955 : Blo 1028606 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B1736363 : Blo 1028606 1736363 := bstep (se 1 (by rfl) ⟨1302272, by rfl⟩ : syracuseStep 1736363 = 2604545) B2604545
theorem B3473225 : Blo 1028606 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B20086865 : Blo 1028606 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B2785871 : Blo 1028606 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B3474143 : Blo 1028606 3474143 := bstep (se 1 (by rfl) ⟨2605607, by rfl⟩ : syracuseStep 3474143 = 5211215) B5211215
theorem B16712507 : Blo 1028606 16712507 := bstep (se 1 (by rfl) ⟨12534380, by rfl⟩ : syracuseStep 16712507 = 25068761) B25068761
theorem B1737551 : Blo 1028606 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B4948931 : Blo 1028606 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B3474575 : Blo 1028606 3474575 := bstep (se 1 (by rfl) ⟨2605931, by rfl⟩ : syracuseStep 3474575 = 5211863) B5211863
theorem B1738543 : Blo 1028606 1738543 := bstep (se 1 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 1738543 = 2607815) B2607815
theorem B3475709 : Blo 1028606 3475709 := bstep (se 3 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 3475709 = 1303391) B1303391
theorem B2197867 : Blo 1028606 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2787947 : Blo 1028606 2787947 := bstep (se 1 (by rfl) ⟨2090960, by rfl⟩ : syracuseStep 2787947 = 4181921) B4181921
theorem B7539479 : Blo 1028606 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1543067 : Blo 1028606 1543067 := bstep (se 1 (by rfl) ⟨1157300, by rfl⟩ : syracuseStep 1543067 = 2314601) B2314601
theorem B3476519 : Blo 1028606 3476519 := bstep (se 1 (by rfl) ⟨2607389, by rfl⟩ : syracuseStep 3476519 = 5214779) B5214779
theorem B1543463 : Blo 1028606 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B1543547 : Blo 1028606 1543547 := bstep (se 1 (by rfl) ⟨1157660, by rfl⟩ : syracuseStep 1543547 = 2315321) B2315321
theorem B7441793 : Blo 1028606 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B2788769 : Blo 1028606 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B3476951 : Blo 1028606 3476951 := bstep (se 1 (by rfl) ⟨2607713, by rfl⟩ : syracuseStep 3476951 = 5215427) B5215427
theorem B1543673 : Blo 1028606 1543673 := bstep (se 2 (by rfl) ⟨578877, by rfl⟩ : syracuseStep 1543673 = 1157755) B1157755
theorem B8359433 : Blo 1028606 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B2199097 : Blo 1028606 2199097 := bstep (se 2 (by rfl) ⟨824661, by rfl⟩ : syracuseStep 2199097 = 1649323) B1649323
theorem B1543775 : Blo 1028606 1543775 := bstep (se 1 (by rfl) ⟨1157831, by rfl⟩ : syracuseStep 1543775 = 2315663) B2315663
theorem B1543991 : Blo 1028606 1543991 := bstep (se 1 (by rfl) ⟨1157993, by rfl⟩ : syracuseStep 1543991 = 2315987) B2315987
theorem B1544297 : Blo 1028606 1544297 := bstep (se 2 (by rfl) ⟨579111, by rfl⟩ : syracuseStep 1544297 = 1158223) B1158223
theorem B8819077 : Blo 1028606 8819077 := bstep (se 4 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 8819077 = 1653577) B1653577
theorem B1544615 : Blo 1028606 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B1741223 : Blo 1028606 1741223 := bstep (se 1 (by rfl) ⟨1305917, by rfl⟩ : syracuseStep 1741223 = 2611835) B2611835
theorem B1544699 : Blo 1028606 1544699 := bstep (se 1 (by rfl) ⟨1158524, by rfl⟩ : syracuseStep 1544699 = 2317049) B2317049
theorem B24154685 : Blo 1028606 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1741385 : Blo 1028606 1741385 := bstep (se 2 (by rfl) ⟨653019, by rfl⟩ : syracuseStep 1741385 = 1306039) B1306039
theorem B1544825 : Blo 1028606 1544825 := bstep (se 2 (by rfl) ⟨579309, by rfl⟩ : syracuseStep 1544825 = 1158619) B1158619
theorem B1544879 : Blo 1028606 1544879 := bstep (se 1 (by rfl) ⟨1158659, by rfl⟩ : syracuseStep 1544879 = 2317319) B2317319
theorem B1544927 : Blo 1028606 1544927 := bstep (se 1 (by rfl) ⟨1158695, by rfl⟩ : syracuseStep 1544927 = 2317391) B2317391
theorem B4756333 : Blo 1028606 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B5870501 : Blo 1028606 5870501 := bstep (se 4 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 5870501 = 1100719) B1100719
theorem B22287307 : Blo 1028606 22287307 := bstep (se 1 (by rfl) ⟨16715480, by rfl⟩ : syracuseStep 22287307 = 33430961) B33430961
theorem B13210573 : Blo 1028606 13210573 := bstep (se 3 (by rfl) ⟨2476982, by rfl⟩ : syracuseStep 13210573 = 4953965) B4953965
theorem B4396007 : Blo 1028606 4396007 := bstep (se 1 (by rfl) ⟨3297005, by rfl⟩ : syracuseStep 4396007 = 6594011) B6594011
theorem B1545191 : Blo 1028606 1545191 := bstep (se 1 (by rfl) ⟨1158893, by rfl⟩ : syracuseStep 1545191 = 2317787) B2317787
theorem B2200567 : Blo 1028606 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B3478625 : Blo 1028606 3478625 := bstep (se 2 (by rfl) ⟨1304484, by rfl⟩ : syracuseStep 3478625 = 2608969) B2608969
theorem B4396265 : Blo 1028606 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B1545449 : Blo 1028606 1545449 := bstep (se 2 (by rfl) ⟨579543, by rfl⟩ : syracuseStep 1545449 = 1159087) B1159087
theorem B1545503 : Blo 1028606 1545503 := bstep (se 1 (by rfl) ⟨1159127, by rfl⟩ : syracuseStep 1545503 = 2318255) B2318255
theorem B5575979 : Blo 1028606 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B1545671 : Blo 1028606 1545671 := bstep (se 1 (by rfl) ⟨1159253, by rfl⟩ : syracuseStep 1545671 = 2318507) B2318507
theorem B5215751 : Blo 1028606 5215751 := bstep (se 1 (by rfl) ⟨3911813, by rfl⟩ : syracuseStep 5215751 = 7823627) B7823627
theorem B1742431 : Blo 1028606 1742431 := bstep (se 1 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 1742431 = 2613647) B2613647
theorem B231478885 : Blo 1028606 231478885 := bstep (se 4 (by rfl) ⟨21701145, by rfl⟩ : syracuseStep 231478885 = 43402291) B43402291
theorem B5576327 : Blo 1028606 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B1546025 : Blo 1028606 1546025 := bstep (se 2 (by rfl) ⟨579759, by rfl⟩ : syracuseStep 1546025 = 1159519) B1159519
theorem B1546031 : Blo 1028606 1546031 := bstep (se 1 (by rfl) ⟨1159523, by rfl⟩ : syracuseStep 1546031 = 2319047) B2319047
theorem B5216237 : Blo 1028606 5216237 := bstep (se 3 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 5216237 = 1956089) B1956089
theorem B144644237 : Blo 1028606 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B5019833 : Blo 1028606 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B1546505 : Blo 1028606 1546505 := bstep (se 2 (by rfl) ⟨579939, by rfl⟩ : syracuseStep 1546505 = 1159879) B1159879
theorem B1546607 : Blo 1028606 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B21141911 : Blo 1028606 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B3479975 : Blo 1028606 3479975 := bstep (se 1 (by rfl) ⟨2609981, by rfl⟩ : syracuseStep 3479975 = 5219963) B5219963
theorem B5216723 : Blo 1028606 5216723 := bstep (se 1 (by rfl) ⟨3912542, by rfl⟩ : syracuseStep 5216723 = 7825085) B7825085
theorem B3349055 : Blo 1028606 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B1546823 : Blo 1028606 1546823 := bstep (se 1 (by rfl) ⟨1160117, by rfl⟩ : syracuseStep 1546823 = 2320235) B2320235
theorem B3480137 : Blo 1028606 3480137 := bstep (se 2 (by rfl) ⟨1305051, by rfl⟩ : syracuseStep 3480137 = 2610103) B2610103
theorem B4397647 : Blo 1028606 4397647 := bstep (se 1 (by rfl) ⟨3298235, by rfl⟩ : syracuseStep 4397647 = 6596471) B6596471
theorem B1546859 : Blo 1028606 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B5217047 : Blo 1028606 5217047 := bstep (se 1 (by rfl) ⟨3912785, by rfl⟩ : syracuseStep 5217047 = 7825571) B7825571
theorem B1547087 : Blo 1028606 1547087 := bstep (se 1 (by rfl) ⟨1160315, by rfl⟩ : syracuseStep 1547087 = 2320631) B2320631
theorem B1547483 : Blo 1028606 1547483 := bstep (se 1 (by rfl) ⟨1160612, by rfl⟩ : syracuseStep 1547483 = 2321225) B2321225
theorem B1547657 : Blo 1028606 1547657 := bstep (se 2 (by rfl) ⟨580371, by rfl⟩ : syracuseStep 1547657 = 1160743) B1160743
theorem B2203129 : Blo 1028606 2203129 := bstep (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) B1652347
theorem B1548011 : Blo 1028606 1548011 := bstep (se 1 (by rfl) ⟨1161008, by rfl⟩ : syracuseStep 1548011 = 2322017) B2322017
theorem B1548239 : Blo 1028606 1548239 := bstep (se 1 (by rfl) ⟨1161179, by rfl⟩ : syracuseStep 1548239 = 2322359) B2322359
theorem B3711035 : Blo 1028606 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B3481811 : Blo 1028606 3481811 := bstep (se 1 (by rfl) ⟨2611358, by rfl⟩ : syracuseStep 3481811 = 5222717) B5222717
theorem B1548635 : Blo 1028606 1548635 := bstep (se 1 (by rfl) ⟨1161476, by rfl⟩ : syracuseStep 1548635 = 2322953) B2322953
theorem B5218667 : Blo 1028606 5218667 := bstep (se 1 (by rfl) ⟨3914000, by rfl⟩ : syracuseStep 5218667 = 7828001) B7828001
theorem B15868385 : Blo 1028606 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B3482081 : Blo 1028606 3482081 := bstep (se 2 (by rfl) ⟨1305780, by rfl⟩ : syracuseStep 3482081 = 2611561) B2611561
theorem B1548863 : Blo 1028606 1548863 := bstep (se 1 (by rfl) ⟨1161647, by rfl⟩ : syracuseStep 1548863 = 2323295) B2323295
theorem B9904855 : Blo 1028606 9904855 := bstep (se 1 (by rfl) ⟨7428641, by rfl⟩ : syracuseStep 9904855 = 14857283) B14857283
theorem B17605349 : Blo 1028606 17605349 := bstep (se 4 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 17605349 = 3301003) B3301003
theorem B3908807 : Blo 1028606 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B10036529 : Blo 1028606 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B3483323 : Blo 1028606 3483323 := bstep (se 1 (by rfl) ⟨2612492, by rfl⟩ : syracuseStep 3483323 = 5224985) B5224985
theorem B5220125 : Blo 1028606 5220125 := bstep (se 3 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 5220125 = 1957547) B1957547
theorem B3712823 : Blo 1028606 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B37562545 : Blo 1028606 37562545 := bstep (se 2 (by rfl) ⟨14085954, by rfl⟩ : syracuseStep 37562545 = 28171909) B28171909
theorem B1157467 : Blo 1028606 1157467 := bstep (se 1 (by rfl) ⟨868100, by rfl⟩ : syracuseStep 1157467 = 1736201) B1736201
theorem B1157575 : Blo 1028606 1157575 := bstep (se 1 (by rfl) ⟨868181, by rfl⟩ : syracuseStep 1157575 = 1736363) B1736363
theorem B10037969 : Blo 1028606 10037969 := bstep (se 2 (by rfl) ⟨3764238, by rfl⟩ : syracuseStep 10037969 = 7528477) B7528477
theorem B6269719 : Blo 1028606 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B1157935 : Blo 1028606 1157935 := bstep (se 1 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 1157935 = 1736903) B1736903
theorem B243837773 : Blo 1028606 243837773 := bstep (se 3 (by rfl) ⟨45719582, by rfl⟩ : syracuseStep 243837773 = 91439165) B91439165
theorem B1158043 : Blo 1028606 1158043 := bstep (se 1 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 1158043 = 1737065) B1737065
theorem B1649579 : Blo 1028606 1649579 := bstep (se 1 (by rfl) ⟨1237184, by rfl⟩ : syracuseStep 1649579 = 2474369) B2474369
theorem B5876651 : Blo 1028606 5876651 := bstep (se 1 (by rfl) ⟨4407488, by rfl⟩ : syracuseStep 5876651 = 8814977) B8814977
theorem B5024987 : Blo 1028606 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B1158439 : Blo 1028606 1158439 := bstep (se 1 (by rfl) ⟨868829, by rfl⟩ : syracuseStep 1158439 = 1737659) B1737659
theorem B1158511 : Blo 1028606 1158511 := bstep (se 1 (by rfl) ⟨868883, by rfl⟩ : syracuseStep 1158511 = 1737767) B1737767
theorem B1650169 : Blo 1028606 1650169 := bstep (se 2 (by rfl) ⟨618813, by rfl⟩ : syracuseStep 1650169 = 1237627) B1237627
theorem B1158727 : Blo 1028606 1158727 := bstep (se 1 (by rfl) ⟨869045, by rfl⟩ : syracuseStep 1158727 = 1738091) B1738091
theorem B3911435 : Blo 1028606 3911435 := bstep (se 1 (by rfl) ⟨2933576, by rfl⟩ : syracuseStep 3911435 = 5867153) B5867153
theorem B8794169 : Blo 1028606 8794169 := bstep (se 2 (by rfl) ⟨3297813, by rfl⟩ : syracuseStep 8794169 = 6595627) B6595627
theorem B33402941 : Blo 1028606 33402941 := bstep (se 3 (by rfl) ⟨6263051, by rfl⟩ : syracuseStep 33402941 = 12526103) B12526103
theorem B1159591 : Blo 1028606 1159591 := bstep (se 1 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 1159591 = 1739387) B1739387
theorem B5878291 : Blo 1028606 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B1028671 : Blo 1028606 1028671 := bstep (se 1 (by rfl) ⟨771503, by rfl⟩ : syracuseStep 1028671 = 1543007) B1543007
theorem B1028679 : Blo 1028606 1028679 := bstep (se 1 (by rfl) ⟨771509, by rfl⟩ : syracuseStep 1028679 = 1543019) B1543019
theorem B1028831 : Blo 1028606 1028831 := bstep (se 1 (by rfl) ⟨771623, by rfl⟩ : syracuseStep 1028831 = 1543247) B1543247
theorem B1028911 : Blo 1028606 1028911 := bstep (se 1 (by rfl) ⟨771683, by rfl⟩ : syracuseStep 1028911 = 1543367) B1543367
theorem B1029019 : Blo 1028606 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B1029071 : Blo 1028606 1029071 := bstep (se 1 (by rfl) ⟨771803, by rfl⟩ : syracuseStep 1029071 = 1543607) B1543607
theorem B1029095 : Blo 1028606 1029095 := bstep (se 1 (by rfl) ⟨771821, by rfl⟩ : syracuseStep 1029095 = 1543643) B1543643
theorem B1160167 : Blo 1028606 1160167 := bstep (se 1 (by rfl) ⟨870125, by rfl⟩ : syracuseStep 1160167 = 1740251) B1740251
theorem B40121335 : Blo 1028606 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B3912695 : Blo 1028606 3912695 := bstep (se 1 (by rfl) ⟨2934521, by rfl⟩ : syracuseStep 3912695 = 5869043) B5869043
theorem B18363671 : Blo 1028606 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B1029407 : Blo 1028606 1029407 := bstep (se 1 (by rfl) ⟨772055, by rfl⟩ : syracuseStep 1029407 = 1544111) B1544111
theorem B1029467 : Blo 1028606 1029467 := bstep (se 1 (by rfl) ⟨772100, by rfl⟩ : syracuseStep 1029467 = 1544201) B1544201
theorem B1029487 : Blo 1028606 1029487 := bstep (se 1 (by rfl) ⟨772115, by rfl⟩ : syracuseStep 1029487 = 1544231) B1544231
theorem B3716513 : Blo 1028606 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B1029543 : Blo 1028606 1029543 := bstep (se 1 (by rfl) ⟨772157, by rfl⟩ : syracuseStep 1029543 = 1544315) B1544315
theorem B1029627 : Blo 1028606 1029627 := bstep (se 1 (by rfl) ⟨772220, by rfl⟩ : syracuseStep 1029627 = 1544441) B1544441
theorem B1029695 : Blo 1028606 1029695 := bstep (se 1 (by rfl) ⟨772271, by rfl⟩ : syracuseStep 1029695 = 1544543) B1544543
theorem B1029703 : Blo 1028606 1029703 := bstep (se 1 (by rfl) ⟨772277, by rfl⟩ : syracuseStep 1029703 = 1544555) B1544555
theorem B1029855 : Blo 1028606 1029855 := bstep (se 1 (by rfl) ⟨772391, by rfl⟩ : syracuseStep 1029855 = 1544783) B1544783
theorem B1029935 : Blo 1028606 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B4405097 : Blo 1028606 4405097 := bstep (se 2 (by rfl) ⟨1651911, by rfl⟩ : syracuseStep 4405097 = 3303823) B3303823
theorem B1030043 : Blo 1028606 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B1030095 : Blo 1028606 1030095 := bstep (se 1 (by rfl) ⟨772571, by rfl⟩ : syracuseStep 1030095 = 1545143) B1545143
theorem B22263781 : Blo 1028606 22263781 := bstep (se 4 (by rfl) ⟨2087229, by rfl⟩ : syracuseStep 22263781 = 4174459) B4174459
theorem B1030119 : Blo 1028606 1030119 := bstep (se 1 (by rfl) ⟨772589, by rfl⟩ : syracuseStep 1030119 = 1545179) B1545179
theorem B1030431 : Blo 1028606 1030431 := bstep (se 1 (by rfl) ⟨772823, by rfl⟩ : syracuseStep 1030431 = 1545647) B1545647
theorem B35633459 : Blo 1028606 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B1030491 : Blo 1028606 1030491 := bstep (se 1 (by rfl) ⟨772868, by rfl⟩ : syracuseStep 1030491 = 1545737) B1545737
theorem B1030511 : Blo 1028606 1030511 := bstep (se 1 (by rfl) ⟨772883, by rfl⟩ : syracuseStep 1030511 = 1545767) B1545767
theorem B6601085 : Blo 1028606 6601085 := bstep (se 3 (by rfl) ⟨1237703, by rfl⟩ : syracuseStep 6601085 = 2475407) B2475407
theorem B1030567 : Blo 1028606 1030567 := bstep (se 1 (by rfl) ⟨772925, by rfl⟩ : syracuseStep 1030567 = 1545851) B1545851
theorem B1030651 : Blo 1028606 1030651 := bstep (se 1 (by rfl) ⟨772988, by rfl⟩ : syracuseStep 1030651 = 1545977) B1545977
theorem B1030719 : Blo 1028606 1030719 := bstep (se 1 (by rfl) ⟨773039, by rfl⟩ : syracuseStep 1030719 = 1546079) B1546079
theorem B3717695 : Blo 1028606 3717695 := bstep (se 1 (by rfl) ⟨2788271, by rfl⟩ : syracuseStep 3717695 = 5576543) B5576543
theorem B1030727 : Blo 1028606 1030727 := bstep (se 1 (by rfl) ⟨773045, by rfl⟩ : syracuseStep 1030727 = 1546091) B1546091
theorem B1030879 : Blo 1028606 1030879 := bstep (se 1 (by rfl) ⟨773159, by rfl⟩ : syracuseStep 1030879 = 1546319) B1546319
theorem B7813907 : Blo 1028606 7813907 := bstep (se 1 (by rfl) ⟨5860430, by rfl⟩ : syracuseStep 7813907 = 11720861) B11720861
theorem B1030959 : Blo 1028606 1030959 := bstep (se 1 (by rfl) ⟨773219, by rfl⟩ : syracuseStep 1030959 = 1546439) B1546439
theorem B3914639 : Blo 1028606 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B6273935 : Blo 1028606 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1031067 : Blo 1028606 1031067 := bstep (se 1 (by rfl) ⟨773300, by rfl⟩ : syracuseStep 1031067 = 1546601) B1546601
theorem B2603947 : Blo 1028606 2603947 := bstep (se 1 (by rfl) ⟨1952960, by rfl⟩ : syracuseStep 2603947 = 3905921) B3905921
theorem B7945147 : Blo 1028606 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1031119 : Blo 1028606 1031119 := bstep (se 1 (by rfl) ⟨773339, by rfl⟩ : syracuseStep 1031119 = 1546679) B1546679
theorem B1031143 : Blo 1028606 1031143 := bstep (se 1 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 1031143 = 1546715) B1546715
theorem B2472947 : Blo 1028606 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B4406395 : Blo 1028606 4406395 := bstep (se 1 (by rfl) ⟨3304796, by rfl⟩ : syracuseStep 4406395 = 6609593) B6609593
theorem B2604251 : Blo 1028606 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B1031455 : Blo 1028606 1031455 := bstep (se 1 (by rfl) ⟨773591, by rfl⟩ : syracuseStep 1031455 = 1547183) B1547183
theorem B5225795 : Blo 1028606 5225795 := bstep (se 1 (by rfl) ⟨3919346, by rfl⟩ : syracuseStep 5225795 = 7838693) B7838693
theorem B1031515 : Blo 1028606 1031515 := bstep (se 1 (by rfl) ⟨773636, by rfl⟩ : syracuseStep 1031515 = 1547273) B1547273
theorem B2604383 : Blo 1028606 2604383 := bstep (se 1 (by rfl) ⟨1953287, by rfl⟩ : syracuseStep 2604383 = 3906575) B3906575
theorem B1031535 : Blo 1028606 1031535 := bstep (se 1 (by rfl) ⟨773651, by rfl⟩ : syracuseStep 1031535 = 1547303) B1547303
theorem B1031591 : Blo 1028606 1031591 := bstep (se 1 (by rfl) ⟨773693, by rfl⟩ : syracuseStep 1031591 = 1547387) B1547387
theorem B1392071 : Blo 1028606 1392071 := bstep (se 1 (by rfl) ⟨1044053, by rfl⟩ : syracuseStep 1392071 = 2088107) B2088107
theorem B5291513 : Blo 1028606 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B1031675 : Blo 1028606 1031675 := bstep (se 1 (by rfl) ⟨773756, by rfl⟩ : syracuseStep 1031675 = 1547513) B1547513
theorem B1031743 : Blo 1028606 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B1031751 : Blo 1028606 1031751 := bstep (se 1 (by rfl) ⟨773813, by rfl⟩ : syracuseStep 1031751 = 1547627) B1547627
theorem B1392223 : Blo 1028606 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B1031903 : Blo 1028606 1031903 := bstep (se 1 (by rfl) ⟨773927, by rfl⟩ : syracuseStep 1031903 = 1547855) B1547855
theorem B7520003 : Blo 1028606 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B5226281 : Blo 1028606 5226281 := bstep (se 2 (by rfl) ⟨1959855, by rfl⟩ : syracuseStep 5226281 = 3919711) B3919711
theorem B1031983 : Blo 1028606 1031983 := bstep (se 1 (by rfl) ⟨773987, by rfl⟩ : syracuseStep 1031983 = 1547975) B1547975
theorem B1032091 : Blo 1028606 1032091 := bstep (se 1 (by rfl) ⟨774068, by rfl⟩ : syracuseStep 1032091 = 1548137) B1548137
theorem B1032143 : Blo 1028606 1032143 := bstep (se 1 (by rfl) ⟨774107, by rfl⟩ : syracuseStep 1032143 = 1548215) B1548215
theorem B1032167 : Blo 1028606 1032167 := bstep (se 1 (by rfl) ⟨774125, by rfl⟩ : syracuseStep 1032167 = 1548251) B1548251
theorem B2605081 : Blo 1028606 2605081 := bstep (se 2 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 2605081 = 1953811) B1953811
theorem B1032479 : Blo 1028606 1032479 := bstep (se 1 (by rfl) ⟨774359, by rfl⟩ : syracuseStep 1032479 = 1548719) B1548719
theorem B2605385 : Blo 1028606 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B4407625 : Blo 1028606 4407625 := bstep (se 2 (by rfl) ⟨1652859, by rfl⟩ : syracuseStep 4407625 = 3305719) B3305719
theorem B1032539 : Blo 1028606 1032539 := bstep (se 1 (by rfl) ⟨774404, by rfl⟩ : syracuseStep 1032539 = 1548809) B1548809
theorem B1032559 : Blo 1028606 1032559 := bstep (se 1 (by rfl) ⟨774419, by rfl⟩ : syracuseStep 1032559 = 1548839) B1548839
theorem B7815851 : Blo 1028606 7815851 := bstep (se 1 (by rfl) ⟨5861888, by rfl⟩ : syracuseStep 7815851 = 11723777) B11723777
theorem B3523295 : Blo 1028606 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B4408445 : Blo 1028606 4408445 := bstep (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) B1653167
theorem B2933975 : Blo 1028606 2933975 := bstep (se 1 (by rfl) ⟨2200481, by rfl⟩ : syracuseStep 2933975 = 4400963) B4400963
theorem B3917099 : Blo 1028606 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B1099207 : Blo 1028606 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B6604649 : Blo 1028606 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B11716487 : Blo 1028606 11716487 := bstep (se 1 (by rfl) ⟨8787365, by rfl⟩ : syracuseStep 11716487 = 17574731) B17574731
theorem B3295417 : Blo 1028606 3295417 := bstep (se 2 (by rfl) ⟨1235781, by rfl⟩ : syracuseStep 3295417 = 2471563) B2471563
theorem B4409711 : Blo 1028606 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B2608271 : Blo 1028606 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B1101223 : Blo 1028606 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B2936857 : Blo 1028606 2936857 := bstep (se 2 (by rfl) ⟨1101321, by rfl⟩ : syracuseStep 2936857 = 2202643) B2202643
theorem B1102043 : Blo 1028606 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B7819739 : Blo 1028606 7819739 := bstep (se 1 (by rfl) ⟨5864804, by rfl⟩ : syracuseStep 7819739 = 11729609) B11729609
theorem B10572511 : Blo 1028606 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B2315087 : Blo 1028606 2315087 := bstep (se 1 (by rfl) ⟨1736315, by rfl⟩ : syracuseStep 2315087 = 3472631) B3472631
theorem B18830173 : Blo 1028606 18830173 := bstep (se 3 (by rfl) ⟨3530657, by rfl⟩ : syracuseStep 18830173 = 7061315) B7061315
theorem B2479079 : Blo 1028606 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B2315303 : Blo 1028606 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B2610215 : Blo 1028606 2610215 := bstep (se 1 (by rfl) ⟨1957661, by rfl⟩ : syracuseStep 2610215 = 3915323) B3915323
theorem B2315483 : Blo 1028606 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B3528031 : Blo 1028606 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B2610569 : Blo 1028606 2610569 := bstep (se 2 (by rfl) ⟨978963, by rfl⟩ : syracuseStep 2610569 = 1957927) B1957927
theorem B2315681 : Blo 1028606 2315681 := bstep (se 2 (by rfl) ⟨868380, by rfl⟩ : syracuseStep 2315681 = 1736761) B1736761
theorem B2316239 : Blo 1028606 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B2480233 : Blo 1028606 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B2316617 : Blo 1028606 2316617 := bstep (se 2 (by rfl) ⟨868731, by rfl⟩ : syracuseStep 2316617 = 1737463) B1737463
theorem B2316635 : Blo 1028606 2316635 := bstep (se 1 (by rfl) ⟨1737476, by rfl⟩ : syracuseStep 2316635 = 3474953) B3474953
theorem B2480635 : Blo 1028606 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B3299903 : Blo 1028606 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B2939465 : Blo 1028606 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B1956575 : Blo 1028606 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B2612047 : Blo 1028606 2612047 := bstep (se 1 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 2612047 = 3918071) B3918071
theorem B2939773 : Blo 1028606 2939773 := bstep (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) B1102415
theorem B2317211 : Blo 1028606 2317211 := bstep (se 1 (by rfl) ⟨1737908, by rfl⟩ : syracuseStep 2317211 = 3475817) B3475817
theorem B2317409 : Blo 1028606 2317409 := bstep (se 2 (by rfl) ⟨869028, by rfl⟩ : syracuseStep 2317409 = 1738057) B1738057
theorem B2612321 : Blo 1028606 2612321 := bstep (se 2 (by rfl) ⟨979620, by rfl⟩ : syracuseStep 2612321 = 1959241) B1959241
theorem B2514169 : Blo 1028606 2514169 := bstep (se 2 (by rfl) ⟨942813, by rfl⟩ : syracuseStep 2514169 = 1885627) B1885627
theorem B2317607 : Blo 1028606 2317607 := bstep (se 1 (by rfl) ⟨1738205, by rfl⟩ : syracuseStep 2317607 = 3476411) B3476411
theorem B6806851 : Blo 1028606 6806851 := bstep (se 1 (by rfl) ⟨5105138, by rfl⟩ : syracuseStep 6806851 = 10210277) B10210277
theorem B1465723 : Blo 1028606 1465723 := bstep (se 1 (by rfl) ⟨1099292, by rfl⟩ : syracuseStep 1465723 = 2198585) B2198585
theorem B24141199 : Blo 1028606 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B2612695 : Blo 1028606 2612695 := bstep (se 1 (by rfl) ⟨1959521, by rfl⟩ : syracuseStep 2612695 = 3919043) B3919043
theorem B9887291 : Blo 1028606 9887291 := bstep (se 1 (by rfl) ⟨7415468, by rfl⟩ : syracuseStep 9887291 = 14830937) B14830937
theorem B1564255 : Blo 1028606 1564255 := bstep (se 1 (by rfl) ⟨1173191, by rfl⟩ : syracuseStep 1564255 = 2346383) B2346383
theorem B1465951 : Blo 1028606 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B2317985 : Blo 1028606 2317985 := bstep (se 2 (by rfl) ⟨869244, by rfl⟩ : syracuseStep 2317985 = 1738489) B1738489
theorem B2612999 : Blo 1028606 2612999 := bstep (se 1 (by rfl) ⟨1959749, by rfl⟩ : syracuseStep 2612999 = 3919499) B3919499
theorem B2514695 : Blo 1028606 2514695 := bstep (se 1 (by rfl) ⟨1886021, by rfl⟩ : syracuseStep 2514695 = 3772043) B3772043
theorem B1564463 : Blo 1028606 1564463 := bstep (se 1 (by rfl) ⟨1173347, by rfl⟩ : syracuseStep 1564463 = 2346695) B2346695
theorem B2318345 : Blo 1028606 2318345 := bstep (se 2 (by rfl) ⟨869379, by rfl⟩ : syracuseStep 2318345 = 1738759) B1738759
theorem B1302895 : Blo 1028606 1302895 := bstep (se 1 (by rfl) ⟨977171, by rfl⟩ : syracuseStep 1302895 = 1954343) B1954343
theorem B1237415 : Blo 1028606 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B2318759 : Blo 1028606 2318759 := bstep (se 1 (by rfl) ⟨1739069, by rfl⟩ : syracuseStep 2318759 = 3478139) B3478139
theorem B8806913 : Blo 1028606 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B2318867 : Blo 1028606 2318867 := bstep (se 1 (by rfl) ⟨1739150, by rfl⟩ : syracuseStep 2318867 = 3478301) B3478301
theorem B2613779 : Blo 1028606 2613779 := bstep (se 1 (by rfl) ⟨1960334, by rfl⟩ : syracuseStep 2613779 = 3920669) B3920669
theorem B2318921 : Blo 1028606 2318921 := bstep (se 2 (by rfl) ⟨869595, by rfl⟩ : syracuseStep 2318921 = 1739191) B1739191
theorem B3302363 : Blo 1028606 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B2319335 : Blo 1028606 2319335 := bstep (se 1 (by rfl) ⟨1739501, by rfl⟩ : syracuseStep 2319335 = 3479003) B3479003
theorem B31745125 : Blo 1028606 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1303771 : Blo 1028606 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B3302633 : Blo 1028606 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B2319713 : Blo 1028606 2319713 := bstep (se 2 (by rfl) ⟨869892, by rfl⟩ : syracuseStep 2319713 = 1739785) B1739785
theorem B2319803 : Blo 1028606 2319803 := bstep (se 1 (by rfl) ⟨1739852, by rfl⟩ : syracuseStep 2319803 = 3479705) B3479705
theorem B2319929 : Blo 1028606 2319929 := bstep (se 2 (by rfl) ⟨869973, by rfl⟩ : syracuseStep 2319929 = 1739947) B1739947
theorem B1468201 : Blo 1028606 1468201 := bstep (se 2 (by rfl) ⟨550575, by rfl⟩ : syracuseStep 1468201 = 1101151) B1101151
theorem B1959727 : Blo 1028606 1959727 := bstep (se 1 (by rfl) ⟨1469795, by rfl⟩ : syracuseStep 1959727 = 2939591) B2939591
theorem B5564389 : Blo 1028606 5564389 := bstep (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) B1043323
theorem B2320595 : Blo 1028606 2320595 := bstep (se 1 (by rfl) ⟨1740446, by rfl⟩ : syracuseStep 2320595 = 3480893) B3480893
theorem B2320649 : Blo 1028606 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B2320865 : Blo 1028606 2320865 := bstep (se 2 (by rfl) ⟨870324, by rfl⟩ : syracuseStep 2320865 = 1740649) B1740649
theorem B7039475 : Blo 1028606 7039475 := bstep (se 1 (by rfl) ⟨5279606, by rfl⟩ : syracuseStep 7039475 = 10559213) B10559213
theorem B2583035 : Blo 1028606 2583035 := bstep (se 1 (by rfl) ⟨1937276, by rfl⟩ : syracuseStep 2583035 = 3874553) B3874553
theorem B2321171 : Blo 1028606 2321171 := bstep (se 1 (by rfl) ⟨1740878, by rfl⟩ : syracuseStep 2321171 = 3481757) B3481757
theorem B1305391 : Blo 1028606 1305391 := bstep (se 1 (by rfl) ⟨979043, by rfl⟩ : syracuseStep 1305391 = 1958087) B1958087
theorem B2321531 : Blo 1028606 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B1469659 : Blo 1028606 1469659 := bstep (se 1 (by rfl) ⟨1102244, by rfl⟩ : syracuseStep 1469659 = 2204489) B2204489
theorem B2321657 : Blo 1028606 2321657 := bstep (se 2 (by rfl) ⟨870621, by rfl⟩ : syracuseStep 2321657 = 1741243) B1741243
theorem B2321801 : Blo 1028606 2321801 := bstep (se 2 (by rfl) ⟨870675, by rfl⟩ : syracuseStep 2321801 = 1741351) B1741351
theorem B5860795 : Blo 1028606 5860795 := bstep (se 1 (by rfl) ⟨4395596, by rfl⟩ : syracuseStep 5860795 = 8791193) B8791193
theorem B2321927 : Blo 1028606 2321927 := bstep (se 1 (by rfl) ⟨1741445, by rfl⟩ : syracuseStep 2321927 = 3482891) B3482891
theorem B2354849 : Blo 1028606 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B2322107 : Blo 1028606 2322107 := bstep (se 1 (by rfl) ⟨1741580, by rfl⟩ : syracuseStep 2322107 = 3483161) B3483161
theorem B3305195 : Blo 1028606 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B4943663 : Blo 1028606 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B2322233 : Blo 1028606 2322233 := bstep (se 2 (by rfl) ⟨870837, by rfl⟩ : syracuseStep 2322233 = 1741675) B1741675
theorem B1044455 : Blo 1028606 1044455 := bstep (se 1 (by rfl) ⟨783341, by rfl⟩ : syracuseStep 1044455 = 1566683) B1566683
theorem B7827515 : Blo 1028606 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B6615107 : Blo 1028606 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B2322863 : Blo 1028606 2322863 := bstep (se 1 (by rfl) ⟨1742147, by rfl⟩ : syracuseStep 2322863 = 3484295) B3484295
theorem B2322899 : Blo 1028606 2322899 := bstep (se 1 (by rfl) ⟨1742174, by rfl⟩ : syracuseStep 2322899 = 3484349) B3484349
theorem B2323007 : Blo 1028606 2323007 := bstep (se 1 (by rfl) ⟨1742255, by rfl⟩ : syracuseStep 2323007 = 3484511) B3484511
theorem B2323115 : Blo 1028606 2323115 := bstep (se 1 (by rfl) ⟨1742336, by rfl⟩ : syracuseStep 2323115 = 3484673) B3484673
theorem B1176239 : Blo 1028606 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B5862253 : Blo 1028606 5862253 := bstep (se 3 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 5862253 = 2198345) B2198345
theorem B1176475 : Blo 1028606 1176475 := bstep (se 1 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 1176475 = 1764713) B1764713
theorem B26375219 : Blo 1028606 26375219 := bstep (se 1 (by rfl) ⟨19781414, by rfl⟩ : syracuseStep 26375219 = 39562829) B39562829
theorem B8811665 : Blo 1028606 8811665 := bstep (se 2 (by rfl) ⟨3304374, by rfl⟩ : syracuseStep 8811665 = 6608749) B6608749
theorem B11728151 : Blo 1028606 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B13202783 : Blo 1028606 13202783 := bstep (se 1 (by rfl) ⟨9902087, by rfl⟩ : syracuseStep 13202783 = 19804175) B19804175
theorem B3306847 : Blo 1028606 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B5207489 : Blo 1028606 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B7828973 : Blo 1028606 7828973 := bstep (se 3 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 7828973 = 2935865) B2935865
theorem B20051873 : Blo 1028606 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B9533371 : Blo 1028606 9533371 := bstep (se 1 (by rfl) ⟨7150028, by rfl⟩ : syracuseStep 9533371 = 14300057) B14300057
theorem B3307655 : Blo 1028606 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B4946471 : Blo 1028606 4946471 := bstep (se 1 (by rfl) ⟨3709853, by rfl⟩ : syracuseStep 4946471 = 7419707) B7419707
theorem B3472253 : Blo 1028606 3472253 := bstep (se 3 (by rfl) ⟨651047, by rfl⟩ : syracuseStep 3472253 = 1302095) B1302095
theorem B3472523 : Blo 1028606 3472523 := bstep (se 1 (by rfl) ⟨2604392, by rfl⟩ : syracuseStep 3472523 = 5208785) B5208785
theorem B1735823 : Blo 1028606 1735823 := bstep (se 1 (by rfl) ⟨1301867, by rfl⟩ : syracuseStep 1735823 = 2603735) B2603735
theorem B5864669 : Blo 1028606 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B1736059 : Blo 1028606 1736059 := bstep (se 1 (by rfl) ⟨1302044, by rfl⟩ : syracuseStep 1736059 = 2604089) B2604089
theorem B7831403 : Blo 1028606 7831403 := bstep (se 1 (by rfl) ⟨5873552, by rfl⟩ : syracuseStep 7831403 = 11747105) B11747105
theorem B3473441 : Blo 1028606 3473441 := bstep (se 2 (by rfl) ⟨1302540, by rfl⟩ : syracuseStep 3473441 = 2605081) B2605081
theorem B9896093 : Blo 1028606 9896093 := bstep (se 3 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 9896093 = 3711035) B3711035
theorem B1736923 : Blo 1028606 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B5210567 : Blo 1028606 5210567 := bstep (se 1 (by rfl) ⟨3907925, by rfl⟩ : syracuseStep 5210567 = 7815851) B7815851
theorem B1737193 : Blo 1028606 1737193 := bstep (se 2 (by rfl) ⟨651447, by rfl⟩ : syracuseStep 1737193 = 1302895) B1302895
theorem B11141671 : Blo 1028606 11141671 := bstep (se 1 (by rfl) ⟨8356253, by rfl⟩ : syracuseStep 11141671 = 16712507) B16712507
theorem B13206473 : Blo 1028606 13206473 := bstep (se 2 (by rfl) ⟨4952427, by rfl⟩ : syracuseStep 13206473 = 9904855) B9904855
theorem B1738361 : Blo 1028606 1738361 := bstep (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) B1303771
theorem B1738847 : Blo 1028606 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B5572955 : Blo 1028606 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B4393889 : Blo 1028606 4393889 := bstep (se 2 (by rfl) ⟨1647708, by rfl⟩ : syracuseStep 4393889 = 3295417) B3295417
theorem B5213159 : Blo 1028606 5213159 := bstep (se 1 (by rfl) ⟨3909869, by rfl⟩ : syracuseStep 5213159 = 7819739) B7819739
theorem B1543289 : Blo 1028606 1543289 := bstep (se 2 (by rfl) ⟨578733, by rfl⟩ : syracuseStep 1543289 = 1157467) B1157467
theorem B1543391 : Blo 1028606 1543391 := bstep (se 1 (by rfl) ⟨1157543, by rfl⟩ : syracuseStep 1543391 = 2315087) B2315087
theorem B1543433 : Blo 1028606 1543433 := bstep (se 2 (by rfl) ⟨578787, by rfl⟩ : syracuseStep 1543433 = 1157575) B1157575
theorem B1543535 : Blo 1028606 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B1740143 : Blo 1028606 1740143 := bstep (se 1 (by rfl) ⟨1305107, by rfl⟩ : syracuseStep 1740143 = 2610215) B2610215
theorem B1543655 : Blo 1028606 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B1740379 : Blo 1028606 1740379 := bstep (se 1 (by rfl) ⟨1305284, by rfl⟩ : syracuseStep 1740379 = 2610569) B2610569
theorem B1543787 : Blo 1028606 1543787 := bstep (se 1 (by rfl) ⟨1157840, by rfl⟩ : syracuseStep 1543787 = 2315681) B2315681
theorem B3477167 : Blo 1028606 3477167 := bstep (se 1 (by rfl) ⟨2607875, by rfl⟩ : syracuseStep 3477167 = 5215751) B5215751
theorem B8359625 : Blo 1028606 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B1543913 : Blo 1028606 1543913 := bstep (se 2 (by rfl) ⟨578967, by rfl⟩ : syracuseStep 1543913 = 1157935) B1157935
theorem B1740521 : Blo 1028606 1740521 := bstep (se 2 (by rfl) ⟨652695, by rfl⟩ : syracuseStep 1740521 = 1305391) B1305391
theorem B1544057 : Blo 1028606 1544057 := bstep (se 2 (by rfl) ⟨579021, by rfl⟩ : syracuseStep 1544057 = 1158043) B1158043
theorem B1544159 : Blo 1028606 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B3477491 : Blo 1028606 3477491 := bstep (se 1 (by rfl) ⟨2608118, by rfl⟩ : syracuseStep 3477491 = 5216237) B5216237
theorem B3346555 : Blo 1028606 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B1544411 : Blo 1028606 1544411 := bstep (se 1 (by rfl) ⟨1158308, by rfl⟩ : syracuseStep 1544411 = 2316617) B2316617
theorem B1544423 : Blo 1028606 1544423 := bstep (se 1 (by rfl) ⟨1158317, by rfl⟩ : syracuseStep 1544423 = 2316635) B2316635
theorem B14094607 : Blo 1028606 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B3477815 : Blo 1028606 3477815 := bstep (se 1 (by rfl) ⟨2608361, by rfl⟩ : syracuseStep 3477815 = 5216723) B5216723
theorem B2199935 : Blo 1028606 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B2232703 : Blo 1028606 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B1544585 : Blo 1028606 1544585 := bstep (se 2 (by rfl) ⟨579219, by rfl⟩ : syracuseStep 1544585 = 1158439) B1158439
theorem B1544681 : Blo 1028606 1544681 := bstep (se 2 (by rfl) ⟨579255, by rfl⟩ : syracuseStep 1544681 = 1158511) B1158511
theorem B3478031 : Blo 1028606 3478031 := bstep (se 1 (by rfl) ⟨2608523, by rfl⟩ : syracuseStep 3478031 = 5217047) B5217047
theorem B1544807 : Blo 1028606 1544807 := bstep (se 1 (by rfl) ⟨1158605, by rfl⟩ : syracuseStep 1544807 = 2317211) B2317211
theorem B2200225 : Blo 1028606 2200225 := bstep (se 2 (by rfl) ⟨825084, by rfl⟩ : syracuseStep 2200225 = 1650169) B1650169
theorem B1544939 : Blo 1028606 1544939 := bstep (se 1 (by rfl) ⟨1158704, by rfl⟩ : syracuseStep 1544939 = 2317409) B2317409
theorem B1741547 : Blo 1028606 1741547 := bstep (se 1 (by rfl) ⟨1306160, by rfl⟩ : syracuseStep 1741547 = 2612321) B2612321
theorem B1544969 : Blo 1028606 1544969 := bstep (se 2 (by rfl) ⟨579363, by rfl⟩ : syracuseStep 1544969 = 1158727) B1158727
theorem B1545071 : Blo 1028606 1545071 := bstep (se 1 (by rfl) ⟨1158803, by rfl⟩ : syracuseStep 1545071 = 2317607) B2317607
theorem B6591527 : Blo 1028606 6591527 := bstep (se 1 (by rfl) ⟨4943645, by rfl⟩ : syracuseStep 6591527 = 9887291) B9887291
theorem B1545323 : Blo 1028606 1545323 := bstep (se 1 (by rfl) ⟨1158992, by rfl⟩ : syracuseStep 1545323 = 2317985) B2317985
theorem B1741999 : Blo 1028606 1741999 := bstep (se 1 (by rfl) ⟨1306499, by rfl⟩ : syracuseStep 1741999 = 2612999) B2612999
theorem B1545563 : Blo 1028606 1545563 := bstep (se 1 (by rfl) ⟨1159172, by rfl⟩ : syracuseStep 1545563 = 2318345) B2318345
theorem B3479111 : Blo 1028606 3479111 := bstep (se 1 (by rfl) ⟨2609333, by rfl⟩ : syracuseStep 3479111 = 5218667) B5218667
theorem B1545839 : Blo 1028606 1545839 := bstep (se 1 (by rfl) ⟨1159379, by rfl⟩ : syracuseStep 1545839 = 2318759) B2318759
theorem B5871275 : Blo 1028606 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B1545911 : Blo 1028606 1545911 := bstep (se 1 (by rfl) ⟨1159433, by rfl⟩ : syracuseStep 1545911 = 2318867) B2318867
theorem B1742519 : Blo 1028606 1742519 := bstep (se 1 (by rfl) ⟨1306889, by rfl⟩ : syracuseStep 1742519 = 2613779) B2613779
theorem B8820413 : Blo 1028606 8820413 := bstep (se 3 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 8820413 = 3307655) B3307655
theorem B1545947 : Blo 1028606 1545947 := bstep (se 1 (by rfl) ⟨1159460, by rfl⟩ : syracuseStep 1545947 = 2318921) B2318921
theorem B11736899 : Blo 1028606 11736899 := bstep (se 1 (by rfl) ⟨8802674, by rfl⟩ : syracuseStep 11736899 = 17605349) B17605349
theorem B1546121 : Blo 1028606 1546121 := bstep (se 2 (by rfl) ⟨579795, by rfl⟩ : syracuseStep 1546121 = 1159591) B1159591
theorem B2201575 : Blo 1028606 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B1546223 : Blo 1028606 1546223 := bstep (se 1 (by rfl) ⟨1159667, by rfl⟩ : syracuseStep 1546223 = 2319335) B2319335
theorem B7837721 : Blo 1028606 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B2201755 : Blo 1028606 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B6691019 : Blo 1028606 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B1546475 : Blo 1028606 1546475 := bstep (se 1 (by rfl) ⟨1159856, by rfl⟩ : syracuseStep 1546475 = 2319713) B2319713
theorem B1546535 : Blo 1028606 1546535 := bstep (se 1 (by rfl) ⟨1159901, by rfl⟩ : syracuseStep 1546535 = 2319803) B2319803
theorem B14096681 : Blo 1028606 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B1546619 : Blo 1028606 1546619 := bstep (se 1 (by rfl) ⟨1159964, by rfl⟩ : syracuseStep 1546619 = 2319929) B2319929
theorem B25106897 : Blo 1028606 25106897 := bstep (se 2 (by rfl) ⟨9415086, by rfl⟩ : syracuseStep 25106897 = 18830173) B18830173
theorem B3480083 : Blo 1028606 3480083 := bstep (se 1 (by rfl) ⟨2610062, by rfl⟩ : syracuseStep 3480083 = 5220125) B5220125
theorem B1546889 : Blo 1028606 1546889 := bstep (se 2 (by rfl) ⟨580083, by rfl⟩ : syracuseStep 1546889 = 1160167) B1160167
theorem B1547063 : Blo 1028606 1547063 := bstep (se 1 (by rfl) ⟨1160297, by rfl⟩ : syracuseStep 1547063 = 2320595) B2320595
theorem B1547099 : Blo 1028606 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1547243 : Blo 1028606 1547243 := bstep (se 1 (by rfl) ⟨1160432, by rfl⟩ : syracuseStep 1547243 = 2320865) B2320865
theorem B4692983 : Blo 1028606 4692983 := bstep (se 1 (by rfl) ⟨3519737, by rfl⟩ : syracuseStep 4692983 = 7039475) B7039475
theorem B6691979 : Blo 1028606 6691979 := bstep (se 1 (by rfl) ⟨5018984, by rfl⟩ : syracuseStep 6691979 = 10037969) B10037969
theorem B1547447 : Blo 1028606 1547447 := bstep (se 1 (by rfl) ⟨1160585, by rfl⟩ : syracuseStep 1547447 = 2321171) B2321171
theorem B5217533 : Blo 1028606 5217533 := bstep (se 3 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 5217533 = 1956575) B1956575
theorem B1547687 : Blo 1028606 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B3349991 : Blo 1028606 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1547771 : Blo 1028606 1547771 := bstep (se 1 (by rfl) ⟨1160828, by rfl⟩ : syracuseStep 1547771 = 2321657) B2321657
theorem B1547867 : Blo 1028606 1547867 := bstep (se 1 (by rfl) ⟨1160900, by rfl⟩ : syracuseStep 1547867 = 2321801) B2321801
theorem B1547951 : Blo 1028606 1547951 := bstep (se 1 (by rfl) ⟨1160963, by rfl⟩ : syracuseStep 1547951 = 2321927) B2321927
theorem B4398877 : Blo 1028606 4398877 := bstep (se 3 (by rfl) ⟨824789, by rfl⟩ : syracuseStep 4398877 = 1649579) B1649579
theorem B1548071 : Blo 1028606 1548071 := bstep (se 1 (by rfl) ⟨1161053, by rfl⟩ : syracuseStep 1548071 = 2322107) B2322107
theorem B2203463 : Blo 1028606 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B1548155 : Blo 1028606 1548155 := bstep (se 1 (by rfl) ⟨1161116, by rfl⟩ : syracuseStep 1548155 = 2322233) B2322233
theorem B5218343 : Blo 1028606 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B1548575 : Blo 1028606 1548575 := bstep (se 1 (by rfl) ⟨1161431, by rfl⟩ : syracuseStep 1548575 = 2322863) B2322863
theorem B1548599 : Blo 1028606 1548599 := bstep (se 1 (by rfl) ⟨1161449, by rfl⟩ : syracuseStep 1548599 = 2322899) B2322899
theorem B1548671 : Blo 1028606 1548671 := bstep (se 1 (by rfl) ⟨1161503, by rfl⟩ : syracuseStep 1548671 = 2323007) B2323007
theorem B1548743 : Blo 1028606 1548743 := bstep (se 1 (by rfl) ⟨1161557, by rfl⟩ : syracuseStep 1548743 = 2323115) B2323115
theorem B5874443 : Blo 1028606 5874443 := bstep (se 1 (by rfl) ⟨4405832, by rfl⟩ : syracuseStep 5874443 = 8811665) B8811665
theorem B5219315 : Blo 1028606 5219315 := bstep (se 1 (by rfl) ⟨3914486, by rfl⟩ : syracuseStep 5219315 = 7828973) B7828973
theorem B3482729 : Blo 1028606 3482729 := bstep (se 2 (by rfl) ⟨1306023, by rfl⟩ : syracuseStep 3482729 = 2612047) B2612047
theorem B3712189 : Blo 1028606 3712189 := bstep (se 3 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 3712189 = 1392071) B1392071
theorem B10593529 : Blo 1028606 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B5875193 : Blo 1028606 5875193 := bstep (se 2 (by rfl) ⟨2203197, by rfl⟩ : syracuseStep 5875193 = 4406395) B4406395
theorem B4400723 : Blo 1028606 4400723 := bstep (se 1 (by rfl) ⟨3300542, by rfl⟩ : syracuseStep 4400723 = 6601085) B6601085
theorem B3352225 : Blo 1028606 3352225 := bstep (se 2 (by rfl) ⟨1257084, by rfl⟩ : syracuseStep 3352225 = 2514169) B2514169
theorem B32188265 : Blo 1028606 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B3483593 : Blo 1028606 3483593 := bstep (se 2 (by rfl) ⟨1306347, by rfl⟩ : syracuseStep 3483593 = 2612695) B2612695
theorem B1648631 : Blo 1028606 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B1157215 : Blo 1028606 1157215 := bstep (se 1 (by rfl) ⟨867911, by rfl⟩ : syracuseStep 1157215 = 1735823) B1735823
theorem B3909779 : Blo 1028606 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B3483863 : Blo 1028606 3483863 := bstep (se 1 (by rfl) ⟨2612897, by rfl⟩ : syracuseStep 3483863 = 5225795) B5225795
theorem B3484187 : Blo 1028606 3484187 := bstep (se 1 (by rfl) ⟨2613140, by rfl⟩ : syracuseStep 3484187 = 5226281) B5226281
theorem B5220935 : Blo 1028606 5220935 := bstep (se 1 (by rfl) ⟨3915701, by rfl⟩ : syracuseStep 5220935 = 7831403) B7831403
theorem B5876833 : Blo 1028606 5876833 := bstep (se 2 (by rfl) ⟨2203812, by rfl⟩ : syracuseStep 5876833 = 4407625) B4407625
theorem B1158367 : Blo 1028606 1158367 := bstep (se 1 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 1158367 = 1737551) B1737551
theorem B4403099 : Blo 1028606 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B7810991 : Blo 1028606 7810991 := bstep (se 1 (by rfl) ⟨5858243, by rfl⟩ : syracuseStep 7810991 = 11716487) B11716487
theorem B5026319 : Blo 1028606 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1028711 : Blo 1028606 1028711 := bstep (se 1 (by rfl) ⟨771533, by rfl⟩ : syracuseStep 1028711 = 1543067) B1543067
theorem B1028975 : Blo 1028606 1028975 := bstep (se 1 (by rfl) ⟨771731, by rfl⟩ : syracuseStep 1028975 = 1543463) B1543463
theorem B1029031 : Blo 1028606 1029031 := bstep (se 1 (by rfl) ⟨771773, by rfl⟩ : syracuseStep 1029031 = 1543547) B1543547
theorem B4961195 : Blo 1028606 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B1029115 : Blo 1028606 1029115 := bstep (se 1 (by rfl) ⟨771836, by rfl⟩ : syracuseStep 1029115 = 1543673) B1543673
theorem B1029183 : Blo 1028606 1029183 := bstep (se 1 (by rfl) ⟨771887, by rfl⟩ : syracuseStep 1029183 = 1543775) B1543775
theorem B1029327 : Blo 1028606 1029327 := bstep (se 1 (by rfl) ⟨771995, by rfl⟩ : syracuseStep 1029327 = 1543991) B1543991
theorem B7419185 : Blo 1028606 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B1029531 : Blo 1028606 1029531 := bstep (se 1 (by rfl) ⟨772148, by rfl⟩ : syracuseStep 1029531 = 1544297) B1544297
theorem B50083393 : Blo 1028606 50083393 := bstep (se 2 (by rfl) ⟨18781272, by rfl⟩ : syracuseStep 50083393 = 37562545) B37562545
theorem B1029743 : Blo 1028606 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B1160815 : Blo 1028606 1160815 := bstep (se 1 (by rfl) ⟨870611, by rfl⟩ : syracuseStep 1160815 = 1741223) B1741223
theorem B1029799 : Blo 1028606 1029799 := bstep (se 1 (by rfl) ⟨772349, by rfl⟩ : syracuseStep 1029799 = 1544699) B1544699
theorem B16103123 : Blo 1028606 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B1160923 : Blo 1028606 1160923 := bstep (se 1 (by rfl) ⟨870692, by rfl⟩ : syracuseStep 1160923 = 1741385) B1741385
theorem B1029883 : Blo 1028606 1029883 := bstep (se 1 (by rfl) ⟨772412, by rfl⟩ : syracuseStep 1029883 = 1544825) B1544825
theorem B1029919 : Blo 1028606 1029919 := bstep (se 1 (by rfl) ⟨772439, by rfl⟩ : syracuseStep 1029919 = 1544879) B1544879
theorem B2930489 : Blo 1028606 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B1029951 : Blo 1028606 1029951 := bstep (se 1 (by rfl) ⟨772463, by rfl⟩ : syracuseStep 1029951 = 1544927) B1544927
theorem B3913667 : Blo 1028606 3913667 := bstep (se 1 (by rfl) ⟨2935250, by rfl⟩ : syracuseStep 3913667 = 5870501) B5870501
theorem B2930671 : Blo 1028606 2930671 := bstep (se 1 (by rfl) ⟨2198003, by rfl⟩ : syracuseStep 2930671 = 4396007) B4396007
theorem B1030127 : Blo 1028606 1030127 := bstep (se 1 (by rfl) ⟨772595, by rfl⟩ : syracuseStep 1030127 = 1545191) B1545191
theorem B1652719 : Blo 1028606 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B2930843 : Blo 1028606 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B1030299 : Blo 1028606 1030299 := bstep (se 1 (by rfl) ⟨772724, by rfl⟩ : syracuseStep 1030299 = 1545449) B1545449
theorem B1030335 : Blo 1028606 1030335 := bstep (se 1 (by rfl) ⟨772751, by rfl⟩ : syracuseStep 1030335 = 1545503) B1545503
theorem B1030447 : Blo 1028606 1030447 := bstep (se 1 (by rfl) ⟨772835, by rfl⟩ : syracuseStep 1030447 = 1545671) B1545671
theorem B3717551 : Blo 1028606 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B1030683 : Blo 1028606 1030683 := bstep (se 1 (by rfl) ⟨773012, by rfl⟩ : syracuseStep 1030683 = 1546025) B1546025
theorem B1030687 : Blo 1028606 1030687 := bstep (se 1 (by rfl) ⟨773015, by rfl⟩ : syracuseStep 1030687 = 1546031) B1546031
theorem B1031003 : Blo 1028606 1031003 := bstep (se 1 (by rfl) ⟨773252, by rfl⟩ : syracuseStep 1031003 = 1546505) B1546505
theorem B1031071 : Blo 1028606 1031071 := bstep (se 1 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 1031071 = 1546607) B1546607
theorem B1031215 : Blo 1028606 1031215 := bstep (se 1 (by rfl) ⟨773411, by rfl⟩ : syracuseStep 1031215 = 1546823) B1546823
theorem B1031239 : Blo 1028606 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B1031391 : Blo 1028606 1031391 := bstep (se 1 (by rfl) ⟨773543, by rfl⟩ : syracuseStep 1031391 = 1547087) B1547087
theorem B7814393 : Blo 1028606 7814393 := bstep (se 2 (by rfl) ⟨2930397, by rfl⟩ : syracuseStep 7814393 = 5860795) B5860795
theorem B2932129 : Blo 1028606 2932129 := bstep (se 2 (by rfl) ⟨1099548, by rfl⟩ : syracuseStep 2932129 = 2199097) B2199097
theorem B1031655 : Blo 1028606 1031655 := bstep (se 1 (by rfl) ⟨773741, by rfl⟩ : syracuseStep 1031655 = 1547483) B1547483
theorem B1031771 : Blo 1028606 1031771 := bstep (se 1 (by rfl) ⟨773828, by rfl⟩ : syracuseStep 1031771 = 1547657) B1547657
theorem B1032007 : Blo 1028606 1032007 := bstep (se 1 (by rfl) ⟨774005, by rfl⟩ : syracuseStep 1032007 = 1548011) B1548011
theorem B1032159 : Blo 1028606 1032159 := bstep (se 1 (by rfl) ⟨774119, by rfl⟩ : syracuseStep 1032159 = 1548239) B1548239
theorem B3915809 : Blo 1028606 3915809 := bstep (se 2 (by rfl) ⟨1468428, by rfl⟩ : syracuseStep 3915809 = 2936857) B2936857
theorem B1032423 : Blo 1028606 1032423 := bstep (se 1 (by rfl) ⟨774317, by rfl⟩ : syracuseStep 1032423 = 1548635) B1548635
theorem B1032575 : Blo 1028606 1032575 := bstep (se 1 (by rfl) ⟨774431, by rfl⟩ : syracuseStep 1032575 = 1548863) B1548863
theorem B2605871 : Blo 1028606 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B6341777 : Blo 1028606 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B7816337 : Blo 1028606 7816337 := bstep (se 2 (by rfl) ⟨2931126, by rfl⟩ : syracuseStep 7816337 = 5862253) B5862253
theorem B2475215 : Blo 1028606 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B17614097 : Blo 1028606 17614097 := bstep (se 2 (by rfl) ⟨6605286, by rfl⟩ : syracuseStep 17614097 = 13210573) B13210573
theorem B53495113 : Blo 1028606 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B2934089 : Blo 1028606 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B145212821 : Blo 1028606 145212821 := bstep (se 6 (by rfl) ⟨3403425, by rfl⟩ : syracuseStep 145212821 = 6806851) B6806851
theorem B9913853 : Blo 1028606 9913853 := bstep (se 3 (by rfl) ⟨1858847, by rfl⟩ : syracuseStep 9913853 = 3717695) B3717695
theorem B1722023 : Blo 1028606 1722023 := bstep (se 1 (by rfl) ⟨1291517, by rfl⟩ : syracuseStep 1722023 = 2583035) B2583035
theorem B4704041 : Blo 1028606 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B4409129 : Blo 1028606 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B3917767 : Blo 1028606 3917767 := bstep (se 1 (by rfl) ⟨2938325, by rfl⟩ : syracuseStep 3917767 = 5876651) B5876651
theorem B2607623 : Blo 1028606 2607623 := bstep (se 1 (by rfl) ⟨1955717, by rfl⟩ : syracuseStep 2607623 = 3911435) B3911435
theorem B3295775 : Blo 1028606 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B11750021 : Blo 1028606 11750021 := bstep (se 4 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 11750021 = 2203129) B2203129
theorem B22268627 : Blo 1028606 22268627 := bstep (se 1 (by rfl) ⟨16701470, by rfl⟩ : syracuseStep 22268627 = 33402941) B33402941
theorem B4410071 : Blo 1028606 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B26823413 : Blo 1028606 26823413 := bstep (se 5 (by rfl) ⟨1257347, by rfl⟩ : syracuseStep 26823413 = 2514695) B2514695
theorem B2608463 : Blo 1028606 2608463 := bstep (se 1 (by rfl) ⟨1956347, by rfl⟩ : syracuseStep 2608463 = 3912695) B3912695
theorem B17583479 : Blo 1028606 17583479 := bstep (se 1 (by rfl) ⟨13187609, by rfl⟩ : syracuseStep 17583479 = 26375219) B26375219
theorem B7818767 : Blo 1028606 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B12242447 : Blo 1028606 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B8801855 : Blo 1028606 8801855 := bstep (se 1 (by rfl) ⟨6601391, by rfl⟩ : syracuseStep 8801855 = 13202783) B13202783
theorem B2477675 : Blo 1028606 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B3919697 : Blo 1028606 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B2936731 : Blo 1028606 2936731 := bstep (se 1 (by rfl) ⟨2202548, by rfl⟩ : syracuseStep 2936731 = 4405097) B4405097
theorem B3297647 : Blo 1028606 3297647 := bstep (se 1 (by rfl) ⟨2473235, by rfl⟩ : syracuseStep 3297647 = 4946471) B4946471
theorem B2314745 : Blo 1028606 2314745 := bstep (se 2 (by rfl) ⟨868029, by rfl⟩ : syracuseStep 2314745 = 1736059) B1736059
theorem B1954297 : Blo 1028606 1954297 := bstep (se 2 (by rfl) ⟨732861, by rfl⟩ : syracuseStep 1954297 = 1465723) B1465723
theorem B2314835 : Blo 1028606 2314835 := bstep (se 1 (by rfl) ⟨1736126, by rfl⟩ : syracuseStep 2314835 = 3472253) B3472253
theorem B2609759 : Blo 1028606 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B4182623 : Blo 1028606 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B2315015 : Blo 1028606 2315015 := bstep (se 1 (by rfl) ⟨1736261, by rfl⟩ : syracuseStep 2315015 = 3472523) B3472523
theorem B2085673 : Blo 1028606 2085673 := bstep (se 2 (by rfl) ⟨782127, by rfl⟩ : syracuseStep 2085673 = 1564255) B1564255
theorem B1954601 : Blo 1028606 1954601 := bstep (se 2 (by rfl) ⟨732975, by rfl⟩ : syracuseStep 1954601 = 1465951) B1465951
theorem B1856297 : Blo 1028606 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B3527675 : Blo 1028606 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B13391243 : Blo 1028606 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B2316095 : Blo 1028606 2316095 := bstep (se 1 (by rfl) ⟨1737071, by rfl⟩ : syracuseStep 2316095 = 3474143) B3474143
theorem B2938781 : Blo 1028606 2938781 := bstep (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) B1102043
theorem B3299287 : Blo 1028606 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B2316383 : Blo 1028606 2316383 := bstep (se 1 (by rfl) ⟨1737287, by rfl⟩ : syracuseStep 2316383 = 3474575) B3474575
theorem B1955983 : Blo 1028606 1955983 := bstep (se 1 (by rfl) ⟨1466987, by rfl⟩ : syracuseStep 1955983 = 2933975) B2933975
theorem B2611399 : Blo 1028606 2611399 := bstep (se 1 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 2611399 = 3917099) B3917099
theorem B3299773 : Blo 1028606 3299773 := bstep (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) B1237415
theorem B42326833 : Blo 1028606 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B2317139 : Blo 1028606 2317139 := bstep (se 1 (by rfl) ⟨1737854, by rfl⟩ : syracuseStep 2317139 = 3475709) B3475709
theorem B7428989 : Blo 1028606 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B2939807 : Blo 1028606 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B1858631 : Blo 1028606 1858631 := bstep (se 1 (by rfl) ⟨1393973, by rfl⟩ : syracuseStep 1858631 = 2787947) B2787947
theorem B3136637 : Blo 1028606 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B9395453 : Blo 1028606 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B1465609 : Blo 1028606 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B2317679 : Blo 1028606 2317679 := bstep (se 1 (by rfl) ⟨1738259, by rfl⟩ : syracuseStep 2317679 = 3476519) B3476519
theorem B2317967 : Blo 1028606 2317967 := bstep (se 1 (by rfl) ⟨1738475, by rfl⟩ : syracuseStep 2317967 = 3476951) B3476951
theorem B1957601 : Blo 1028606 1957601 := bstep (se 2 (by rfl) ⟨734100, by rfl⟩ : syracuseStep 1957601 = 1468201) B1468201
theorem B2318057 : Blo 1028606 2318057 := bstep (se 2 (by rfl) ⟨869271, by rfl⟩ : syracuseStep 2318057 = 1738543) B1738543
theorem B2612969 : Blo 1028606 2612969 := bstep (se 2 (by rfl) ⟨979863, by rfl⟩ : syracuseStep 2612969 = 1959727) B1959727
theorem B13230053 : Blo 1028606 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B11755853 : Blo 1028606 11755853 := bstep (se 3 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 11755853 = 4408445) B4408445
theorem B2319083 : Blo 1028606 2319083 := bstep (se 1 (by rfl) ⟨1739312, by rfl⟩ : syracuseStep 2319083 = 3478625) B3478625
theorem B14869277 : Blo 1028606 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B96429491 : Blo 1028606 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B2319983 : Blo 1028606 2319983 := bstep (se 1 (by rfl) ⟨1739987, by rfl⟩ : syracuseStep 2319983 = 3479975) B3479975
theorem B1959545 : Blo 1028606 1959545 := bstep (se 2 (by rfl) ⟨734829, by rfl⟩ : syracuseStep 1959545 = 1469659) B1469659
theorem B2320091 : Blo 1028606 2320091 := bstep (se 1 (by rfl) ⟨1740068, by rfl⟩ : syracuseStep 2320091 = 3480137) B3480137
theorem B1959643 : Blo 1028606 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B1468297 : Blo 1028606 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B1042975 : Blo 1028606 1042975 := bstep (se 1 (by rfl) ⟨782231, by rfl⟩ : syracuseStep 1042975 = 1564463) B1564463
theorem B2321207 : Blo 1028606 2321207 := bstep (se 1 (by rfl) ⟨1740905, by rfl⟩ : syracuseStep 2321207 = 3481811) B3481811
theorem B10578923 : Blo 1028606 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B2321387 : Blo 1028606 2321387 := bstep (se 1 (by rfl) ⟨1741040, by rfl⟩ : syracuseStep 2321387 = 3482081) B3482081
theorem B11758769 : Blo 1028606 11758769 := bstep (se 2 (by rfl) ⟨4409538, by rfl⟩ : syracuseStep 11758769 = 8819077) B8819077
theorem B2322215 : Blo 1028606 2322215 := bstep (se 1 (by rfl) ⟨1741661, by rfl⟩ : syracuseStep 2322215 = 3483323) B3483323
theorem B29716409 : Blo 1028606 29716409 := bstep (se 2 (by rfl) ⟨11143653, by rfl⟩ : syracuseStep 29716409 = 22287307) B22287307
theorem B162558515 : Blo 1028606 162558515 := bstep (se 1 (by rfl) ⟨121918886, by rfl⟩ : syracuseStep 162558515 = 243837773) B243837773
theorem B2323241 : Blo 1028606 2323241 := bstep (se 2 (by rfl) ⟨871215, by rfl⟩ : syracuseStep 2323241 = 1742431) B1742431
theorem B308638513 : Blo 1028606 308638513 := bstep (se 2 (by rfl) ⟨115739442, by rfl⟩ : syracuseStep 308638513 = 231478885) B231478885
theorem B1569899 : Blo 1028606 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B12711161 : Blo 1028606 12711161 := bstep (se 2 (by rfl) ⟨4766685, by rfl⟩ : syracuseStep 12711161 = 9533371) B9533371
theorem B29685041 : Blo 1028606 29685041 := bstep (se 2 (by rfl) ⟨11131890, by rfl⟩ : syracuseStep 29685041 = 22263781) B22263781
theorem B5862779 : Blo 1028606 5862779 := bstep (se 1 (by rfl) ⟨4397084, by rfl⟩ : syracuseStep 5862779 = 8794169) B8794169
theorem B3306977 : Blo 1028606 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B25098133 : Blo 1028606 25098133 := bstep (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) B1176475
theorem B5863529 : Blo 1028606 5863529 := bstep (se 2 (by rfl) ⟨2198823, by rfl⟩ : syracuseStep 5863529 = 4397647) B4397647
theorem B3471659 : Blo 1028606 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B7436717 : Blo 1028606 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B3471929 : Blo 1028606 3471929 := bstep (se 2 (by rfl) ⟨1301973, by rfl⟩ : syracuseStep 3471929 = 2603947) B2603947
theorem B13367915 : Blo 1028606 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B23755639 : Blo 1028606 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B5209271 : Blo 1028606 5209271 := bstep (se 1 (by rfl) ⟨3906953, by rfl⟩ : syracuseStep 5209271 = 7813907) B7813907
theorem B1736167 : Blo 1028606 1736167 := bstep (se 1 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 1736167 = 2604251) B2604251
theorem B1736255 : Blo 1028606 1736255 := bstep (se 1 (by rfl) ⟨1302191, by rfl⟩ : syracuseStep 1736255 = 2604383) B2604383
theorem B5013335 : Blo 1028606 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B2785213 : Blo 1028606 2785213 := bstep (se 3 (by rfl) ⟨522227, by rfl⟩ : syracuseStep 2785213 = 1044455) B1044455
theorem B3473711 : Blo 1028606 3473711 := bstep (se 1 (by rfl) ⟨2605283, by rfl⟩ : syracuseStep 3473711 = 5210567) B5210567
theorem B1737247 : Blo 1028606 1737247 := bstep (se 1 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 1737247 = 2605871) B2605871
theorem B19825397 : Blo 1028606 19825397 := bstep (se 5 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 19825397 = 1858631) B1858631
theorem B4227851 : Blo 1028606 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B5210891 : Blo 1028606 5210891 := bstep (se 1 (by rfl) ⟨3908168, by rfl⟩ : syracuseStep 5210891 = 7816337) B7816337
theorem B1148015 : Blo 1028606 1148015 := bstep (se 1 (by rfl) ⟨861011, by rfl⟩ : syracuseStep 1148015 = 1722023) B1722023
theorem B4949585 : Blo 1028606 4949585 := bstep (se 2 (by rfl) ⟨1856094, by rfl⟩ : syracuseStep 4949585 = 3712189) B3712189
theorem B1738415 : Blo 1028606 1738415 := bstep (se 1 (by rfl) ⟨1303811, by rfl⟩ : syracuseStep 1738415 = 2607623) B2607623
theorem B7833347 : Blo 1028606 7833347 := bstep (se 1 (by rfl) ⟨5875010, by rfl⟩ : syracuseStep 7833347 = 11750021) B11750021
theorem B14845751 : Blo 1028606 14845751 := bstep (se 1 (by rfl) ⟨11134313, by rfl⟩ : syracuseStep 14845751 = 22268627) B22268627
theorem B3475439 : Blo 1028606 3475439 := bstep (se 1 (by rfl) ⟨2606579, by rfl⟩ : syracuseStep 3475439 = 5213159) B5213159
theorem B1738975 : Blo 1028606 1738975 := bstep (se 1 (by rfl) ⟨1304231, by rfl⟩ : syracuseStep 1738975 = 2608463) B2608463
theorem B5212511 : Blo 1028606 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B8161631 : Blo 1028606 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B5867903 : Blo 1028606 5867903 := bstep (se 1 (by rfl) ⟨4400927, by rfl⟩ : syracuseStep 5867903 = 8801855) B8801855
theorem B1542953 : Blo 1028606 1542953 := bstep (se 2 (by rfl) ⟨578607, by rfl⟩ : syracuseStep 1542953 = 1157215) B1157215
theorem B2198431 : Blo 1028606 2198431 := bstep (se 1 (by rfl) ⟨1648823, by rfl⟩ : syracuseStep 2198431 = 3297647) B3297647
theorem B1543163 : Blo 1028606 1543163 := bstep (se 1 (by rfl) ⟨1157372, by rfl⟩ : syracuseStep 1543163 = 2314745) B2314745
theorem B1543223 : Blo 1028606 1543223 := bstep (se 1 (by rfl) ⟨1157417, by rfl⟩ : syracuseStep 1543223 = 2314835) B2314835
theorem B1739839 : Blo 1028606 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B2788415 : Blo 1028606 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B1543343 : Blo 1028606 1543343 := bstep (se 1 (by rfl) ⟨1157507, by rfl⟩ : syracuseStep 1543343 = 2315015) B2315015
theorem B4394351 : Blo 1028606 4394351 := bstep (se 1 (by rfl) ⟨3295763, by rfl⟩ : syracuseStep 4394351 = 6591527) B6591527
theorem B1544063 : Blo 1028606 1544063 := bstep (se 1 (by rfl) ⟨1158047, by rfl⟩ : syracuseStep 1544063 = 2316095) B2316095
theorem B1544255 : Blo 1028606 1544255 := bstep (se 1 (by rfl) ⟨1158191, by rfl⟩ : syracuseStep 1544255 = 2316383) B2316383
theorem B7835777 : Blo 1028606 7835777 := bstep (se 2 (by rfl) ⟨2938416, by rfl⟩ : syracuseStep 7835777 = 5876833) B5876833
theorem B1544489 : Blo 1028606 1544489 := bstep (se 2 (by rfl) ⟨579183, by rfl⟩ : syracuseStep 1544489 = 1158367) B1158367
theorem B1544759 : Blo 1028606 1544759 := bstep (se 1 (by rfl) ⟨1158569, by rfl⟩ : syracuseStep 1544759 = 2317139) B2317139
theorem B4952659 : Blo 1028606 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B4461319 : Blo 1028606 4461319 := bstep (se 1 (by rfl) ⟨3345989, by rfl⟩ : syracuseStep 4461319 = 6691979) B6691979
theorem B6263635 : Blo 1028606 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B3478355 : Blo 1028606 3478355 := bstep (se 1 (by rfl) ⟨2608766, by rfl⟩ : syracuseStep 3478355 = 5217533) B5217533
theorem B1545119 : Blo 1028606 1545119 := bstep (se 1 (by rfl) ⟨1158839, by rfl⟩ : syracuseStep 1545119 = 2317679) B2317679
theorem B2233327 : Blo 1028606 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B7836749 : Blo 1028606 7836749 := bstep (se 3 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 7836749 = 2938781) B2938781
theorem B1545311 : Blo 1028606 1545311 := bstep (se 1 (by rfl) ⟨1158983, by rfl⟩ : syracuseStep 1545311 = 2317967) B2317967
theorem B1545371 : Blo 1028606 1545371 := bstep (se 1 (by rfl) ⟨1159028, by rfl⟩ : syracuseStep 1545371 = 2318057) B2318057
theorem B1741979 : Blo 1028606 1741979 := bstep (se 1 (by rfl) ⟨1306484, by rfl⟩ : syracuseStep 1741979 = 2612969) B2612969
theorem B4396349 : Blo 1028606 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B8820035 : Blo 1028606 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B3478895 : Blo 1028606 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B4462073 : Blo 1028606 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B7837235 : Blo 1028606 7837235 := bstep (se 1 (by rfl) ⟨5877926, by rfl⟩ : syracuseStep 7837235 = 11755853) B11755853
theorem B1546055 : Blo 1028606 1546055 := bstep (se 1 (by rfl) ⟨1159541, by rfl⟩ : syracuseStep 1546055 = 2319083) B2319083
theorem B3479543 : Blo 1028606 3479543 := bstep (se 1 (by rfl) ⟨2609657, by rfl⟩ : syracuseStep 3479543 = 5219315) B5219315
theorem B1546655 : Blo 1028606 1546655 := bstep (se 1 (by rfl) ⟨1159991, by rfl⟩ : syracuseStep 1546655 = 2319983) B2319983
theorem B1546727 : Blo 1028606 1546727 := bstep (se 1 (by rfl) ⟨1160045, by rfl⟩ : syracuseStep 1546727 = 2320091) B2320091
theorem B8788733 : Blo 1028606 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B3480623 : Blo 1028606 3480623 := bstep (se 1 (by rfl) ⟨2610467, by rfl⟩ : syracuseStep 3480623 = 5220935) B5220935
theorem B1547471 : Blo 1028606 1547471 := bstep (se 1 (by rfl) ⟨1160603, by rfl⟩ : syracuseStep 1547471 = 2321207) B2321207
theorem B7052615 : Blo 1028606 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B1547591 : Blo 1028606 1547591 := bstep (se 1 (by rfl) ⟨1160693, by rfl⟩ : syracuseStep 1547591 = 2321387) B2321387
theorem B7839179 : Blo 1028606 7839179 := bstep (se 1 (by rfl) ⟨5879384, by rfl⟩ : syracuseStep 7839179 = 11758769) B11758769
theorem B1547753 : Blo 1028606 1547753 := bstep (se 2 (by rfl) ⟨580407, by rfl⟩ : syracuseStep 1547753 = 1160815) B1160815
theorem B1547897 : Blo 1028606 1547897 := bstep (se 2 (by rfl) ⟨580461, by rfl⟩ : syracuseStep 1547897 = 1160923) B1160923
theorem B1548143 : Blo 1028606 1548143 := bstep (se 1 (by rfl) ⟨1161107, by rfl⟩ : syracuseStep 1548143 = 2322215) B2322215
theorem B33464177 : Blo 1028606 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B4399049 : Blo 1028606 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B3907561 : Blo 1028606 3907561 := bstep (se 2 (by rfl) ⟨1465335, by rfl⟩ : syracuseStep 3907561 = 2930671) B2930671
theorem B2203625 : Blo 1028606 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B3481865 : Blo 1028606 3481865 := bstep (se 2 (by rfl) ⟨1305699, by rfl⟩ : syracuseStep 3481865 = 2611399) B2611399
theorem B3350879 : Blo 1028606 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B108372343 : Blo 1028606 108372343 := bstep (se 1 (by rfl) ⟨81279257, by rfl⟩ : syracuseStep 108372343 = 162558515) B162558515
theorem B1548827 : Blo 1028606 1548827 := bstep (se 1 (by rfl) ⟨1161620, by rfl⟩ : syracuseStep 1548827 = 2323241) B2323241
theorem B4399697 : Blo 1028606 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B3908519 : Blo 1028606 3908519 := bstep (se 1 (by rfl) ⟨2931389, by rfl⟩ : syracuseStep 3908519 = 5862779) B5862779
theorem B2204651 : Blo 1028606 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B56435777 : Blo 1028606 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B3909019 : Blo 1028606 3909019 := bstep (se 1 (by rfl) ⟨2931764, by rfl⟩ : syracuseStep 3909019 = 5863529) B5863529
theorem B4957811 : Blo 1028606 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B22292333 : Blo 1028606 22292333 := bstep (se 3 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 22292333 = 8359625) B8359625
theorem B3909505 : Blo 1028606 3909505 := bstep (se 2 (by rfl) ⟨1466064, by rfl⟩ : syracuseStep 3909505 = 2932129) B2932129
theorem B5875901 : Blo 1028606 5875901 := bstep (se 3 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 5875901 = 2203463) B2203463
theorem B1157503 : Blo 1028606 1157503 := bstep (se 1 (by rfl) ⟨868127, by rfl⟩ : syracuseStep 1157503 = 1736255) B1736255
theorem B3713617 : Blo 1028606 3713617 := bstep (se 2 (by rfl) ⟨1392606, by rfl⟩ : syracuseStep 3713617 = 2785213) B2785213
theorem B6597395 : Blo 1028606 6597395 := bstep (se 1 (by rfl) ⟨4948046, by rfl⟩ : syracuseStep 6597395 = 9896093) B9896093
theorem B14855561 : Blo 1028606 14855561 := bstep (se 2 (by rfl) ⟨5570835, by rfl⟩ : syracuseStep 14855561 = 11141671) B11141671
theorem B1650143 : Blo 1028606 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B11742731 : Blo 1028606 11742731 := bstep (se 1 (by rfl) ⟨8807048, by rfl⟩ : syracuseStep 11742731 = 17614097) B17614097
theorem B96808547 : Blo 1028606 96808547 := bstep (se 1 (by rfl) ⟨72606410, by rfl⟩ : syracuseStep 96808547 = 145212821) B145212821
theorem B1158907 : Blo 1028606 1158907 := bstep (se 1 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 1158907 = 1738361) B1738361
theorem B1159231 : Blo 1028606 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B3715303 : Blo 1028606 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B2929259 : Blo 1028606 2929259 := bstep (se 1 (by rfl) ⟨2196944, by rfl⟩ : syracuseStep 2929259 = 4393889) B4393889
theorem B11907749 : Blo 1028606 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B1028859 : Blo 1028606 1028859 := bstep (se 1 (by rfl) ⟨771644, by rfl⟩ : syracuseStep 1028859 = 1543289) B1543289
theorem B1028927 : Blo 1028606 1028927 := bstep (se 1 (by rfl) ⟨771695, by rfl⟩ : syracuseStep 1028927 = 1543391) B1543391
theorem B1028955 : Blo 1028606 1028955 := bstep (se 1 (by rfl) ⟨771716, by rfl⟩ : syracuseStep 1028955 = 1543433) B1543433
theorem B4469633 : Blo 1028606 4469633 := bstep (se 2 (by rfl) ⟨1676112, by rfl⟩ : syracuseStep 4469633 = 3352225) B3352225
theorem B1160095 : Blo 1028606 1160095 := bstep (se 1 (by rfl) ⟨870071, by rfl⟩ : syracuseStep 1160095 = 1740143) B1740143
theorem B1029023 : Blo 1028606 1029023 := bstep (se 1 (by rfl) ⟨771767, by rfl⟩ : syracuseStep 1029023 = 1543535) B1543535
theorem B1029103 : Blo 1028606 1029103 := bstep (se 1 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 1029103 = 1543655) B1543655
theorem B1029191 : Blo 1028606 1029191 := bstep (se 1 (by rfl) ⟨771893, by rfl⟩ : syracuseStep 1029191 = 1543787) B1543787
theorem B1029275 : Blo 1028606 1029275 := bstep (se 1 (by rfl) ⟨771956, by rfl⟩ : syracuseStep 1029275 = 1543913) B1543913
theorem B1160347 : Blo 1028606 1160347 := bstep (se 1 (by rfl) ⟨870260, by rfl⟩ : syracuseStep 1160347 = 1740521) B1740521
theorem B1029371 : Blo 1028606 1029371 := bstep (se 1 (by rfl) ⟨772028, by rfl⟩ : syracuseStep 1029371 = 1544057) B1544057
theorem B5223689 : Blo 1028606 5223689 := bstep (se 2 (by rfl) ⟨1958883, by rfl⟩ : syracuseStep 5223689 = 3917767) B3917767
theorem B1029439 : Blo 1028606 1029439 := bstep (se 1 (by rfl) ⟨772079, by rfl⟩ : syracuseStep 1029439 = 1544159) B1544159
theorem B1029607 : Blo 1028606 1029607 := bstep (se 1 (by rfl) ⟨772205, by rfl⟩ : syracuseStep 1029607 = 1544411) B1544411
theorem B1029615 : Blo 1028606 1029615 := bstep (se 1 (by rfl) ⟨772211, by rfl⟩ : syracuseStep 1029615 = 1544423) B1544423
theorem B1029723 : Blo 1028606 1029723 := bstep (se 1 (by rfl) ⟨772292, by rfl⟩ : syracuseStep 1029723 = 1544585) B1544585
theorem B1029787 : Blo 1028606 1029787 := bstep (se 1 (by rfl) ⟨772340, by rfl⟩ : syracuseStep 1029787 = 1544681) B1544681
theorem B1029871 : Blo 1028606 1029871 := bstep (se 1 (by rfl) ⟨772403, by rfl⟩ : syracuseStep 1029871 = 1544807) B1544807
theorem B1029959 : Blo 1028606 1029959 := bstep (se 1 (by rfl) ⟨772469, by rfl⟩ : syracuseStep 1029959 = 1544939) B1544939
theorem B1161031 : Blo 1028606 1161031 := bstep (se 1 (by rfl) ⟨870773, by rfl⟩ : syracuseStep 1161031 = 1741547) B1741547
theorem B1029979 : Blo 1028606 1029979 := bstep (se 1 (by rfl) ⟨772484, by rfl⟩ : syracuseStep 1029979 = 1544969) B1544969
theorem B1030047 : Blo 1028606 1030047 := bstep (se 1 (by rfl) ⟨772535, by rfl⟩ : syracuseStep 1030047 = 1545071) B1545071
theorem B1030215 : Blo 1028606 1030215 := bstep (se 1 (by rfl) ⟨772661, by rfl⟩ : syracuseStep 1030215 = 1545323) B1545323
theorem B1030375 : Blo 1028606 1030375 := bstep (se 1 (by rfl) ⟨772781, by rfl⟩ : syracuseStep 1030375 = 1545563) B1545563
theorem B8927495 : Blo 1028606 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B1030559 : Blo 1028606 1030559 := bstep (se 1 (by rfl) ⟨772919, by rfl⟩ : syracuseStep 1030559 = 1545839) B1545839
theorem B3914183 : Blo 1028606 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B1030607 : Blo 1028606 1030607 := bstep (se 1 (by rfl) ⟨772955, by rfl⟩ : syracuseStep 1030607 = 1545911) B1545911
theorem B1161679 : Blo 1028606 1161679 := bstep (se 1 (by rfl) ⟨871259, by rfl⟩ : syracuseStep 1161679 = 1742519) B1742519
theorem B5880275 : Blo 1028606 5880275 := bstep (se 1 (by rfl) ⟨4410206, by rfl⟩ : syracuseStep 5880275 = 8820413) B8820413
theorem B1030631 : Blo 1028606 1030631 := bstep (se 1 (by rfl) ⟨772973, by rfl⟩ : syracuseStep 1030631 = 1545947) B1545947
theorem B1030747 : Blo 1028606 1030747 := bstep (se 1 (by rfl) ⟨773060, by rfl⟩ : syracuseStep 1030747 = 1546121) B1546121
theorem B1030815 : Blo 1028606 1030815 := bstep (se 1 (by rfl) ⟨773111, by rfl⟩ : syracuseStep 1030815 = 1546223) B1546223
theorem B5225147 : Blo 1028606 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B1030983 : Blo 1028606 1030983 := bstep (se 1 (by rfl) ⟨773237, by rfl⟩ : syracuseStep 1030983 = 1546475) B1546475
theorem B1031023 : Blo 1028606 1031023 := bstep (se 1 (by rfl) ⟨773267, by rfl⟩ : syracuseStep 1031023 = 1546535) B1546535
theorem B1031079 : Blo 1028606 1031079 := bstep (se 1 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 1031079 = 1546619) B1546619
theorem B1031259 : Blo 1028606 1031259 := bstep (se 1 (by rfl) ⟨773444, by rfl⟩ : syracuseStep 1031259 = 1546889) B1546889
theorem B1031375 : Blo 1028606 1031375 := bstep (se 1 (by rfl) ⟨773531, by rfl⟩ : syracuseStep 1031375 = 1547063) B1547063
theorem B1031399 : Blo 1028606 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1031495 : Blo 1028606 1031495 := bstep (se 1 (by rfl) ⟨773621, by rfl⟩ : syracuseStep 1031495 = 1547243) B1547243
theorem B1031631 : Blo 1028606 1031631 := bstep (se 1 (by rfl) ⟨773723, by rfl⟩ : syracuseStep 1031631 = 1547447) B1547447
theorem B1031791 : Blo 1028606 1031791 := bstep (se 1 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 1031791 = 1547687) B1547687
theorem B1031847 : Blo 1028606 1031847 := bstep (se 1 (by rfl) ⟨773885, by rfl⟩ : syracuseStep 1031847 = 1547771) B1547771
theorem B1031911 : Blo 1028606 1031911 := bstep (se 1 (by rfl) ⟨773933, by rfl⟩ : syracuseStep 1031911 = 1547867) B1547867
theorem B1031967 : Blo 1028606 1031967 := bstep (se 1 (by rfl) ⟨773975, by rfl⟩ : syracuseStep 1031967 = 1547951) B1547951
theorem B1032047 : Blo 1028606 1032047 := bstep (se 1 (by rfl) ⟨774035, by rfl⟩ : syracuseStep 1032047 = 1548071) B1548071
theorem B3915641 : Blo 1028606 3915641 := bstep (se 2 (by rfl) ⟨1468365, by rfl⟩ : syracuseStep 3915641 = 2936731) B2936731
theorem B1032103 : Blo 1028606 1032103 := bstep (se 1 (by rfl) ⟨774077, by rfl⟩ : syracuseStep 1032103 = 1548155) B1548155
theorem B1032383 : Blo 1028606 1032383 := bstep (se 1 (by rfl) ⟨774287, by rfl⟩ : syracuseStep 1032383 = 1548575) B1548575
theorem B1032399 : Blo 1028606 1032399 := bstep (se 1 (by rfl) ⟨774299, by rfl⟩ : syracuseStep 1032399 = 1548599) B1548599
theorem B1032447 : Blo 1028606 1032447 := bstep (se 1 (by rfl) ⟨774335, by rfl⟩ : syracuseStep 1032447 = 1548671) B1548671
theorem B1032495 : Blo 1028606 1032495 := bstep (se 1 (by rfl) ⟨774371, by rfl⟩ : syracuseStep 1032495 = 1548743) B1548743
theorem B18792809 : Blo 1028606 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B3916295 : Blo 1028606 3916295 := bstep (se 1 (by rfl) ⟨2937221, by rfl⟩ : syracuseStep 3916295 = 5874443) B5874443
theorem B9912851 : Blo 1028606 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B17842717 : Blo 1028606 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B2605729 : Blo 1028606 2605729 := bstep (se 2 (by rfl) ⟨977148, by rfl⟩ : syracuseStep 2605729 = 1954297) B1954297
theorem B2933633 : Blo 1028606 2933633 := bstep (se 2 (by rfl) ⟨1100112, by rfl⟩ : syracuseStep 2933633 = 2200225) B2200225
theorem B3916795 : Blo 1028606 3916795 := bstep (se 1 (by rfl) ⟨2937596, by rfl⟩ : syracuseStep 3916795 = 5875193) B5875193
theorem B2933815 : Blo 1028606 2933815 := bstep (se 1 (by rfl) ⟨2200361, by rfl⟩ : syracuseStep 2933815 = 4400723) B4400723
theorem B411518017 : Blo 1028606 411518017 := bstep (se 2 (by rfl) ⟨154319256, by rfl⟩ : syracuseStep 411518017 = 308638513) B308638513
theorem B2606519 : Blo 1028606 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B2935399 : Blo 1028606 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B19810939 : Blo 1028606 19810939 := bstep (se 1 (by rfl) ⟨14858204, by rfl⟩ : syracuseStep 19810939 = 29716409) B29716409
theorem B2935433 : Blo 1028606 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B2607977 : Blo 1028606 2607977 := bstep (se 2 (by rfl) ⟨977991, by rfl⟩ : syracuseStep 2607977 = 1955983) B1955983
theorem B2935673 : Blo 1028606 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B8474107 : Blo 1028606 8474107 := bstep (se 1 (by rfl) ⟨6355580, by rfl⟩ : syracuseStep 8474107 = 12711161) B12711161
theorem B10735415 : Blo 1028606 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B31674185 : Blo 1028606 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B1953659 : Blo 1028606 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B2609111 : Blo 1028606 2609111 := bstep (se 1 (by rfl) ⟨1956833, by rfl⟩ : syracuseStep 2609111 = 3913667) B3913667
theorem B1953895 : Blo 1028606 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B2314439 : Blo 1028606 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B6607133 : Blo 1028606 6607133 := bstep (se 3 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 6607133 = 2477675) B2477675
theorem B2478367 : Blo 1028606 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B1954145 : Blo 1028606 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B2314619 : Blo 1028606 2314619 := bstep (se 1 (by rfl) ⟨1735964, by rfl⟩ : syracuseStep 2314619 = 3471929) B3471929
theorem B2314889 : Blo 1028606 2314889 := bstep (se 2 (by rfl) ⟨868083, by rfl⟩ : syracuseStep 2314889 = 1736167) B1736167
theorem B50058485 : Blo 1028606 50058485 := bstep (se 5 (by rfl) ⟨2346491, by rfl⟩ : syracuseStep 50058485 = 4692983) B4692983
theorem B2315627 : Blo 1028606 2315627 := bstep (se 1 (by rfl) ⟨1736720, by rfl⟩ : syracuseStep 2315627 = 3473441) B3473441
theorem B2610539 : Blo 1028606 2610539 := bstep (se 1 (by rfl) ⟨1957904, by rfl⟩ : syracuseStep 2610539 = 3915809) B3915809
theorem B2315897 : Blo 1028606 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B8804315 : Blo 1028606 8804315 := bstep (se 1 (by rfl) ⟨6603236, by rfl⟩ : syracuseStep 8804315 = 13206473) B13206473
theorem B2316257 : Blo 1028606 2316257 := bstep (se 2 (by rfl) ⟨868596, by rfl⟩ : syracuseStep 2316257 = 1737193) B1737193
theorem B1956059 : Blo 1028606 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B6609235 : Blo 1028606 6609235 := bstep (se 1 (by rfl) ⟨4956926, by rfl⟩ : syracuseStep 6609235 = 9913853) B9913853
theorem B2939419 : Blo 1028606 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B71326817 : Blo 1028606 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B2940047 : Blo 1028606 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B11722319 : Blo 1028606 11722319 := bstep (se 1 (by rfl) ⟨8791739, by rfl⟩ : syracuseStep 11722319 = 17583479) B17583479
theorem B2612857 : Blo 1028606 2612857 := bstep (se 2 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 2612857 = 1959643) B1959643
theorem B2318111 : Blo 1028606 2318111 := bstep (se 1 (by rfl) ⟨1738583, by rfl⟩ : syracuseStep 2318111 = 3477167) B3477167
theorem B2613131 : Blo 1028606 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B2318327 : Blo 1028606 2318327 := bstep (se 1 (by rfl) ⟨1738745, by rfl⟩ : syracuseStep 2318327 = 3477491) B3477491
theorem B5562533 : Blo 1028606 5562533 := bstep (se 4 (by rfl) ⟨521487, by rfl⟩ : syracuseStep 5562533 = 1042975) B1042975
theorem B2318543 : Blo 1028606 2318543 := bstep (se 1 (by rfl) ⟨1738907, by rfl⟩ : syracuseStep 2318543 = 3477815) B3477815
theorem B1466623 : Blo 1028606 1466623 := bstep (se 1 (by rfl) ⟨1099967, by rfl⟩ : syracuseStep 1466623 = 2199935) B2199935
theorem B4186397 : Blo 1028606 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B2318687 : Blo 1028606 2318687 := bstep (se 1 (by rfl) ⟨1739015, by rfl⟩ : syracuseStep 2318687 = 3478031) B3478031
theorem B1303067 : Blo 1028606 1303067 := bstep (se 1 (by rfl) ⟨977300, by rfl⟩ : syracuseStep 1303067 = 1954601) B1954601
theorem B1237531 : Blo 1028606 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B2351783 : Blo 1028606 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B2319407 : Blo 1028606 2319407 := bstep (se 1 (by rfl) ⟨1739555, by rfl⟩ : syracuseStep 2319407 = 3479111) B3479111
theorem B7824599 : Blo 1028606 7824599 := bstep (se 1 (by rfl) ⟨5868449, by rfl⟩ : syracuseStep 7824599 = 11736899) B11736899
theorem B9397787 : Blo 1028606 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B16737931 : Blo 1028606 16737931 := bstep (se 1 (by rfl) ⟨12553448, by rfl⟩ : syracuseStep 16737931 = 25106897) B25106897
theorem B2320055 : Blo 1028606 2320055 := bstep (se 1 (by rfl) ⟨1740041, by rfl⟩ : syracuseStep 2320055 = 3480083) B3480083
theorem B1959871 : Blo 1028606 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B2091091 : Blo 1028606 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B12544109 : Blo 1028606 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B2320505 : Blo 1028606 2320505 := bstep (se 2 (by rfl) ⟨870189, by rfl⟩ : syracuseStep 2320505 = 1740379) B1740379
theorem B1305067 : Blo 1028606 1305067 := bstep (se 1 (by rfl) ⟨978800, by rfl⟩ : syracuseStep 1305067 = 1957601) B1957601
theorem B225995285 : Blo 1028606 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B2321819 : Blo 1028606 2321819 := bstep (se 1 (by rfl) ⟨1741364, by rfl⟩ : syracuseStep 2321819 = 3482729) B3482729
theorem B64286327 : Blo 1028606 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B2780897 : Blo 1028606 2780897 := bstep (se 2 (by rfl) ⟨1042836, by rfl⟩ : syracuseStep 2780897 = 2085673) B2085673
theorem B1306363 : Blo 1028606 1306363 := bstep (se 1 (by rfl) ⟨979772, by rfl⟩ : syracuseStep 1306363 = 1959545) B1959545
theorem B21458843 : Blo 1028606 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B2322395 : Blo 1028606 2322395 := bstep (se 1 (by rfl) ⟨1741796, by rfl⟩ : syracuseStep 2322395 = 3483593) B3483593
theorem B2322575 : Blo 1028606 2322575 := bstep (se 1 (by rfl) ⟨1741931, by rfl⟩ : syracuseStep 2322575 = 3483863) B3483863
theorem B2322665 : Blo 1028606 2322665 := bstep (se 2 (by rfl) ⟨870999, by rfl⟩ : syracuseStep 2322665 = 1741999) B1741999
theorem B2322791 : Blo 1028606 2322791 := bstep (se 1 (by rfl) ⟨1742093, by rfl⟩ : syracuseStep 2322791 = 3484187) B3484187
theorem B71529101 : Blo 1028606 71529101 := bstep (se 3 (by rfl) ⟨13411706, by rfl⟩ : syracuseStep 71529101 = 26823413) B26823413
theorem B66777857 : Blo 1028606 66777857 := bstep (se 2 (by rfl) ⟨25041696, by rfl⟩ : syracuseStep 66777857 = 50083393) B50083393
theorem B5207327 : Blo 1028606 5207327 := bstep (se 1 (by rfl) ⟨3905495, by rfl⟩ : syracuseStep 5207327 = 7810991) B7810991
theorem B3307463 : Blo 1028606 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B4946123 : Blo 1028606 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B19790027 : Blo 1028606 19790027 := bstep (se 1 (by rfl) ⟨14842520, by rfl⟩ : syracuseStep 19790027 = 29685041) B29685041
theorem B8911943 : Blo 1028606 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B7830917 : Blo 1028606 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B3472847 : Blo 1028606 3472847 := bstep (se 1 (by rfl) ⟨2604635, by rfl⟩ : syracuseStep 3472847 = 5209271) B5209271
theorem B5209595 : Blo 1028606 5209595 := bstep (se 1 (by rfl) ⟨3907196, by rfl⟩ : syracuseStep 5209595 = 7814393) B7814393
theorem B5865169 : Blo 1028606 5865169 := bstep (se 2 (by rfl) ⟨2199438, by rfl⟩ : syracuseStep 5865169 = 4398877) B4398877
theorem B3342223 : Blo 1028606 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B2818567 : Blo 1028606 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3473927 : Blo 1028606 3473927 := bstep (se 1 (by rfl) ⟨2605445, by rfl⟩ : syracuseStep 3473927 = 5210891) B5210891
theorem B23790289 : Blo 1028606 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B3474305 : Blo 1028606 3474305 := bstep (se 2 (by rfl) ⟨1302864, by rfl⟩ : syracuseStep 3474305 = 2605729) B2605729
theorem B5211053 : Blo 1028606 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B1737679 : Blo 1028606 1737679 := bstep (se 1 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 1737679 = 2606519) B2606519
theorem B9897167 : Blo 1028606 9897167 := bstep (se 1 (by rfl) ⟨7422875, by rfl⟩ : syracuseStep 9897167 = 14845751) B14845751
theorem B3474845 : Blo 1028606 3474845 := bstep (se 3 (by rfl) ⟨651533, by rfl⟩ : syracuseStep 3474845 = 1303067) B1303067
theorem B11732525 : Blo 1028606 11732525 := bstep (se 3 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 11732525 = 4399697) B4399697
theorem B3475007 : Blo 1028606 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B5441087 : Blo 1028606 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B5212025 : Blo 1028606 5212025 := bstep (se 2 (by rfl) ⟨1954509, by rfl⟩ : syracuseStep 5212025 = 3909019) B3909019
theorem B1738651 : Blo 1028606 1738651 := bstep (se 1 (by rfl) ⟨1303988, by rfl⟩ : syracuseStep 1738651 = 2607977) B2607977
theorem B22317241 : Blo 1028606 22317241 := bstep (se 2 (by rfl) ⟨8368965, by rfl⟩ : syracuseStep 22317241 = 16737931) B16737931
theorem B5212673 : Blo 1028606 5212673 := bstep (se 2 (by rfl) ⟨1954752, by rfl⟩ : syracuseStep 5212673 = 3909505) B3909505
theorem B1739407 : Blo 1028606 1739407 := bstep (se 1 (by rfl) ⟨1304555, by rfl⟩ : syracuseStep 1739407 = 2609111) B2609111
theorem B2788121 : Blo 1028606 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B1542959 : Blo 1028606 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B1543079 : Blo 1028606 1543079 := bstep (se 1 (by rfl) ⟨1157309, by rfl⟩ : syracuseStep 1543079 = 2314619) B2314619
theorem B1543259 : Blo 1028606 1543259 := bstep (se 1 (by rfl) ⟨1157444, by rfl⟩ : syracuseStep 1543259 = 2314889) B2314889
theorem B1543337 : Blo 1028606 1543337 := bstep (se 2 (by rfl) ⟨578751, by rfl⟩ : syracuseStep 1543337 = 1157503) B1157503
theorem B1740089 : Blo 1028606 1740089 := bstep (se 2 (by rfl) ⟨652533, by rfl⟩ : syracuseStep 1740089 = 1305067) B1305067
theorem B4951489 : Blo 1028606 4951489 := bstep (se 2 (by rfl) ⟨1856808, by rfl⟩ : syracuseStep 4951489 = 3713617) B3713617
theorem B26414585 : Blo 1028606 26414585 := bstep (se 2 (by rfl) ⟨9905469, by rfl⟩ : syracuseStep 26414585 = 19810939) B19810939
theorem B1543751 : Blo 1028606 1543751 := bstep (se 1 (by rfl) ⟨1157813, by rfl⟩ : syracuseStep 1543751 = 2315627) B2315627
theorem B1740359 : Blo 1028606 1740359 := bstep (se 1 (by rfl) ⟨1305269, by rfl⟩ : syracuseStep 1740359 = 2610539) B2610539
theorem B1543931 : Blo 1028606 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B5869543 : Blo 1028606 5869543 := bstep (se 1 (by rfl) ⟨4402157, by rfl⟩ : syracuseStep 5869543 = 8804315) B8804315
theorem B1544171 : Blo 1028606 1544171 := bstep (se 1 (by rfl) ⟨1158128, by rfl⟩ : syracuseStep 1544171 = 2316257) B2316257
theorem B47551211 : Blo 1028606 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B1545209 : Blo 1028606 1545209 := bstep (se 2 (by rfl) ⟨579453, by rfl⟩ : syracuseStep 1545209 = 1158907) B1158907
theorem B1741817 : Blo 1028606 1741817 := bstep (se 2 (by rfl) ⟨653181, by rfl⟩ : syracuseStep 1741817 = 1306363) B1306363
theorem B1545407 : Blo 1028606 1545407 := bstep (se 1 (by rfl) ⟨1159055, by rfl⟩ : syracuseStep 1545407 = 2318111) B2318111
theorem B1742087 : Blo 1028606 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B1545551 : Blo 1028606 1545551 := bstep (se 1 (by rfl) ⟨1159163, by rfl⟩ : syracuseStep 1545551 = 2318327) B2318327
theorem B1545641 : Blo 1028606 1545641 := bstep (se 2 (by rfl) ⟨579615, by rfl⟩ : syracuseStep 1545641 = 1159231) B1159231
theorem B3708355 : Blo 1028606 3708355 := bstep (se 1 (by rfl) ⟨2781266, by rfl⟩ : syracuseStep 3708355 = 5562533) B5562533
theorem B1545695 : Blo 1028606 1545695 := bstep (se 1 (by rfl) ⟨1159271, by rfl⟩ : syracuseStep 1545695 = 2318543) B2318543
theorem B2790931 : Blo 1028606 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B1545791 : Blo 1028606 1545791 := bstep (se 1 (by rfl) ⟨1159343, by rfl⟩ : syracuseStep 1545791 = 2318687) B2318687
theorem B2233919 : Blo 1028606 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B4953737 : Blo 1028606 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B1546271 : Blo 1028606 1546271 := bstep (se 1 (by rfl) ⟨1159703, by rfl⟩ : syracuseStep 1546271 = 2319407) B2319407
theorem B37623851 : Blo 1028606 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B5216399 : Blo 1028606 5216399 := bstep (se 1 (by rfl) ⟨3912299, by rfl⟩ : syracuseStep 5216399 = 7824599) B7824599
theorem B1546703 : Blo 1028606 1546703 := bstep (se 1 (by rfl) ⟨1160027, by rfl⟩ : syracuseStep 1546703 = 2320055) B2320055
theorem B1546793 : Blo 1028606 1546793 := bstep (se 2 (by rfl) ⟨580047, by rfl⟩ : syracuseStep 1546793 = 1160095) B1160095
theorem B8362739 : Blo 1028606 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B1547003 : Blo 1028606 1547003 := bstep (se 1 (by rfl) ⟨1160252, by rfl⟩ : syracuseStep 1547003 = 2320505) B2320505
theorem B1547129 : Blo 1028606 1547129 := bstep (se 2 (by rfl) ⟨580173, by rfl⟩ : syracuseStep 1547129 = 1160347) B1160347
theorem B4398263 : Blo 1028606 4398263 := bstep (se 1 (by rfl) ⟨3298697, by rfl⟩ : syracuseStep 4398263 = 6597395) B6597395
theorem B9903707 : Blo 1028606 9903707 := bstep (se 1 (by rfl) ⟨7427780, by rfl⟩ : syracuseStep 9903707 = 14855561) B14855561
theorem B1547879 : Blo 1028606 1547879 := bstep (se 1 (by rfl) ⟨1160909, by rfl⟩ : syracuseStep 1547879 = 2321819) B2321819
theorem B1548041 : Blo 1028606 1548041 := bstep (se 2 (by rfl) ⟨580515, by rfl⟩ : syracuseStep 1548041 = 1161031) B1161031
theorem B1548263 : Blo 1028606 1548263 := bstep (se 1 (by rfl) ⟨1161197, by rfl⟩ : syracuseStep 1548263 = 2322395) B2322395
theorem B1548383 : Blo 1028606 1548383 := bstep (se 1 (by rfl) ⟨1161287, by rfl⟩ : syracuseStep 1548383 = 2322575) B2322575
theorem B1548443 : Blo 1028606 1548443 := bstep (se 1 (by rfl) ⟨1161332, by rfl⟩ : syracuseStep 1548443 = 2322665) B2322665
theorem B1548527 : Blo 1028606 1548527 := bstep (se 1 (by rfl) ⟨1161395, by rfl⟩ : syracuseStep 1548527 = 2322791) B2322791
theorem B47686067 : Blo 1028606 47686067 := bstep (se 1 (by rfl) ⟨35764550, by rfl⟩ : syracuseStep 47686067 = 71529101) B71529101
theorem B7938499 : Blo 1028606 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B1548905 : Blo 1028606 1548905 := bstep (se 2 (by rfl) ⟨580839, by rfl⟩ : syracuseStep 1548905 = 1161679) B1161679
theorem B3482459 : Blo 1028606 3482459 := bstep (se 1 (by rfl) ⟨2611844, by rfl⟩ : syracuseStep 3482459 = 5223689) B5223689
theorem B4400381 : Blo 1028606 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B2204975 : Blo 1028606 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B3483431 : Blo 1028606 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B7415725 : Blo 1028606 7415725 := bstep (se 3 (by rfl) ⟨1390448, by rfl⟩ : syracuseStep 7415725 = 2780897) B2780897
theorem B5941295 : Blo 1028606 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B3483809 : Blo 1028606 3483809 := bstep (se 2 (by rfl) ⟨1306428, by rfl⟩ : syracuseStep 3483809 = 2612857) B2612857
theorem B5220611 : Blo 1028606 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B5876333 : Blo 1028606 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B12528539 : Blo 1028606 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B13216931 : Blo 1028606 13216931 := bstep (se 1 (by rfl) ⟨9912698, by rfl⟩ : syracuseStep 13216931 = 19825397) B19825397
theorem B1650041 : Blo 1028606 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B1158943 : Blo 1028606 1158943 := bstep (se 1 (by rfl) ⟨869207, by rfl⟩ : syracuseStep 1158943 = 1738415) B1738415
theorem B5222231 : Blo 1028606 5222231 := bstep (se 1 (by rfl) ⟨3916673, by rfl⟩ : syracuseStep 5222231 = 7833347) B7833347
theorem B5222393 : Blo 1028606 5222393 := bstep (se 2 (by rfl) ⟨1958397, by rfl⟩ : syracuseStep 5222393 = 3916795) B3916795
theorem B3911753 : Blo 1028606 3911753 := bstep (se 2 (by rfl) ⟨1466907, by rfl⟩ : syracuseStep 3911753 = 2933815) B2933815
theorem B3911935 : Blo 1028606 3911935 := bstep (se 1 (by rfl) ⟨2933951, by rfl⟩ : syracuseStep 3911935 = 5867903) B5867903
theorem B1028635 : Blo 1028606 1028635 := bstep (se 1 (by rfl) ⟨771476, by rfl⟩ : syracuseStep 1028635 = 1542953) B1542953
theorem B1028775 : Blo 1028606 1028775 := bstep (se 1 (by rfl) ⟨771581, by rfl⟩ : syracuseStep 1028775 = 1543163) B1543163
theorem B1028815 : Blo 1028606 1028815 := bstep (se 1 (by rfl) ⟨771611, by rfl⟩ : syracuseStep 1028815 = 1543223) B1543223
theorem B1028895 : Blo 1028606 1028895 := bstep (se 1 (by rfl) ⟨771671, by rfl⟩ : syracuseStep 1028895 = 1543343) B1543343
theorem B2929567 : Blo 1028606 2929567 := bstep (se 1 (by rfl) ⟨2197175, by rfl⟩ : syracuseStep 2929567 = 4394351) B4394351
theorem B7156943 : Blo 1028606 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B21116123 : Blo 1028606 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B1029375 : Blo 1028606 1029375 := bstep (se 1 (by rfl) ⟨772031, by rfl⟩ : syracuseStep 1029375 = 1544063) B1544063
theorem B1029503 : Blo 1028606 1029503 := bstep (se 1 (by rfl) ⟨772127, by rfl⟩ : syracuseStep 1029503 = 1544255) B1544255
theorem B5223851 : Blo 1028606 5223851 := bstep (se 1 (by rfl) ⟨3917888, by rfl⟩ : syracuseStep 5223851 = 7835777) B7835777
theorem B4404755 : Blo 1028606 4404755 := bstep (se 1 (by rfl) ⟨3303566, by rfl⟩ : syracuseStep 4404755 = 6607133) B6607133
theorem B1029659 : Blo 1028606 1029659 := bstep (se 1 (by rfl) ⟨772244, by rfl⟩ : syracuseStep 1029659 = 1544489) B1544489
theorem B3061373 : Blo 1028606 3061373 := bstep (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) B1148015
theorem B1029839 : Blo 1028606 1029839 := bstep (se 1 (by rfl) ⟨772379, by rfl⟩ : syracuseStep 1029839 = 1544759) B1544759
theorem B1030079 : Blo 1028606 1030079 := bstep (se 1 (by rfl) ⟨772559, by rfl⟩ : syracuseStep 1030079 = 1545119) B1545119
theorem B5224499 : Blo 1028606 5224499 := bstep (se 1 (by rfl) ⟨3918374, by rfl⟩ : syracuseStep 5224499 = 7836749) B7836749
theorem B1030207 : Blo 1028606 1030207 := bstep (se 1 (by rfl) ⟨772655, by rfl⟩ : syracuseStep 1030207 = 1545311) B1545311
theorem B1030247 : Blo 1028606 1030247 := bstep (se 1 (by rfl) ⟨772685, by rfl⟩ : syracuseStep 1030247 = 1545371) B1545371
theorem B1161319 : Blo 1028606 1161319 := bstep (se 1 (by rfl) ⟨870989, by rfl⟩ : syracuseStep 1161319 = 1741979) B1741979
theorem B3913865 : Blo 1028606 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B33372323 : Blo 1028606 33372323 := bstep (se 1 (by rfl) ⟨25029242, by rfl⟩ : syracuseStep 33372323 = 50058485) B50058485
theorem B2930899 : Blo 1028606 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B5880023 : Blo 1028606 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B5224823 : Blo 1028606 5224823 := bstep (se 1 (by rfl) ⟨3918617, by rfl⟩ : syracuseStep 5224823 = 7837235) B7837235
theorem B2931241 : Blo 1028606 2931241 := bstep (se 2 (by rfl) ⟨1099215, by rfl⟩ : syracuseStep 2931241 = 2198431) B2198431
theorem B1030703 : Blo 1028606 1030703 := bstep (se 1 (by rfl) ⟨773027, by rfl⟩ : syracuseStep 1030703 = 1546055) B1546055
theorem B1031103 : Blo 1028606 1031103 := bstep (se 1 (by rfl) ⟨773327, by rfl⟩ : syracuseStep 1031103 = 1546655) B1546655
theorem B1031151 : Blo 1028606 1031151 := bstep (se 1 (by rfl) ⟨773363, by rfl⟩ : syracuseStep 1031151 = 1546727) B1546727
theorem B1031647 : Blo 1028606 1031647 := bstep (se 1 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 1031647 = 1547471) B1547471
theorem B4701743 : Blo 1028606 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B1031727 : Blo 1028606 1031727 := bstep (se 1 (by rfl) ⟨773795, by rfl⟩ : syracuseStep 1031727 = 1547591) B1547591
theorem B5226119 : Blo 1028606 5226119 := bstep (se 1 (by rfl) ⟨3919589, by rfl⟩ : syracuseStep 5226119 = 7839179) B7839179
theorem B1031835 : Blo 1028606 1031835 := bstep (se 1 (by rfl) ⟨773876, by rfl⟩ : syracuseStep 1031835 = 1547753) B1547753
theorem B7814879 : Blo 1028606 7814879 := bstep (se 1 (by rfl) ⟨5861159, by rfl⟩ : syracuseStep 7814879 = 11722319) B11722319
theorem B1031931 : Blo 1028606 1031931 := bstep (se 1 (by rfl) ⟨773948, by rfl⟩ : syracuseStep 1031931 = 1547897) B1547897
theorem B1032095 : Blo 1028606 1032095 := bstep (se 1 (by rfl) ⟨774071, by rfl⟩ : syracuseStep 1032095 = 1548143) B1548143
theorem B2932699 : Blo 1028606 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B2605193 : Blo 1028606 2605193 := bstep (se 2 (by rfl) ⟨976947, by rfl⟩ : syracuseStep 2605193 = 1953895) B1953895
theorem B1032551 : Blo 1028606 1032551 := bstep (se 1 (by rfl) ⟨774413, by rfl⟩ : syracuseStep 1032551 = 1548827) B1548827
theorem B13189661 : Blo 1028606 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B2605679 : Blo 1028606 2605679 := bstep (se 1 (by rfl) ⟨1954259, by rfl⟩ : syracuseStep 2605679 = 3908519) B3908519
theorem B6603545 : Blo 1028606 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B5948425 : Blo 1028606 5948425 := bstep (se 2 (by rfl) ⟨2230659, by rfl⟩ : syracuseStep 5948425 = 4461319) B4461319
theorem B14861555 : Blo 1028606 14861555 := bstep (se 1 (by rfl) ⟨11146166, by rfl⟩ : syracuseStep 14861555 = 22292333) B22292333
theorem B3917267 : Blo 1028606 3917267 := bstep (se 1 (by rfl) ⟨2937950, by rfl⟩ : syracuseStep 3917267 = 5875901) B5875901
theorem B64539031 : Blo 1028606 64539031 := bstep (se 1 (by rfl) ⟨48404273, by rfl⟩ : syracuseStep 64539031 = 96808547) B96808547
theorem B14305895 : Blo 1028606 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B1952839 : Blo 1028606 1952839 := bstep (se 1 (by rfl) ⟨1464629, by rfl⟩ : syracuseStep 1952839 = 2929259) B2929259
theorem B44518571 : Blo 1028606 44518571 := bstep (se 1 (by rfl) ⟨33388928, by rfl⟩ : syracuseStep 44518571 = 66777857) B66777857
theorem B3919225 : Blo 1028606 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B13193351 : Blo 1028606 13193351 := bstep (se 1 (by rfl) ⟨9895013, by rfl⟩ : syracuseStep 13193351 = 19790027) B19790027
theorem B5951663 : Blo 1028606 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B2609455 : Blo 1028606 2609455 := bstep (se 1 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 2609455 = 3914183) B3914183
theorem B3920183 : Blo 1028606 3920183 := bstep (se 1 (by rfl) ⟨2940137, by rfl⟩ : syracuseStep 3920183 = 5880275) B5880275
theorem B7820225 : Blo 1028606 7820225 := bstep (se 2 (by rfl) ⟨2932584, by rfl⟩ : syracuseStep 7820225 = 5865169) B5865169
theorem B2315231 : Blo 1028606 2315231 := bstep (se 1 (by rfl) ⟨1736423, by rfl⟩ : syracuseStep 2315231 = 3472847) B3472847
theorem B2610427 : Blo 1028606 2610427 := bstep (se 1 (by rfl) ⟨1957820, by rfl⟩ : syracuseStep 2610427 = 3915641) B3915641
theorem B2315807 : Blo 1028606 2315807 := bstep (se 1 (by rfl) ⟨1736855, by rfl⟩ : syracuseStep 2315807 = 3473711) B3473711
theorem B1955497 : Blo 1028606 1955497 := bstep (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) B1466623
theorem B2610863 : Blo 1028606 2610863 := bstep (se 1 (by rfl) ⟨1958147, by rfl⟩ : syracuseStep 2610863 = 3916295) B3916295
theorem B6608567 : Blo 1028606 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B144496457 : Blo 1028606 144496457 := bstep (se 2 (by rfl) ⟨54186171, by rfl⟩ : syracuseStep 144496457 = 108372343) B108372343
theorem B1955755 : Blo 1028606 1955755 := bstep (se 1 (by rfl) ⟨1466816, by rfl⟩ : syracuseStep 1955755 = 2933633) B2933633
theorem B2316329 : Blo 1028606 2316329 := bstep (se 2 (by rfl) ⟨868623, by rfl⟩ : syracuseStep 2316329 = 1737247) B1737247
theorem B3299723 : Blo 1028606 3299723 := bstep (se 1 (by rfl) ⟨2474792, by rfl⟩ : syracuseStep 3299723 = 4949585) B4949585
theorem B2316959 : Blo 1028606 2316959 := bstep (se 1 (by rfl) ⟨1737719, by rfl⟩ : syracuseStep 2316959 = 3475439) B3475439
theorem B548690689 : Blo 1028606 548690689 := bstep (se 2 (by rfl) ⟨205759008, by rfl⟩ : syracuseStep 548690689 = 411518017) B411518017
theorem B1956955 : Blo 1028606 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B1957115 : Blo 1028606 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B1858943 : Blo 1028606 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B2613161 : Blo 1028606 2613161 := bstep (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) B1959871
theorem B2318633 : Blo 1028606 2318633 := bstep (se 2 (by rfl) ⟨869487, by rfl⟩ : syracuseStep 2318633 = 1738975) B1738975
theorem B2318903 : Blo 1028606 2318903 := bstep (se 1 (by rfl) ⟨1739177, by rfl⟩ : syracuseStep 2318903 = 3478355) B3478355
theorem B2319263 : Blo 1028606 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B2974715 : Blo 1028606 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B2319695 : Blo 1028606 2319695 := bstep (se 1 (by rfl) ⟨1739771, by rfl⟩ : syracuseStep 2319695 = 3479543) B3479543
theorem B25060765 : Blo 1028606 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B2319785 : Blo 1028606 2319785 := bstep (se 2 (by rfl) ⟨869919, by rfl⟩ : syracuseStep 2319785 = 1739839) B1739839
theorem B1304039 : Blo 1028606 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B5859155 : Blo 1028606 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B11298809 : Blo 1028606 11298809 := bstep (se 2 (by rfl) ⟨4237053, by rfl⟩ : syracuseStep 11298809 = 8474107) B8474107
theorem B2320415 : Blo 1028606 2320415 := bstep (se 1 (by rfl) ⟨1740311, by rfl⟩ : syracuseStep 2320415 = 3480623) B3480623
theorem B1960031 : Blo 1028606 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B22309451 : Blo 1028606 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B2321243 : Blo 1028606 2321243 := bstep (se 1 (by rfl) ⟨1740932, by rfl⟩ : syracuseStep 2321243 = 3481865) B3481865
theorem B3304489 : Blo 1028606 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B1567855 : Blo 1028606 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1469767 : Blo 1028606 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B3305207 : Blo 1028606 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B8351513 : Blo 1028606 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B2977769 : Blo 1028606 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B150663523 : Blo 1028606 150663523 := bstep (se 1 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 150663523 = 225995285) B225995285
theorem B7828487 : Blo 1028606 7828487 := bstep (se 1 (by rfl) ⟨5871365, by rfl⟩ : syracuseStep 7828487 = 11742731) B11742731
theorem B42857551 : Blo 1028606 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B8812313 : Blo 1028606 8812313 := bstep (se 2 (by rfl) ⟨3304617, by rfl⟩ : syracuseStep 8812313 = 6609235) B6609235
theorem B2979755 : Blo 1028606 2979755 := bstep (se 1 (by rfl) ⟨2234816, by rfl⟩ : syracuseStep 2979755 = 4469633) B4469633
theorem B3471551 : Blo 1028606 3471551 := bstep (se 1 (by rfl) ⟨2603663, by rfl⟩ : syracuseStep 3471551 = 5207327) B5207327
theorem B5209757 : Blo 1028606 5209757 := bstep (se 3 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 5209757 = 1953659) B1953659
theorem B3473063 : Blo 1028606 3473063 := bstep (se 1 (by rfl) ⟨2604797, by rfl⟩ : syracuseStep 3473063 = 5209595) B5209595
theorem B4456297 : Blo 1028606 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B5210081 : Blo 1028606 5210081 := bstep (se 2 (by rfl) ⟨1953780, by rfl⟩ : syracuseStep 5210081 = 3907561) B3907561
theorem B1736795 : Blo 1028606 1736795 := bstep (se 1 (by rfl) ⟨1302596, by rfl⟩ : syracuseStep 1736795 = 2605193) B2605193
theorem B1737119 : Blo 1028606 1737119 := bstep (se 1 (by rfl) ⟨1302839, by rfl⟩ : syracuseStep 1737119 = 2605679) B2605679
theorem B10584665 : Blo 1028606 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B3474035 : Blo 1028606 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B31720385 : Blo 1028606 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B3474683 : Blo 1028606 3474683 := bstep (se 1 (by rfl) ⟨2606012, by rfl⟩ : syracuseStep 3474683 = 5212025) B5212025
theorem B7931233 : Blo 1028606 7931233 := bstep (se 2 (by rfl) ⟨2974212, by rfl⟩ : syracuseStep 7931233 = 5948425) B5948425
theorem B3475115 : Blo 1028606 3475115 := bstep (se 1 (by rfl) ⟨2606336, by rfl⟩ : syracuseStep 3475115 = 5212673) B5212673
theorem B9537263 : Blo 1028606 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B3967775 : Blo 1028606 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B29756321 : Blo 1028606 29756321 := bstep (se 2 (by rfl) ⟨11158620, by rfl⟩ : syracuseStep 29756321 = 22317241) B22317241
theorem B86052041 : Blo 1028606 86052041 := bstep (se 2 (by rfl) ⟨32269515, by rfl⟩ : syracuseStep 86052041 = 64539031) B64539031
theorem B5213483 : Blo 1028606 5213483 := bstep (se 1 (by rfl) ⟨3910112, by rfl⟩ : syracuseStep 5213483 = 7820225) B7820225
theorem B1543487 : Blo 1028606 1543487 := bstep (se 1 (by rfl) ⟨1157615, by rfl⟩ : syracuseStep 1543487 = 2315231) B2315231
theorem B1543871 : Blo 1028606 1543871 := bstep (se 1 (by rfl) ⟨1157903, by rfl⟩ : syracuseStep 1543871 = 2315807) B2315807
theorem B1740575 : Blo 1028606 1740575 := bstep (se 1 (by rfl) ⟨1305431, by rfl⟩ : syracuseStep 1740575 = 2610863) B2610863
theorem B3477437 : Blo 1028606 3477437 := bstep (se 3 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 3477437 = 1304039) B1304039
theorem B1544219 : Blo 1028606 1544219 := bstep (se 1 (by rfl) ⟨1158164, by rfl⟩ : syracuseStep 1544219 = 2316329) B2316329
theorem B3477599 : Blo 1028606 3477599 := bstep (se 1 (by rfl) ⟨2608199, by rfl⟩ : syracuseStep 3477599 = 5216399) B5216399
theorem B2199815 : Blo 1028606 2199815 := bstep (se 1 (by rfl) ⟨1649861, by rfl⟩ : syracuseStep 2199815 = 3299723) B3299723
theorem B8163661 : Blo 1028606 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B1544639 : Blo 1028606 1544639 := bstep (se 1 (by rfl) ⟨1158479, by rfl⟩ : syracuseStep 1544639 = 2316959) B2316959
theorem B5575159 : Blo 1028606 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B1545257 : Blo 1028606 1545257 := bstep (se 2 (by rfl) ⟨579471, by rfl⟩ : syracuseStep 1545257 = 1158943) B1158943
theorem B1742107 : Blo 1028606 1742107 := bstep (se 1 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 1742107 = 2613161) B2613161
theorem B1545755 : Blo 1028606 1545755 := bstep (se 1 (by rfl) ⟨1159316, by rfl⟩ : syracuseStep 1545755 = 2318633) B2318633
theorem B31790711 : Blo 1028606 31790711 := bstep (se 1 (by rfl) ⟨23843033, by rfl⟩ : syracuseStep 31790711 = 47686067) B47686067
theorem B5215913 : Blo 1028606 5215913 := bstep (se 2 (by rfl) ⟨1955967, by rfl⟩ : syracuseStep 5215913 = 3911935) B3911935
theorem B1545935 : Blo 1028606 1545935 := bstep (se 1 (by rfl) ⟨1159451, by rfl⟩ : syracuseStep 1545935 = 2318903) B2318903
theorem B3479273 : Blo 1028606 3479273 := bstep (se 2 (by rfl) ⟨1304727, by rfl⟩ : syracuseStep 3479273 = 2609455) B2609455
theorem B1546175 : Blo 1028606 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B1546463 : Blo 1028606 1546463 := bstep (se 1 (by rfl) ⟨1159847, by rfl⟩ : syracuseStep 1546463 = 2319695) B2319695
theorem B1546523 : Blo 1028606 1546523 := bstep (se 1 (by rfl) ⟨1159892, by rfl⟩ : syracuseStep 1546523 = 2319785) B2319785
theorem B3906089 : Blo 1028606 3906089 := bstep (se 2 (by rfl) ⟨1464783, by rfl⟩ : syracuseStep 3906089 = 2929567) B2929567
theorem B3906103 : Blo 1028606 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B1546943 : Blo 1028606 1546943 := bstep (se 1 (by rfl) ⟨1160207, by rfl⟩ : syracuseStep 1546943 = 2320415) B2320415
theorem B3480407 : Blo 1028606 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B3480569 : Blo 1028606 3480569 := bstep (se 2 (by rfl) ⟨1305213, by rfl⟩ : syracuseStep 3480569 = 2610427) B2610427
theorem B1547495 : Blo 1028606 1547495 := bstep (se 1 (by rfl) ⟨1160621, by rfl⟩ : syracuseStep 1547495 = 2321243) B2321243
theorem B2203471 : Blo 1028606 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B3481487 : Blo 1028606 3481487 := bstep (se 1 (by rfl) ⟨2611115, by rfl⟩ : syracuseStep 3481487 = 5222231) B5222231
theorem B3481595 : Blo 1028606 3481595 := bstep (se 1 (by rfl) ⟨2611196, by rfl⟩ : syracuseStep 3481595 = 5222393) B5222393
theorem B1548425 : Blo 1028606 1548425 := bstep (se 2 (by rfl) ⟨580659, by rfl⟩ : syracuseStep 1548425 = 1161319) B1161319
theorem B3907865 : Blo 1028606 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B5218991 : Blo 1028606 5218991 := bstep (se 1 (by rfl) ⟨3914243, by rfl⟩ : syracuseStep 5218991 = 7828487) B7828487
theorem B3908321 : Blo 1028606 3908321 := bstep (se 2 (by rfl) ⟨1465620, by rfl⟩ : syracuseStep 3908321 = 2931241) B2931241
theorem B3482567 : Blo 1028606 3482567 := bstep (se 1 (by rfl) ⟨2611925, by rfl⟩ : syracuseStep 3482567 = 5223851) B5223851
theorem B731587585 : Blo 1028606 731587585 := bstep (se 2 (by rfl) ⟨274345344, by rfl⟩ : syracuseStep 731587585 = 548690689) B548690689
theorem B5874875 : Blo 1028606 5874875 := bstep (se 1 (by rfl) ⟨4406156, by rfl⟩ : syracuseStep 5874875 = 8812313) B8812313
theorem B3482999 : Blo 1028606 3482999 := bstep (se 1 (by rfl) ⟨2612249, by rfl⟩ : syracuseStep 3482999 = 5224499) B5224499
theorem B3483215 : Blo 1028606 3483215 := bstep (se 1 (by rfl) ⟨2612411, by rfl⟩ : syracuseStep 3483215 = 5224823) B5224823
theorem B3484079 : Blo 1028606 3484079 := bstep (se 1 (by rfl) ⟨2613059, by rfl⟩ : syracuseStep 3484079 = 5226119) B5226119
theorem B5941729 : Blo 1028606 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B7940717 : Blo 1028606 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B3910265 : Blo 1028606 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B8793107 : Blo 1028606 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B4402363 : Blo 1028606 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B6598111 : Blo 1028606 6598111 := bstep (se 1 (by rfl) ⟨4948583, by rfl⟩ : syracuseStep 6598111 = 9897167) B9897167
theorem B9907703 : Blo 1028606 9907703 := bstep (se 1 (by rfl) ⟨7430777, by rfl⟩ : syracuseStep 9907703 = 14861555) B14861555
theorem B1028639 : Blo 1028606 1028639 := bstep (se 1 (by rfl) ⟨771479, by rfl⟩ : syracuseStep 1028639 = 1542959) B1542959
theorem B1028719 : Blo 1028606 1028719 := bstep (se 1 (by rfl) ⟨771539, by rfl⟩ : syracuseStep 1028719 = 1543079) B1543079
theorem B1028839 : Blo 1028606 1028839 := bstep (se 1 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 1028839 = 1543259) B1543259
theorem B1028891 : Blo 1028606 1028891 := bstep (se 1 (by rfl) ⟨771668, by rfl⟩ : syracuseStep 1028891 = 1543337) B1543337
theorem B1160059 : Blo 1028606 1160059 := bstep (se 1 (by rfl) ⟨870044, by rfl⟩ : syracuseStep 1160059 = 1740089) B1740089
theorem B17609723 : Blo 1028606 17609723 := bstep (se 1 (by rfl) ⟨13207292, by rfl⟩ : syracuseStep 17609723 = 26414585) B26414585
theorem B1029167 : Blo 1028606 1029167 := bstep (se 1 (by rfl) ⟨771875, by rfl⟩ : syracuseStep 1029167 = 1543751) B1543751
theorem B1160239 : Blo 1028606 1160239 := bstep (se 1 (by rfl) ⟨870179, by rfl⟩ : syracuseStep 1160239 = 1740359) B1740359
theorem B1029287 : Blo 1028606 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B1029447 : Blo 1028606 1029447 := bstep (se 1 (by rfl) ⟨772085, by rfl⟩ : syracuseStep 1029447 = 1544171) B1544171
theorem B8795567 : Blo 1028606 8795567 := bstep (se 1 (by rfl) ⟨6596675, by rfl⟩ : syracuseStep 8795567 = 13193351) B13193351
theorem B31700807 : Blo 1028606 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B1030139 : Blo 1028606 1030139 := bstep (se 1 (by rfl) ⟨772604, by rfl⟩ : syracuseStep 1030139 = 1545209) B1545209
theorem B1161211 : Blo 1028606 1161211 := bstep (se 1 (by rfl) ⟨870908, by rfl⟩ : syracuseStep 1161211 = 1741817) B1741817
theorem B1030271 : Blo 1028606 1030271 := bstep (se 1 (by rfl) ⟨772703, by rfl⟩ : syracuseStep 1030271 = 1545407) B1545407
theorem B1161391 : Blo 1028606 1161391 := bstep (se 1 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 1161391 = 1742087) B1742087
theorem B1030367 : Blo 1028606 1030367 := bstep (se 1 (by rfl) ⟨772775, by rfl⟩ : syracuseStep 1030367 = 1545551) B1545551
theorem B1030427 : Blo 1028606 1030427 := bstep (se 1 (by rfl) ⟨772820, by rfl⟩ : syracuseStep 1030427 = 1545641) B1545641
theorem B1030463 : Blo 1028606 1030463 := bstep (se 1 (by rfl) ⟨772847, by rfl⟩ : syracuseStep 1030463 = 1545695) B1545695
theorem B1030527 : Blo 1028606 1030527 := bstep (se 1 (by rfl) ⟨772895, by rfl⟩ : syracuseStep 1030527 = 1545791) B1545791
theorem B1489279 : Blo 1028606 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B1030847 : Blo 1028606 1030847 := bstep (se 1 (by rfl) ⟨773135, by rfl⟩ : syracuseStep 1030847 = 1546271) B1546271
theorem B25082567 : Blo 1028606 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B4405985 : Blo 1028606 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B2603785 : Blo 1028606 2603785 := bstep (se 2 (by rfl) ⟨976419, by rfl⟩ : syracuseStep 2603785 = 1952839) B1952839
theorem B1031135 : Blo 1028606 1031135 := bstep (se 1 (by rfl) ⟨773351, by rfl⟩ : syracuseStep 1031135 = 1546703) B1546703
theorem B1031195 : Blo 1028606 1031195 := bstep (se 1 (by rfl) ⟨773396, by rfl⟩ : syracuseStep 1031195 = 1546793) B1546793
theorem B5225633 : Blo 1028606 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B1031335 : Blo 1028606 1031335 := bstep (se 1 (by rfl) ⟨773501, by rfl⟩ : syracuseStep 1031335 = 1547003) B1547003
theorem B1031419 : Blo 1028606 1031419 := bstep (se 1 (by rfl) ⟨773564, by rfl⟩ : syracuseStep 1031419 = 1547129) B1547129
theorem B6601985 : Blo 1028606 6601985 := bstep (se 2 (by rfl) ⟨2475744, by rfl⟩ : syracuseStep 6601985 = 4951489) B4951489
theorem B2932175 : Blo 1028606 2932175 := bstep (se 1 (by rfl) ⟨2199131, by rfl⟩ : syracuseStep 2932175 = 4398263) B4398263
theorem B6602471 : Blo 1028606 6602471 := bstep (se 1 (by rfl) ⟨4951853, by rfl⟩ : syracuseStep 6602471 = 9903707) B9903707
theorem B1031919 : Blo 1028606 1031919 := bstep (se 1 (by rfl) ⟨773939, by rfl⟩ : syracuseStep 1031919 = 1547879) B1547879
theorem B1032027 : Blo 1028606 1032027 := bstep (se 1 (by rfl) ⟨774020, by rfl⟩ : syracuseStep 1032027 = 1548041) B1548041
theorem B30130157 : Blo 1028606 30130157 := bstep (se 3 (by rfl) ⟨5649404, by rfl⟩ : syracuseStep 30130157 = 11298809) B11298809
theorem B1032175 : Blo 1028606 1032175 := bstep (se 1 (by rfl) ⟨774131, by rfl⟩ : syracuseStep 1032175 = 1548263) B1548263
theorem B1032255 : Blo 1028606 1032255 := bstep (se 1 (by rfl) ⟨774191, by rfl⟩ : syracuseStep 1032255 = 1548383) B1548383
theorem B1032295 : Blo 1028606 1032295 := bstep (se 1 (by rfl) ⟨774221, by rfl⟩ : syracuseStep 1032295 = 1548443) B1548443
theorem B1032351 : Blo 1028606 1032351 := bstep (se 1 (by rfl) ⟨774263, by rfl⟩ : syracuseStep 1032351 = 1548527) B1548527
theorem B1032603 : Blo 1028606 1032603 := bstep (se 1 (by rfl) ⟨774452, by rfl⟩ : syracuseStep 1032603 = 1548905) B1548905
theorem B228573605 : Blo 1028606 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B200884697 : Blo 1028606 200884697 := bstep (se 2 (by rfl) ⟨75331761, by rfl⟩ : syracuseStep 200884697 = 150663523) B150663523
theorem B1983143 : Blo 1028606 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B2933587 : Blo 1028606 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B3917555 : Blo 1028606 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B3721241 : Blo 1028606 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B2607329 : Blo 1028606 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B1100027 : Blo 1028606 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B2607673 : Blo 1028606 2607673 := bstep (se 2 (by rfl) ⟨977877, by rfl⟩ : syracuseStep 2607673 = 1955755) B1955755
theorem B2607835 : Blo 1028606 2607835 := bstep (se 1 (by rfl) ⟨1955876, by rfl⟩ : syracuseStep 2607835 = 3911753) B3911753
theorem B4771295 : Blo 1028606 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B14077415 : Blo 1028606 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B2936503 : Blo 1028606 2936503 := bstep (se 1 (by rfl) ⟨2202377, by rfl⟩ : syracuseStep 2936503 = 4404755) B4404755
theorem B1986503 : Blo 1028606 1986503 := bstep (se 1 (by rfl) ⟨1489877, by rfl⟩ : syracuseStep 1986503 = 2979755) B2979755
theorem B2609243 : Blo 1028606 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B2609273 : Blo 1028606 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B2314367 : Blo 1028606 2314367 := bstep (se 1 (by rfl) ⟨1735775, by rfl⟩ : syracuseStep 2314367 = 3471551) B3471551
theorem B3920015 : Blo 1028606 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B3134495 : Blo 1028606 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B2315375 : Blo 1028606 2315375 := bstep (se 1 (by rfl) ⟨1736531, by rfl⟩ : syracuseStep 2315375 = 3473063) B3473063
theorem B2315951 : Blo 1028606 2315951 := bstep (se 1 (by rfl) ⟨1736963, by rfl⟩ : syracuseStep 2315951 = 3473927) B3473927
theorem B2316203 : Blo 1028606 2316203 := bstep (se 1 (by rfl) ⟨1737152, by rfl⟩ : syracuseStep 2316203 = 3474305) B3474305
theorem B3758089 : Blo 1028606 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B2316563 : Blo 1028606 2316563 := bstep (se 1 (by rfl) ⟨1737422, by rfl⟩ : syracuseStep 2316563 = 3474845) B3474845
theorem B2611511 : Blo 1028606 2611511 := bstep (se 1 (by rfl) ⟨1958633, by rfl⟩ : syracuseStep 2611511 = 3917267) B3917267
theorem B7821683 : Blo 1028606 7821683 := bstep (se 1 (by rfl) ⟨5866262, by rfl⟩ : syracuseStep 7821683 = 11732525) B11732525
theorem B2316671 : Blo 1028606 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B3627391 : Blo 1028606 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B2316905 : Blo 1028606 2316905 := bstep (se 2 (by rfl) ⟨868839, by rfl⟩ : syracuseStep 2316905 = 1737679) B1737679
theorem B33414353 : Blo 1028606 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B29679047 : Blo 1028606 29679047 := bstep (se 1 (by rfl) ⟨22259285, by rfl⟩ : syracuseStep 29679047 = 44518571) B44518571
theorem B2318201 : Blo 1028606 2318201 := bstep (se 2 (by rfl) ⟨869325, by rfl⟩ : syracuseStep 2318201 = 1738651) B1738651
theorem B9887633 : Blo 1028606 9887633 := bstep (se 2 (by rfl) ⟨3707862, by rfl⟩ : syracuseStep 9887633 = 7415725) B7415725
theorem B2613455 : Blo 1028606 2613455 := bstep (se 1 (by rfl) ⟨1960091, by rfl⟩ : syracuseStep 2613455 = 3920183) B3920183
theorem B2319209 : Blo 1028606 2319209 := bstep (se 2 (by rfl) ⟨869703, by rfl⟩ : syracuseStep 2319209 = 1739407) B1739407
theorem B3302491 : Blo 1028606 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B96330971 : Blo 1028606 96330971 := bstep (se 1 (by rfl) ⟨72248228, by rfl⟩ : syracuseStep 96330971 = 144496457) B144496457
theorem B2090473 : Blo 1028606 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B1959689 : Blo 1028606 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B17622845 : Blo 1028606 17622845 := bstep (se 3 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 17622845 = 6608567) B6608567
theorem B1304743 : Blo 1028606 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B1239295 : Blo 1028606 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B7826057 : Blo 1028606 7826057 := bstep (se 2 (by rfl) ⟨2934771, by rfl⟩ : syracuseStep 7826057 = 5869543) B5869543
theorem B2321639 : Blo 1028606 2321639 := bstep (se 1 (by rfl) ⟨1741229, by rfl⟩ : syracuseStep 2321639 = 3482459) B3482459
theorem B1469983 : Blo 1028606 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B2322287 : Blo 1028606 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B3960863 : Blo 1028606 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B1306687 : Blo 1028606 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B2322539 : Blo 1028606 2322539 := bstep (se 1 (by rfl) ⟨1741904, by rfl⟩ : syracuseStep 2322539 = 3483809) B3483809
theorem B14872967 : Blo 1028606 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B4944473 : Blo 1028606 4944473 := bstep (se 2 (by rfl) ⟨1854177, by rfl⟩ : syracuseStep 4944473 = 3708355) B3708355
theorem B8352359 : Blo 1028606 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B7434989 : Blo 1028606 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B8811287 : Blo 1028606 8811287 := bstep (se 1 (by rfl) ⟨6608465, by rfl⟩ : syracuseStep 8811287 = 13216931) B13216931
theorem B5567675 : Blo 1028606 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B22248215 : Blo 1028606 22248215 := bstep (se 1 (by rfl) ⟨16686161, by rfl⟩ : syracuseStep 22248215 = 33372323) B33372323
theorem B3473171 : Blo 1028606 3473171 := bstep (se 1 (by rfl) ⟨2604878, by rfl⟩ : syracuseStep 3473171 = 5209757) B5209757
theorem B5209919 : Blo 1028606 5209919 := bstep (se 1 (by rfl) ⟨3907439, by rfl⟩ : syracuseStep 5209919 = 7814879) B7814879
theorem B3473387 : Blo 1028606 3473387 := bstep (se 1 (by rfl) ⟨2605040, by rfl⟩ : syracuseStep 3473387 = 5210081) B5210081
theorem B133923131 : Blo 1028606 133923131 := bstep (se 1 (by rfl) ⟨100442348, by rfl⟩ : syracuseStep 133923131 = 200884697) B200884697
theorem B6358175 : Blo 1028606 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B1738219 : Blo 1028606 1738219 := bstep (se 1 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 1738219 = 2607329) B2607329
theorem B3475655 : Blo 1028606 3475655 := bstep (se 1 (by rfl) ⟨2606741, by rfl⟩ : syracuseStep 3475655 = 5213483) B5213483
theorem B3180863 : Blo 1028606 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B1739495 : Blo 1028606 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B1739515 : Blo 1028606 1739515 := bstep (se 1 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 1739515 = 2609273) B2609273
theorem B8358653 : Blo 1028606 8358653 := bstep (se 3 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 8358653 = 3134495) B3134495
theorem B1542911 : Blo 1028606 1542911 := bstep (se 1 (by rfl) ⟨1157183, by rfl⟩ : syracuseStep 1542911 = 2314367) B2314367
theorem B1739657 : Blo 1028606 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B14847133 : Blo 1028606 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B1543583 : Blo 1028606 1543583 := bstep (se 1 (by rfl) ⟨1157687, by rfl⟩ : syracuseStep 1543583 = 2315375) B2315375
theorem B3476897 : Blo 1028606 3476897 := bstep (se 2 (by rfl) ⟨1303836, by rfl⟩ : syracuseStep 3476897 = 2607673) B2607673
theorem B3477113 : Blo 1028606 3477113 := bstep (se 2 (by rfl) ⟨1303917, by rfl⟩ : syracuseStep 3477113 = 2607835) B2607835
theorem B3477275 : Blo 1028606 3477275 := bstep (se 1 (by rfl) ⟨2607956, by rfl⟩ : syracuseStep 3477275 = 5215913) B5215913
theorem B1543967 : Blo 1028606 1543967 := bstep (se 1 (by rfl) ⟨1157975, by rfl⟩ : syracuseStep 1543967 = 2315951) B2315951
theorem B1544135 : Blo 1028606 1544135 := bstep (se 1 (by rfl) ⟨1158101, by rfl⟩ : syracuseStep 1544135 = 2316203) B2316203
theorem B1544375 : Blo 1028606 1544375 := bstep (se 1 (by rfl) ⟨1158281, by rfl⟩ : syracuseStep 1544375 = 2316563) B2316563
theorem B1741007 : Blo 1028606 1741007 := bstep (se 1 (by rfl) ⟨1305755, by rfl⟩ : syracuseStep 1741007 = 2611511) B2611511
theorem B5214455 : Blo 1028606 5214455 := bstep (se 1 (by rfl) ⟨3910841, by rfl⟩ : syracuseStep 5214455 = 7821683) B7821683
theorem B5869817 : Blo 1028606 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B1544447 : Blo 1028606 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1544603 : Blo 1028606 1544603 := bstep (se 1 (by rfl) ⟨1158452, by rfl⟩ : syracuseStep 1544603 = 2316905) B2316905
theorem B1545467 : Blo 1028606 1545467 := bstep (se 1 (by rfl) ⟨1159100, by rfl⟩ : syracuseStep 1545467 = 2318201) B2318201
theorem B6591755 : Blo 1028606 6591755 := bstep (se 1 (by rfl) ⟨4943816, by rfl⟩ : syracuseStep 6591755 = 9887633) B9887633
theorem B1742249 : Blo 1028606 1742249 := bstep (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) B1306687
theorem B1742303 : Blo 1028606 1742303 := bstep (se 1 (by rfl) ⟨1306727, by rfl⟩ : syracuseStep 1742303 = 2613455) B2613455
theorem B10884881 : Blo 1028606 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B3479327 : Blo 1028606 3479327 := bstep (se 1 (by rfl) ⟨2609495, by rfl⟩ : syracuseStep 3479327 = 5218991) B5218991
theorem B1546139 : Blo 1028606 1546139 := bstep (se 1 (by rfl) ⟨1159604, by rfl⟩ : syracuseStep 1546139 = 2319209) B2319209
theorem B1546745 : Blo 1028606 1546745 := bstep (se 2 (by rfl) ⟨580029, by rfl⟩ : syracuseStep 1546745 = 1160059) B1160059
theorem B1546985 : Blo 1028606 1546985 := bstep (se 2 (by rfl) ⟨580119, by rfl⟩ : syracuseStep 1546985 = 1160239) B1160239
theorem B5217371 : Blo 1028606 5217371 := bstep (se 1 (by rfl) ⟨3913028, by rfl⟩ : syracuseStep 5217371 = 7826057) B7826057
theorem B1547759 : Blo 1028606 1547759 := bstep (se 1 (by rfl) ⟨1160819, by rfl⟩ : syracuseStep 1547759 = 2321639) B2321639
theorem B1548191 : Blo 1028606 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B1548281 : Blo 1028606 1548281 := bstep (se 2 (by rfl) ⟨580605, by rfl⟩ : syracuseStep 1548281 = 1161211) B1161211
theorem B1548359 : Blo 1028606 1548359 := bstep (se 1 (by rfl) ⟨1161269, by rfl⟩ : syracuseStep 1548359 = 2322539) B2322539
theorem B1548521 : Blo 1028606 1548521 := bstep (se 2 (by rfl) ⟨580695, by rfl⟩ : syracuseStep 1548521 = 1161391) B1161391
theorem B4956659 : Blo 1028606 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B5874191 : Blo 1028606 5874191 := bstep (se 1 (by rfl) ⟨4405643, by rfl⟩ : syracuseStep 5874191 = 8811287) B8811287
theorem B11739815 : Blo 1028606 11739815 := bstep (se 1 (by rfl) ⟨8804861, by rfl⟩ : syracuseStep 11739815 = 17609723) B17609723
theorem B16721711 : Blo 1028606 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B3483755 : Blo 1028606 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B4401323 : Blo 1028606 4401323 := bstep (se 1 (by rfl) ⟨3300992, by rfl⟩ : syracuseStep 4401323 = 6601985) B6601985
theorem B4401647 : Blo 1028606 4401647 := bstep (se 1 (by rfl) ⟨3301235, by rfl⟩ : syracuseStep 4401647 = 6602471) B6602471
theorem B1157863 : Blo 1028606 1157863 := bstep (se 1 (by rfl) ⟨868397, by rfl⟩ : syracuseStep 1157863 = 1736795) B1736795
theorem B1158079 : Blo 1028606 1158079 := bstep (se 1 (by rfl) ⟨868559, by rfl⟩ : syracuseStep 1158079 = 1737119) B1737119
theorem B152382403 : Blo 1028606 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B7056443 : Blo 1028606 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B1322095 : Blo 1028606 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B21146923 : Blo 1028606 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B3911449 : Blo 1028606 3911449 := bstep (se 2 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 3911449 = 2933587) B2933587
theorem B975450113 : Blo 1028606 975450113 := bstep (se 2 (by rfl) ⟨365793792, by rfl⟩ : syracuseStep 975450113 = 731587585) B731587585
theorem B4403321 : Blo 1028606 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B19837547 : Blo 1028606 19837547 := bstep (se 1 (by rfl) ⟨14878160, by rfl⟩ : syracuseStep 19837547 = 29756321) B29756321
theorem B1028991 : Blo 1028606 1028991 := bstep (se 1 (by rfl) ⟨771743, by rfl⟩ : syracuseStep 1028991 = 1543487) B1543487
theorem B1029247 : Blo 1028606 1029247 := bstep (se 1 (by rfl) ⟨771935, by rfl⟩ : syracuseStep 1029247 = 1543871) B1543871
theorem B1160383 : Blo 1028606 1160383 := bstep (se 1 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 1160383 = 1740575) B1740575
theorem B1029479 : Blo 1028606 1029479 := bstep (se 1 (by rfl) ⟨772109, by rfl⟩ : syracuseStep 1029479 = 1544219) B1544219
theorem B1029759 : Blo 1028606 1029759 := bstep (se 1 (by rfl) ⟨772319, by rfl⟩ : syracuseStep 1029759 = 1544639) B1544639
theorem B1652393 : Blo 1028606 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B1030171 : Blo 1028606 1030171 := bstep (se 1 (by rfl) ⟨772628, by rfl⟩ : syracuseStep 1030171 = 1545257) B1545257
theorem B1030503 : Blo 1028606 1030503 := bstep (se 1 (by rfl) ⟨772877, by rfl⟩ : syracuseStep 1030503 = 1545755) B1545755
theorem B1030623 : Blo 1028606 1030623 := bstep (se 1 (by rfl) ⟨772967, by rfl⟩ : syracuseStep 1030623 = 1545935) B1545935
theorem B1030783 : Blo 1028606 1030783 := bstep (se 1 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 1030783 = 1546175) B1546175
theorem B1030975 : Blo 1028606 1030975 := bstep (se 1 (by rfl) ⟨773231, by rfl⟩ : syracuseStep 1030975 = 1546463) B1546463
theorem B1031015 : Blo 1028606 1031015 := bstep (se 1 (by rfl) ⟨773261, by rfl⟩ : syracuseStep 1031015 = 1546523) B1546523
theorem B2604059 : Blo 1028606 2604059 := bstep (se 1 (by rfl) ⟨1953044, by rfl⟩ : syracuseStep 2604059 = 3906089) B3906089
theorem B1031295 : Blo 1028606 1031295 := bstep (se 1 (by rfl) ⟨773471, by rfl⟩ : syracuseStep 1031295 = 1546943) B1546943
theorem B8797481 : Blo 1028606 8797481 := bstep (se 2 (by rfl) ⟨3299055, by rfl⟩ : syracuseStep 8797481 = 6598111) B6598111
theorem B1031663 : Blo 1028606 1031663 := bstep (se 1 (by rfl) ⟨773747, by rfl⟩ : syracuseStep 1031663 = 1547495) B1547495
theorem B3915337 : Blo 1028606 3915337 := bstep (se 2 (by rfl) ⟨1468251, by rfl⟩ : syracuseStep 3915337 = 2936503) B2936503
theorem B1032283 : Blo 1028606 1032283 := bstep (se 1 (by rfl) ⟨774212, by rfl⟩ : syracuseStep 1032283 = 1548425) B1548425
theorem B2605243 : Blo 1028606 2605243 := bstep (se 1 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 2605243 = 3907865) B3907865
theorem B2605547 : Blo 1028606 2605547 := bstep (se 1 (by rfl) ⟨1954160, by rfl⟩ : syracuseStep 2605547 = 3908321) B3908321
theorem B2933405 : Blo 1028606 2933405 := bstep (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) B1100027
theorem B3916583 : Blo 1028606 3916583 := bstep (se 1 (by rfl) ⟨2937437, by rfl⟩ : syracuseStep 3916583 = 5874875) B5874875
theorem B11748563 : Blo 1028606 11748563 := bstep (se 1 (by rfl) ⟨8811422, by rfl⟩ : syracuseStep 11748563 = 17622845) B17622845
theorem B5293811 : Blo 1028606 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2606843 : Blo 1028606 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B6605135 : Blo 1028606 6605135 := bstep (se 1 (by rfl) ⟨4953851, by rfl⟩ : syracuseStep 6605135 = 9907703) B9907703
theorem B2640575 : Blo 1028606 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B9915311 : Blo 1028606 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B3296315 : Blo 1028606 3296315 := bstep (se 1 (by rfl) ⟨2472236, by rfl⟩ : syracuseStep 3296315 = 4944473) B4944473
theorem B1985705 : Blo 1028606 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B4836521 : Blo 1028606 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B37539773 : Blo 1028606 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B2937323 : Blo 1028606 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B14832143 : Blo 1028606 14832143 := bstep (se 1 (by rfl) ⟨11124107, by rfl⟩ : syracuseStep 14832143 = 22248215) B22248215
theorem B21189365 : Blo 1028606 21189365 := bstep (se 5 (by rfl) ⟨993251, by rfl⟩ : syracuseStep 21189365 = 1986503) B1986503
theorem B1954783 : Blo 1028606 1954783 := bstep (se 1 (by rfl) ⟨1466087, by rfl⟩ : syracuseStep 1954783 = 2932175) B2932175
theorem B2937961 : Blo 1028606 2937961 := bstep (se 2 (by rfl) ⟨1101735, by rfl⟩ : syracuseStep 2937961 = 2203471) B2203471
theorem B2315447 : Blo 1028606 2315447 := bstep (se 1 (by rfl) ⟨1736585, by rfl⟩ : syracuseStep 2315447 = 3473171) B3473171
theorem B2315591 : Blo 1028606 2315591 := bstep (se 1 (by rfl) ⟨1736693, by rfl⟩ : syracuseStep 2315591 = 3473387) B3473387
theorem B2316023 : Blo 1028606 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B2316455 : Blo 1028606 2316455 := bstep (se 1 (by rfl) ⟨1737341, by rfl⟩ : syracuseStep 2316455 = 3474683) B3474683
theorem B2316743 : Blo 1028606 2316743 := bstep (se 1 (by rfl) ⟨1737557, by rfl⟩ : syracuseStep 2316743 = 3475115) B3475115
theorem B2611703 : Blo 1028606 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B10574977 : Blo 1028606 10574977 := bstep (se 2 (by rfl) ⟨3965616, by rfl⟩ : syracuseStep 10574977 = 7931233) B7931233
theorem B2645183 : Blo 1028606 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B57368027 : Blo 1028606 57368027 := bstep (se 1 (by rfl) ⟨43026020, by rfl⟩ : syracuseStep 57368027 = 86052041) B86052041
theorem B2318291 : Blo 1028606 2318291 := bstep (se 1 (by rfl) ⟨1738718, by rfl⟩ : syracuseStep 2318291 = 3477437) B3477437
theorem B2318399 : Blo 1028606 2318399 := bstep (se 1 (by rfl) ⟨1738799, by rfl⟩ : syracuseStep 2318399 = 3477599) B3477599
theorem B2613343 : Blo 1028606 2613343 := bstep (se 1 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 2613343 = 3920015) B3920015
theorem B1466543 : Blo 1028606 1466543 := bstep (se 1 (by rfl) ⟨1099907, by rfl⟩ : syracuseStep 1466543 = 2199815) B2199815
theorem B7922305 : Blo 1028606 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B21193807 : Blo 1028606 21193807 := bstep (se 1 (by rfl) ⟨15895355, by rfl⟩ : syracuseStep 21193807 = 31790711) B31790711
theorem B2319515 : Blo 1028606 2319515 := bstep (se 1 (by rfl) ⟨1739636, by rfl⟩ : syracuseStep 2319515 = 3479273) B3479273
theorem B2320271 : Blo 1028606 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B2320379 : Blo 1028606 2320379 := bstep (se 1 (by rfl) ⟨1740284, by rfl⟩ : syracuseStep 2320379 = 3480569) B3480569
theorem B1959977 : Blo 1028606 1959977 := bstep (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) B1469983
theorem B22276235 : Blo 1028606 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B19786031 : Blo 1028606 19786031 := bstep (se 1 (by rfl) ⟨14839523, by rfl⟩ : syracuseStep 19786031 = 29679047) B29679047
theorem B2320991 : Blo 1028606 2320991 := bstep (se 1 (by rfl) ⟨1740743, by rfl⟩ : syracuseStep 2320991 = 3481487) B3481487
theorem B2321063 : Blo 1028606 2321063 := bstep (se 1 (by rfl) ⟨1740797, by rfl⟩ : syracuseStep 2321063 = 3481595) B3481595
theorem B9923309 : Blo 1028606 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B2321711 : Blo 1028606 2321711 := bstep (se 1 (by rfl) ⟨1741283, by rfl⟩ : syracuseStep 2321711 = 3482567) B3482567
theorem B7433545 : Blo 1028606 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B64220647 : Blo 1028606 64220647 := bstep (se 1 (by rfl) ⟨48165485, by rfl⟩ : syracuseStep 64220647 = 96330971) B96330971
theorem B2321999 : Blo 1028606 2321999 := bstep (se 1 (by rfl) ⟨1741499, by rfl⟩ : syracuseStep 2321999 = 3482999) B3482999
theorem B2322143 : Blo 1028606 2322143 := bstep (se 1 (by rfl) ⟨1741607, by rfl⟩ : syracuseStep 2322143 = 3483215) B3483215
theorem B1306459 : Blo 1028606 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B2322719 : Blo 1028606 2322719 := bstep (se 1 (by rfl) ⟨1742039, by rfl⟩ : syracuseStep 2322719 = 3484079) B3484079
theorem B2322809 : Blo 1028606 2322809 := bstep (se 2 (by rfl) ⟨871053, by rfl⟩ : syracuseStep 2322809 = 1742107) B1742107
theorem B5862071 : Blo 1028606 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B5010785 : Blo 1028606 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B5568239 : Blo 1028606 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B5208137 : Blo 1028606 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B5863711 : Blo 1028606 5863711 := bstep (se 1 (by rfl) ⟨4397783, by rfl⟩ : syracuseStep 5863711 = 8795567) B8795567
theorem B3471713 : Blo 1028606 3471713 := bstep (se 2 (by rfl) ⟨1301892, by rfl⟩ : syracuseStep 3471713 = 2603785) B2603785
theorem B21133871 : Blo 1028606 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B44596757 : Blo 1028606 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B3473279 : Blo 1028606 3473279 := bstep (se 1 (by rfl) ⟨2604959, by rfl⟩ : syracuseStep 3473279 = 5209919) B5209919
theorem B80347085 : Blo 1028606 80347085 := bstep (se 3 (by rfl) ⟨15065078, by rfl⟩ : syracuseStep 80347085 = 30130157) B30130157
theorem B3473657 : Blo 1028606 3473657 := bstep (se 2 (by rfl) ⟨1302621, by rfl⟩ : syracuseStep 3473657 = 2605243) B2605243
theorem B1737031 : Blo 1028606 1737031 := bstep (se 1 (by rfl) ⟨1302773, by rfl⟩ : syracuseStep 1737031 = 2605547) B2605547
theorem B7832375 : Blo 1028606 7832375 := bstep (se 1 (by rfl) ⟨5874281, by rfl⟩ : syracuseStep 7832375 = 11748563) B11748563
theorem B1737895 : Blo 1028606 1737895 := bstep (se 1 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 1737895 = 2606843) B2606843
theorem B7832861 : Blo 1028606 7832861 := bstep (se 3 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 7832861 = 2937323) B2937323
theorem B5572435 : Blo 1028606 5572435 := bstep (se 1 (by rfl) ⟨4179326, by rfl⟩ : syracuseStep 5572435 = 8358653) B8358653
theorem B2197543 : Blo 1028606 2197543 := bstep (se 1 (by rfl) ⟨1648157, by rfl⟩ : syracuseStep 2197543 = 3296315) B3296315
theorem B3476303 : Blo 1028606 3476303 := bstep (se 1 (by rfl) ⟨2607227, by rfl⟩ : syracuseStep 3476303 = 5214455) B5214455
theorem B14126243 : Blo 1028606 14126243 := bstep (se 1 (by rfl) ⟨10594682, by rfl⟩ : syracuseStep 14126243 = 21189365) B21189365
theorem B1543631 : Blo 1028606 1543631 := bstep (se 1 (by rfl) ⟨1157723, by rfl⟩ : syracuseStep 1543631 = 2315447) B2315447
theorem B4394503 : Blo 1028606 4394503 := bstep (se 1 (by rfl) ⟨3295877, by rfl⟩ : syracuseStep 4394503 = 6591755) B6591755
theorem B1543727 : Blo 1028606 1543727 := bstep (se 1 (by rfl) ⟨1157795, by rfl⟩ : syracuseStep 1543727 = 2315591) B2315591
theorem B1543817 : Blo 1028606 1543817 := bstep (se 2 (by rfl) ⟨578931, by rfl⟩ : syracuseStep 1543817 = 1157863) B1157863
theorem B1544015 : Blo 1028606 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B1544105 : Blo 1028606 1544105 := bstep (se 2 (by rfl) ⟨579039, by rfl⟩ : syracuseStep 1544105 = 1158079) B1158079
theorem B1544303 : Blo 1028606 1544303 := bstep (se 1 (by rfl) ⟨1158227, by rfl⟩ : syracuseStep 1544303 = 2316455) B2316455
theorem B19796177 : Blo 1028606 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B1544495 : Blo 1028606 1544495 := bstep (se 1 (by rfl) ⟨1158371, by rfl⟩ : syracuseStep 1544495 = 2316743) B2316743
theorem B1741135 : Blo 1028606 1741135 := bstep (se 1 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 1741135 = 2611703) B2611703
theorem B85627529 : Blo 1028606 85627529 := bstep (se 2 (by rfl) ⟨32110323, by rfl⟩ : syracuseStep 85627529 = 64220647) B64220647
theorem B3478247 : Blo 1028606 3478247 := bstep (se 1 (by rfl) ⟨2608685, by rfl⟩ : syracuseStep 3478247 = 5217371) B5217371
theorem B38245351 : Blo 1028606 38245351 := bstep (se 1 (by rfl) ⟨28684013, by rfl⟩ : syracuseStep 38245351 = 57368027) B57368027
theorem B5215265 : Blo 1028606 5215265 := bstep (se 2 (by rfl) ⟨1955724, by rfl⟩ : syracuseStep 5215265 = 3911449) B3911449
theorem B1741945 : Blo 1028606 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B1545527 : Blo 1028606 1545527 := bstep (se 1 (by rfl) ⟨1159145, by rfl⟩ : syracuseStep 1545527 = 2318291) B2318291
theorem B1545599 : Blo 1028606 1545599 := bstep (se 1 (by rfl) ⟨1159199, by rfl⟩ : syracuseStep 1545599 = 2318399) B2318399
theorem B1546343 : Blo 1028606 1546343 := bstep (se 1 (by rfl) ⟨1159757, by rfl⟩ : syracuseStep 1546343 = 2319515) B2319515
theorem B11147807 : Blo 1028606 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B1546847 : Blo 1028606 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B1546919 : Blo 1028606 1546919 := bstep (se 1 (by rfl) ⟨1160189, by rfl⟩ : syracuseStep 1546919 = 2320379) B2320379
theorem B1547177 : Blo 1028606 1547177 := bstep (se 2 (by rfl) ⟨580191, by rfl⟩ : syracuseStep 1547177 = 1160383) B1160383
theorem B1547327 : Blo 1028606 1547327 := bstep (se 1 (by rfl) ⟨1160495, by rfl⟩ : syracuseStep 1547327 = 2320991) B2320991
theorem B1547375 : Blo 1028606 1547375 := bstep (se 1 (by rfl) ⟨1160531, by rfl⟩ : syracuseStep 1547375 = 2321063) B2321063
theorem B1547807 : Blo 1028606 1547807 := bstep (se 1 (by rfl) ⟨1160855, by rfl⟩ : syracuseStep 1547807 = 2321711) B2321711
theorem B1547999 : Blo 1028606 1547999 := bstep (se 1 (by rfl) ⟨1160999, by rfl⟩ : syracuseStep 1547999 = 2321999) B2321999
theorem B1548095 : Blo 1028606 1548095 := bstep (se 1 (by rfl) ⟨1161071, by rfl⟩ : syracuseStep 1548095 = 2322143) B2322143
theorem B18817181 : Blo 1028606 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B1548479 : Blo 1028606 1548479 := bstep (se 1 (by rfl) ⟨1161359, by rfl⟩ : syracuseStep 1548479 = 2322719) B2322719
theorem B1548539 : Blo 1028606 1548539 := bstep (se 1 (by rfl) ⟨1161404, by rfl⟩ : syracuseStep 1548539 = 2322809) B2322809
theorem B3908047 : Blo 1028606 3908047 := bstep (se 1 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 3908047 = 5862071) B5862071
theorem B3712159 : Blo 1028606 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B14099969 : Blo 1028606 14099969 := bstep (se 2 (by rfl) ⟨5287488, by rfl⟩ : syracuseStep 14099969 = 10574977) B10574977
theorem B5220449 : Blo 1028606 5220449 := bstep (se 2 (by rfl) ⟨1957668, by rfl⟩ : syracuseStep 5220449 = 3915337) B3915337
theorem B29731171 : Blo 1028606 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B3484457 : Blo 1028606 3484457 := bstep (se 2 (by rfl) ⟨1306671, by rfl⟩ : syracuseStep 3484457 = 2613343) B2613343
theorem B3910781 : Blo 1028606 3910781 := bstep (se 3 (by rfl) ⟨733271, by rfl⟩ : syracuseStep 3910781 = 1466543) B1466543
theorem B4238783 : Blo 1028606 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B28258409 : Blo 1028606 28258409 := bstep (se 2 (by rfl) ⟨10596903, by rfl⟩ : syracuseStep 28258409 = 21193807) B21193807
theorem B4403423 : Blo 1028606 4403423 := bstep (se 1 (by rfl) ⟨3302567, by rfl⟩ : syracuseStep 4403423 = 6605135) B6605135
theorem B1159663 : Blo 1028606 1159663 := bstep (se 1 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 1159663 = 1739495) B1739495
theorem B1028607 : Blo 1028606 1028607 := bstep (se 1 (by rfl) ⟨771455, by rfl⟩ : syracuseStep 1028607 = 1542911) B1542911
theorem B1159771 : Blo 1028606 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B1323803 : Blo 1028606 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1029055 : Blo 1028606 1029055 := bstep (se 1 (by rfl) ⟨771791, by rfl⟩ : syracuseStep 1029055 = 1543583) B1543583
theorem B1029311 : Blo 1028606 1029311 := bstep (se 1 (by rfl) ⟨771983, by rfl⟩ : syracuseStep 1029311 = 1543967) B1543967
theorem B1029423 : Blo 1028606 1029423 := bstep (se 1 (by rfl) ⟨772067, by rfl⟩ : syracuseStep 1029423 = 1544135) B1544135
theorem B1029583 : Blo 1028606 1029583 := bstep (se 1 (by rfl) ⟨772187, by rfl⟩ : syracuseStep 1029583 = 1544375) B1544375
theorem B1160671 : Blo 1028606 1160671 := bstep (se 1 (by rfl) ⟨870503, by rfl⟩ : syracuseStep 1160671 = 1741007) B1741007
theorem B3913211 : Blo 1028606 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B1029631 : Blo 1028606 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B1029735 : Blo 1028606 1029735 := bstep (se 1 (by rfl) ⟨772301, by rfl⟩ : syracuseStep 1029735 = 1544603) B1544603
theorem B42252293 : Blo 1028606 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B1030311 : Blo 1028606 1030311 := bstep (se 1 (by rfl) ⟨772733, by rfl⟩ : syracuseStep 1030311 = 1545467) B1545467
theorem B1161499 : Blo 1028606 1161499 := bstep (se 1 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 1161499 = 1742249) B1742249
theorem B1161535 : Blo 1028606 1161535 := bstep (se 1 (by rfl) ⟨871151, by rfl⟩ : syracuseStep 1161535 = 1742303) B1742303
theorem B7256587 : Blo 1028606 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B1030759 : Blo 1028606 1030759 := bstep (se 1 (by rfl) ⟨773069, by rfl⟩ : syracuseStep 1030759 = 1546139) B1546139
theorem B1031163 : Blo 1028606 1031163 := bstep (se 1 (by rfl) ⟨773372, by rfl⟩ : syracuseStep 1031163 = 1546745) B1546745
theorem B9911393 : Blo 1028606 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B1031323 : Blo 1028606 1031323 := bstep (se 1 (by rfl) ⟨773492, by rfl⟩ : syracuseStep 1031323 = 1546985) B1546985
theorem B1031839 : Blo 1028606 1031839 := bstep (se 1 (by rfl) ⟨773879, by rfl⟩ : syracuseStep 1031839 = 1547759) B1547759
theorem B1032127 : Blo 1028606 1032127 := bstep (se 1 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 1032127 = 1548191) B1548191
theorem B1032187 : Blo 1028606 1032187 := bstep (se 1 (by rfl) ⟨774140, by rfl⟩ : syracuseStep 1032187 = 1548281) B1548281
theorem B1032239 : Blo 1028606 1032239 := bstep (se 1 (by rfl) ⟨774179, by rfl⟩ : syracuseStep 1032239 = 1548359) B1548359
theorem B5226605 : Blo 1028606 5226605 := bstep (se 3 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 5226605 = 1959977) B1959977
theorem B1032347 : Blo 1028606 1032347 := bstep (se 1 (by rfl) ⟨774260, by rfl⟩ : syracuseStep 1032347 = 1548521) B1548521
theorem B3916127 : Blo 1028606 3916127 := bstep (se 1 (by rfl) ⟨2937095, by rfl⟩ : syracuseStep 3916127 = 5874191) B5874191
theorem B2606377 : Blo 1028606 2606377 := bstep (se 2 (by rfl) ⟨977391, by rfl⟩ : syracuseStep 2606377 = 1954783) B1954783
theorem B2934215 : Blo 1028606 2934215 := bstep (se 1 (by rfl) ⟨2200661, by rfl⟩ : syracuseStep 2934215 = 4401323) B4401323
theorem B3917281 : Blo 1028606 3917281 := bstep (se 2 (by rfl) ⟨1468980, by rfl⟩ : syracuseStep 3917281 = 2937961) B2937961
theorem B13190687 : Blo 1028606 13190687 := bstep (se 1 (by rfl) ⟨9893015, by rfl⟩ : syracuseStep 13190687 = 19786031) B19786031
theorem B2934431 : Blo 1028606 2934431 := bstep (se 1 (by rfl) ⟨2200823, by rfl⟩ : syracuseStep 2934431 = 4401647) B4401647
theorem B650300075 : Blo 1028606 650300075 := bstep (se 1 (by rfl) ⟨487725056, by rfl⟩ : syracuseStep 650300075 = 975450113) B975450113
theorem B2935547 : Blo 1028606 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B7818281 : Blo 1028606 7818281 := bstep (se 2 (by rfl) ⟨2931855, by rfl⟩ : syracuseStep 7818281 = 5863711) B5863711
theorem B13225031 : Blo 1028606 13225031 := bstep (se 1 (by rfl) ⟨9918773, by rfl⟩ : syracuseStep 13225031 = 19837547) B19837547
theorem B12897389 : Blo 1028606 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B1101595 : Blo 1028606 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B2314475 : Blo 1028606 2314475 := bstep (se 1 (by rfl) ⟨1735856, by rfl⟩ : syracuseStep 2314475 = 3471713) B3471713
theorem B2315519 : Blo 1028606 2315519 := bstep (se 1 (by rfl) ⟨1736639, by rfl⟩ : syracuseStep 2315519 = 3473279) B3473279
theorem B53564723 : Blo 1028606 53564723 := bstep (se 1 (by rfl) ⟨40173542, by rfl⟩ : syracuseStep 53564723 = 80347085) B80347085
theorem B89282087 : Blo 1028606 89282087 := bstep (se 1 (by rfl) ⟨66961565, by rfl⟩ : syracuseStep 89282087 = 133923131) B133923131
theorem B1955603 : Blo 1028606 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B2611055 : Blo 1028606 2611055 := bstep (se 1 (by rfl) ⟨1958291, by rfl⟩ : syracuseStep 2611055 = 3916583) B3916583
theorem B3529207 : Blo 1028606 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B2317103 : Blo 1028606 2317103 := bstep (se 1 (by rfl) ⟨1737827, by rfl⟩ : syracuseStep 2317103 = 3475655) B3475655
theorem B2120575 : Blo 1028606 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B1760383 : Blo 1028606 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B2317625 : Blo 1028606 2317625 := bstep (se 2 (by rfl) ⟨869109, by rfl⟩ : syracuseStep 2317625 = 1738219) B1738219
theorem B2317931 : Blo 1028606 2317931 := bstep (se 1 (by rfl) ⟨1738448, by rfl⟩ : syracuseStep 2317931 = 3476897) B3476897
theorem B2318075 : Blo 1028606 2318075 := bstep (se 1 (by rfl) ⟨1738556, by rfl⟩ : syracuseStep 2318075 = 3477113) B3477113
theorem B2318183 : Blo 1028606 2318183 := bstep (se 1 (by rfl) ⟨1738637, by rfl⟩ : syracuseStep 2318183 = 3477275) B3477275
theorem B25026515 : Blo 1028606 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B9888095 : Blo 1028606 9888095 := bstep (se 1 (by rfl) ⟨7416071, by rfl⟩ : syracuseStep 9888095 = 14832143) B14832143
theorem B2319353 : Blo 1028606 2319353 := bstep (se 2 (by rfl) ⟨869757, by rfl⟩ : syracuseStep 2319353 = 1739515) B1739515
theorem B2319551 : Blo 1028606 2319551 := bstep (se 1 (by rfl) ⟨1739663, by rfl⟩ : syracuseStep 2319551 = 3479327) B3479327
theorem B1762793 : Blo 1028606 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B1763455 : Blo 1028606 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B812706149 : Blo 1028606 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B3304439 : Blo 1028606 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B59403293 : Blo 1028606 59403293 := bstep (se 3 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 59403293 = 22276235) B22276235
theorem B7826543 : Blo 1028606 7826543 := bstep (se 1 (by rfl) ⟨5869907, by rfl⟩ : syracuseStep 7826543 = 11739815) B11739815
theorem B2322503 : Blo 1028606 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B112783589 : Blo 1028606 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B6615539 : Blo 1028606 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B26440829 : Blo 1028606 26440829 := bstep (se 3 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 26440829 = 9915311) B9915311
theorem B3340523 : Blo 1028606 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B3472091 : Blo 1028606 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B14089247 : Blo 1028606 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B1736039 : Blo 1028606 1736039 := bstep (se 1 (by rfl) ⟨1302029, by rfl⟩ : syracuseStep 1736039 = 2604059) B2604059
theorem B5864987 : Blo 1028606 5864987 := bstep (se 1 (by rfl) ⟨4398740, by rfl⟩ : syracuseStep 5864987 = 8797481) B8797481
theorem B5210729 : Blo 1028606 5210729 := bstep (se 2 (by rfl) ⟨1954023, by rfl⟩ : syracuseStep 5210729 = 3908047) B3908047
theorem B3475169 : Blo 1028606 3475169 := bstep (se 2 (by rfl) ⟨1303188, by rfl⟩ : syracuseStep 3475169 = 2606377) B2606377
theorem B5212187 : Blo 1028606 5212187 := bstep (se 1 (by rfl) ⟨3909140, by rfl⟩ : syracuseStep 5212187 = 7818281) B7818281
theorem B8816687 : Blo 1028606 8816687 := bstep (se 1 (by rfl) ⟨6612515, by rfl⟩ : syracuseStep 8816687 = 13225031) B13225031
theorem B1542983 : Blo 1028606 1542983 := bstep (se 1 (by rfl) ⟨1157237, by rfl⟩ : syracuseStep 1542983 = 2314475) B2314475
theorem B57085019 : Blo 1028606 57085019 := bstep (se 1 (by rfl) ⟨42813764, by rfl⟩ : syracuseStep 57085019 = 85627529) B85627529
theorem B3476843 : Blo 1028606 3476843 := bstep (se 1 (by rfl) ⟨2607632, by rfl⟩ : syracuseStep 3476843 = 5215265) B5215265
theorem B1543679 : Blo 1028606 1543679 := bstep (se 1 (by rfl) ⟨1157759, by rfl⟩ : syracuseStep 1543679 = 2315519) B2315519
theorem B1740703 : Blo 1028606 1740703 := bstep (se 1 (by rfl) ⟨1305527, by rfl⟩ : syracuseStep 1740703 = 2611055) B2611055
theorem B1544735 : Blo 1028606 1544735 := bstep (se 1 (by rfl) ⟨1158551, by rfl⟩ : syracuseStep 1544735 = 2317103) B2317103
theorem B5214941 : Blo 1028606 5214941 := bstep (se 3 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 5214941 = 1955603) B1955603
theorem B1545083 : Blo 1028606 1545083 := bstep (se 1 (by rfl) ⟨1158812, by rfl⟩ : syracuseStep 1545083 = 2317625) B2317625
theorem B1545287 : Blo 1028606 1545287 := bstep (se 1 (by rfl) ⟨1158965, by rfl⟩ : syracuseStep 1545287 = 2317931) B2317931
theorem B1545383 : Blo 1028606 1545383 := bstep (se 1 (by rfl) ⟨1159037, by rfl⟩ : syracuseStep 1545383 = 2318075) B2318075
theorem B1545455 : Blo 1028606 1545455 := bstep (se 1 (by rfl) ⟨1159091, by rfl⟩ : syracuseStep 1545455 = 2318183) B2318183
theorem B16684343 : Blo 1028606 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B6592063 : Blo 1028606 6592063 := bstep (se 1 (by rfl) ⟨4944047, by rfl⟩ : syracuseStep 6592063 = 9888095) B9888095
theorem B1546217 : Blo 1028606 1546217 := bstep (se 2 (by rfl) ⟨579831, by rfl⟩ : syracuseStep 1546217 = 1159663) B1159663
theorem B1546235 : Blo 1028606 1546235 := bstep (se 1 (by rfl) ⟨1159676, by rfl⟩ : syracuseStep 1546235 = 2319353) B2319353
theorem B1546361 : Blo 1028606 1546361 := bstep (se 2 (by rfl) ⟨579885, by rfl⟩ : syracuseStep 1546361 = 1159771) B1159771
theorem B1546367 : Blo 1028606 1546367 := bstep (se 1 (by rfl) ⟨1159775, by rfl⟩ : syracuseStep 1546367 = 2319551) B2319551
theorem B19798181 : Blo 1028606 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B50993801 : Blo 1028606 50993801 := bstep (se 2 (by rfl) ⟨19122675, by rfl⟩ : syracuseStep 50993801 = 38245351) B38245351
theorem B3480299 : Blo 1028606 3480299 := bstep (se 1 (by rfl) ⟨2610224, by rfl⟩ : syracuseStep 3480299 = 5220449) B5220449
theorem B1547561 : Blo 1028606 1547561 := bstep (se 2 (by rfl) ⟨580335, by rfl⟩ : syracuseStep 1547561 = 1160671) B1160671
theorem B2202959 : Blo 1028606 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B5217695 : Blo 1028606 5217695 := bstep (se 1 (by rfl) ⟨3913271, by rfl⟩ : syracuseStep 5217695 = 7826543) B7826543
theorem B2825855 : Blo 1028606 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B1548335 : Blo 1028606 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B1548665 : Blo 1028606 1548665 := bstep (se 2 (by rfl) ⟨580749, by rfl⟩ : syracuseStep 1548665 = 1161499) B1161499
theorem B1548713 : Blo 1028606 1548713 := bstep (se 2 (by rfl) ⟨580767, by rfl⟩ : syracuseStep 1548713 = 1161535) B1161535
theorem B9675449 : Blo 1028606 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B2827433 : Blo 1028606 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B1157359 : Blo 1028606 1157359 := bstep (se 1 (by rfl) ⟨868019, by rfl⟩ : syracuseStep 1157359 = 1736039) B1736039
theorem B3909991 : Blo 1028606 3909991 := bstep (se 1 (by rfl) ⟨2932493, by rfl⟩ : syracuseStep 3909991 = 5864987) B5864987
theorem B3484403 : Blo 1028606 3484403 := bstep (se 1 (by rfl) ⟨2613302, by rfl⟩ : syracuseStep 3484403 = 5226605) B5226605
theorem B5221583 : Blo 1028606 5221583 := bstep (se 1 (by rfl) ⟨3916187, by rfl⟩ : syracuseStep 5221583 = 7832375) B7832375
theorem B5221907 : Blo 1028606 5221907 := bstep (se 1 (by rfl) ⟨3916430, by rfl⟩ : syracuseStep 5221907 = 7832861) B7832861
theorem B8793791 : Blo 1028606 8793791 := bstep (se 1 (by rfl) ⟨6595343, by rfl⟩ : syracuseStep 8793791 = 13190687) B13190687
theorem B433533383 : Blo 1028606 433533383 := bstep (se 1 (by rfl) ⟨325150037, by rfl⟩ : syracuseStep 433533383 = 650300075) B650300075
theorem B5223041 : Blo 1028606 5223041 := bstep (se 2 (by rfl) ⟨1958640, by rfl⟩ : syracuseStep 5223041 = 3917281) B3917281
theorem B8598259 : Blo 1028606 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B1029087 : Blo 1028606 1029087 := bstep (se 1 (by rfl) ⟨771815, by rfl⟩ : syracuseStep 1029087 = 1543631) B1543631
theorem B1029151 : Blo 1028606 1029151 := bstep (se 1 (by rfl) ⟨771863, by rfl⟩ : syracuseStep 1029151 = 1543727) B1543727
theorem B1029211 : Blo 1028606 1029211 := bstep (se 1 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 1029211 = 1543817) B1543817
theorem B1029343 : Blo 1028606 1029343 := bstep (se 1 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 1029343 = 1544015) B1544015
theorem B1029403 : Blo 1028606 1029403 := bstep (se 1 (by rfl) ⟨772052, by rfl⟩ : syracuseStep 1029403 = 1544105) B1544105
theorem B2930057 : Blo 1028606 2930057 := bstep (se 2 (by rfl) ⟨1098771, by rfl⟩ : syracuseStep 2930057 = 2197543) B2197543
theorem B1029535 : Blo 1028606 1029535 := bstep (se 1 (by rfl) ⟨772151, by rfl⟩ : syracuseStep 1029535 = 1544303) B1544303
theorem B1029663 : Blo 1028606 1029663 := bstep (se 1 (by rfl) ⟨772247, by rfl⟩ : syracuseStep 1029663 = 1544495) B1544495
theorem B1030351 : Blo 1028606 1030351 := bstep (se 1 (by rfl) ⟨772763, by rfl⟩ : syracuseStep 1030351 = 1545527) B1545527
theorem B1030399 : Blo 1028606 1030399 := bstep (se 1 (by rfl) ⟨772799, by rfl⟩ : syracuseStep 1030399 = 1545599) B1545599
theorem B59521391 : Blo 1028606 59521391 := bstep (se 1 (by rfl) ⟨44641043, by rfl⟩ : syracuseStep 59521391 = 89282087) B89282087
theorem B1030895 : Blo 1028606 1030895 := bstep (se 1 (by rfl) ⟨773171, by rfl⟩ : syracuseStep 1030895 = 1546343) B1546343
theorem B1031231 : Blo 1028606 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B1031279 : Blo 1028606 1031279 := bstep (se 1 (by rfl) ⟨773459, by rfl⟩ : syracuseStep 1031279 = 1546919) B1546919
theorem B1031451 : Blo 1028606 1031451 := bstep (se 1 (by rfl) ⟨773588, by rfl⟩ : syracuseStep 1031451 = 1547177) B1547177
theorem B1031551 : Blo 1028606 1031551 := bstep (se 1 (by rfl) ⟨773663, by rfl⟩ : syracuseStep 1031551 = 1547327) B1547327
theorem B1031583 : Blo 1028606 1031583 := bstep (se 1 (by rfl) ⟨773687, by rfl⟩ : syracuseStep 1031583 = 1547375) B1547375
theorem B1031871 : Blo 1028606 1031871 := bstep (se 1 (by rfl) ⟨773903, by rfl⟩ : syracuseStep 1031871 = 1547807) B1547807
theorem B1031999 : Blo 1028606 1031999 := bstep (se 1 (by rfl) ⟨773999, by rfl⟩ : syracuseStep 1031999 = 1547999) B1547999
theorem B1032063 : Blo 1028606 1032063 := bstep (se 1 (by rfl) ⟨774047, by rfl⟩ : syracuseStep 1032063 = 1548095) B1548095
theorem B1032319 : Blo 1028606 1032319 := bstep (se 1 (by rfl) ⟨774239, by rfl⟩ : syracuseStep 1032319 = 1548479) B1548479
theorem B1032359 : Blo 1028606 1032359 := bstep (se 1 (by rfl) ⟨774269, by rfl⟩ : syracuseStep 1032359 = 1548539) B1548539
theorem B9388709 : Blo 1028606 9388709 := bstep (se 4 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 9388709 = 1760383) B1760383
theorem B541804099 : Blo 1028606 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B39602195 : Blo 1028606 39602195 := bstep (se 1 (by rfl) ⟨29701646, by rfl⟩ : syracuseStep 39602195 = 59403293) B59403293
theorem B2607187 : Blo 1028606 2607187 := bstep (se 1 (by rfl) ⟨1955390, by rfl⟩ : syracuseStep 2607187 = 3910781) B3910781
theorem B2935615 : Blo 1028606 2935615 := bstep (se 1 (by rfl) ⟨2201711, by rfl⟩ : syracuseStep 2935615 = 4403423) B4403423
theorem B75189059 : Blo 1028606 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B4410359 : Blo 1028606 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B37669981 : Blo 1028606 37669981 := bstep (se 3 (by rfl) ⟨7063121, by rfl⟩ : syracuseStep 37669981 = 14126243) B14126243
theorem B4705609 : Blo 1028606 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B2608807 : Blo 1028606 2608807 := bstep (se 1 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 2608807 = 3913211) B3913211
theorem B28168195 : Blo 1028606 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B2314727 : Blo 1028606 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B9392831 : Blo 1028606 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B6607595 : Blo 1028606 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B2315771 : Blo 1028606 2315771 := bstep (se 1 (by rfl) ⟨1736828, by rfl⟩ : syracuseStep 2315771 = 3473657) B3473657
theorem B2610751 : Blo 1028606 2610751 := bstep (se 1 (by rfl) ⟨1958063, by rfl⟩ : syracuseStep 2610751 = 3916127) B3916127
theorem B2316041 : Blo 1028606 2316041 := bstep (se 2 (by rfl) ⟨868515, by rfl⟩ : syracuseStep 2316041 = 1737031) B1737031
theorem B1956143 : Blo 1028606 1956143 := bstep (se 1 (by rfl) ⟨1467107, by rfl⟩ : syracuseStep 1956143 = 2934215) B2934215
theorem B1956287 : Blo 1028606 1956287 := bstep (se 1 (by rfl) ⟨1467215, by rfl⟩ : syracuseStep 1956287 = 2934431) B2934431
theorem B2317193 : Blo 1028606 2317193 := bstep (se 2 (by rfl) ⟨868947, by rfl⟩ : syracuseStep 2317193 = 1737895) B1737895
theorem B1957031 : Blo 1028606 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B2317535 : Blo 1028606 2317535 := bstep (se 1 (by rfl) ⟨1738151, by rfl⟩ : syracuseStep 2317535 = 3476303) B3476303
theorem B3530141 : Blo 1028606 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B7429913 : Blo 1028606 7429913 := bstep (se 2 (by rfl) ⟨2786217, by rfl⟩ : syracuseStep 7429913 = 5572435) B5572435
theorem B13197451 : Blo 1028606 13197451 := bstep (se 1 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 13197451 = 19796177) B19796177
theorem B2351273 : Blo 1028606 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B39641561 : Blo 1028606 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B2318831 : Blo 1028606 2318831 := bstep (se 1 (by rfl) ⟨1739123, by rfl⟩ : syracuseStep 2318831 = 3478247) B3478247
theorem B35709815 : Blo 1028606 35709815 := bstep (se 1 (by rfl) ⟨26782361, by rfl⟩ : syracuseStep 35709815 = 53564723) B53564723
theorem B7431871 : Blo 1028606 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B5859337 : Blo 1028606 5859337 := bstep (se 2 (by rfl) ⟨2197251, by rfl⟩ : syracuseStep 5859337 = 4394503) B4394503
theorem B1468793 : Blo 1028606 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B12544787 : Blo 1028606 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B2321513 : Blo 1028606 2321513 := bstep (se 2 (by rfl) ⟨870567, by rfl⟩ : syracuseStep 2321513 = 1741135) B1741135
theorem B8908061 : Blo 1028606 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B1175195 : Blo 1028606 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B9399979 : Blo 1028606 9399979 := bstep (se 1 (by rfl) ⟨7049984, by rfl⟩ : syracuseStep 9399979 = 14099969) B14099969
theorem B2322593 : Blo 1028606 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B2322971 : Blo 1028606 2322971 := bstep (se 1 (by rfl) ⟨1742228, by rfl⟩ : syracuseStep 2322971 = 3484457) B3484457
theorem B18838939 : Blo 1028606 18838939 := bstep (se 1 (by rfl) ⟨14129204, by rfl⟩ : syracuseStep 18838939 = 28258409) B28258409
theorem B17627219 : Blo 1028606 17627219 := bstep (se 1 (by rfl) ⟨13220414, by rfl⟩ : syracuseStep 17627219 = 26440829) B26440829
theorem B17596601 : Blo 1028606 17596601 := bstep (se 2 (by rfl) ⟨6598725, by rfl⟩ : syracuseStep 17596601 = 13197451) B13197451
theorem B3473819 : Blo 1028606 3473819 := bstep (se 1 (by rfl) ⟨2605364, by rfl⟩ : syracuseStep 3473819 = 5210729) B5210729
theorem B6259139 : Blo 1028606 6259139 := bstep (se 1 (by rfl) ⟨4694354, by rfl⟩ : syracuseStep 6259139 = 9388709) B9388709
theorem B3474791 : Blo 1028606 3474791 := bstep (se 1 (by rfl) ⟨2606093, by rfl⟩ : syracuseStep 3474791 = 5212187) B5212187
theorem B722405465 : Blo 1028606 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B3476249 : Blo 1028606 3476249 := bstep (se 2 (by rfl) ⟨1303593, by rfl⟩ : syracuseStep 3476249 = 2607187) B2607187
theorem B1543145 : Blo 1028606 1543145 := bstep (se 2 (by rfl) ⟨578679, by rfl⟩ : syracuseStep 1543145 = 1157359) B1157359
theorem B1543151 : Blo 1028606 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B6261887 : Blo 1028606 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B5213321 : Blo 1028606 5213321 := bstep (se 2 (by rfl) ⟨1954995, by rfl⟩ : syracuseStep 5213321 = 3909991) B3909991
theorem B3476627 : Blo 1028606 3476627 := bstep (se 1 (by rfl) ⟨2607470, by rfl⟩ : syracuseStep 3476627 = 5214941) B5214941
theorem B1543847 : Blo 1028606 1543847 := bstep (se 1 (by rfl) ⟨1157885, by rfl⟩ : syracuseStep 1543847 = 2315771) B2315771
theorem B1544027 : Blo 1028606 1544027 := bstep (se 1 (by rfl) ⟨1158020, by rfl⟩ : syracuseStep 1544027 = 2316041) B2316041
theorem B1544795 : Blo 1028606 1544795 := bstep (se 1 (by rfl) ⟨1158596, by rfl⟩ : syracuseStep 1544795 = 2317193) B2317193
theorem B1545023 : Blo 1028606 1545023 := bstep (se 1 (by rfl) ⟨1158767, by rfl⟩ : syracuseStep 1545023 = 2317535) B2317535
theorem B3478409 : Blo 1028606 3478409 := bstep (se 2 (by rfl) ⟨1304403, by rfl⟩ : syracuseStep 3478409 = 2608807) B2608807
theorem B3478463 : Blo 1028606 3478463 := bstep (se 1 (by rfl) ⟨2608847, by rfl⟩ : syracuseStep 3478463 = 5217695) B5217695
theorem B4953275 : Blo 1028606 4953275 := bstep (se 1 (by rfl) ⟨3714956, by rfl⟩ : syracuseStep 4953275 = 7429913) B7429913
theorem B37557593 : Blo 1028606 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B1545887 : Blo 1028606 1545887 := bstep (se 1 (by rfl) ⟨1159415, by rfl⟩ : syracuseStep 1545887 = 2318831) B2318831
theorem B8363191 : Blo 1028606 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B1547675 : Blo 1028606 1547675 := bstep (se 1 (by rfl) ⟨1160756, by rfl⟩ : syracuseStep 1547675 = 2321513) B2321513
theorem B8789417 : Blo 1028606 8789417 := bstep (se 2 (by rfl) ⟨3296031, by rfl⟩ : syracuseStep 8789417 = 6592063) B6592063
theorem B3481001 : Blo 1028606 3481001 := bstep (se 2 (by rfl) ⟨1305375, by rfl⟩ : syracuseStep 3481001 = 2610751) B2610751
theorem B3481055 : Blo 1028606 3481055 := bstep (se 1 (by rfl) ⟨2610791, by rfl⟩ : syracuseStep 3481055 = 5221583) B5221583
theorem B3481271 : Blo 1028606 3481271 := bstep (se 1 (by rfl) ⟨2610953, by rfl⟩ : syracuseStep 3481271 = 5221907) B5221907
theorem B1548395 : Blo 1028606 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B289022255 : Blo 1028606 289022255 := bstep (se 1 (by rfl) ⟨216766691, by rfl⟩ : syracuseStep 289022255 = 433533383) B433533383
theorem B1548647 : Blo 1028606 1548647 := bstep (se 1 (by rfl) ⟨1161485, by rfl⟩ : syracuseStep 1548647 = 2322971) B2322971
theorem B3482027 : Blo 1028606 3482027 := bstep (se 1 (by rfl) ⟨2611520, by rfl⟩ : syracuseStep 3482027 = 5223041) B5223041
theorem B6270061 : Blo 1028606 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B5877791 : Blo 1028606 5877791 := bstep (se 1 (by rfl) ⟨4408343, by rfl⟩ : syracuseStep 5877791 = 8816687) B8816687
theorem B1028655 : Blo 1028606 1028655 := bstep (se 1 (by rfl) ⟨771491, by rfl⟩ : syracuseStep 1028655 = 1542983) B1542983
theorem B38056679 : Blo 1028606 38056679 := bstep (se 1 (by rfl) ⟨28542509, by rfl⟩ : syracuseStep 38056679 = 57085019) B57085019
theorem B9909161 : Blo 1028606 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B1029119 : Blo 1028606 1029119 := bstep (se 1 (by rfl) ⟨771839, by rfl⟩ : syracuseStep 1029119 = 1543679) B1543679
theorem B7812449 : Blo 1028606 7812449 := bstep (se 2 (by rfl) ⟨2929668, by rfl⟩ : syracuseStep 7812449 = 5859337) B5859337
theorem B1029823 : Blo 1028606 1029823 := bstep (se 1 (by rfl) ⟨772367, by rfl⟩ : syracuseStep 1029823 = 1544735) B1544735
theorem B4405063 : Blo 1028606 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B1030055 : Blo 1028606 1030055 := bstep (se 1 (by rfl) ⟨772541, by rfl⟩ : syracuseStep 1030055 = 1545083) B1545083
theorem B1030191 : Blo 1028606 1030191 := bstep (se 1 (by rfl) ⟨772643, by rfl⟩ : syracuseStep 1030191 = 1545287) B1545287
theorem B1030255 : Blo 1028606 1030255 := bstep (se 1 (by rfl) ⟨772691, by rfl⟩ : syracuseStep 1030255 = 1545383) B1545383
theorem B1030303 : Blo 1028606 1030303 := bstep (se 1 (by rfl) ⟨772727, by rfl⟩ : syracuseStep 1030303 = 1545455) B1545455
theorem B11122895 : Blo 1028606 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B3914153 : Blo 1028606 3914153 := bstep (se 2 (by rfl) ⟨1467807, by rfl⟩ : syracuseStep 3914153 = 2935615) B2935615
theorem B1030811 : Blo 1028606 1030811 := bstep (se 1 (by rfl) ⟨773108, by rfl⟩ : syracuseStep 1030811 = 1546217) B1546217
theorem B1030823 : Blo 1028606 1030823 := bstep (se 1 (by rfl) ⟨773117, by rfl⟩ : syracuseStep 1030823 = 1546235) B1546235
theorem B1030907 : Blo 1028606 1030907 := bstep (se 1 (by rfl) ⟨773180, by rfl⟩ : syracuseStep 1030907 = 1546361) B1546361
theorem B1030911 : Blo 1028606 1030911 := bstep (se 1 (by rfl) ⟨773183, by rfl⟩ : syracuseStep 1030911 = 1546367) B1546367
theorem B33995867 : Blo 1028606 33995867 := bstep (se 1 (by rfl) ⟨25496900, by rfl⟩ : syracuseStep 33995867 = 50993801) B50993801
theorem B6274145 : Blo 1028606 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1031707 : Blo 1028606 1031707 := bstep (se 1 (by rfl) ⟨773780, by rfl⟩ : syracuseStep 1031707 = 1547561) B1547561
theorem B12533305 : Blo 1028606 12533305 := bstep (se 2 (by rfl) ⟨4699989, by rfl⟩ : syracuseStep 12533305 = 9399979) B9399979
theorem B1883903 : Blo 1028606 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B1032223 : Blo 1028606 1032223 := bstep (se 1 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 1032223 = 1548335) B1548335
theorem B1032443 : Blo 1028606 1032443 := bstep (se 1 (by rfl) ⟨774332, by rfl⟩ : syracuseStep 1032443 = 1548665) B1548665
theorem B1032475 : Blo 1028606 1032475 := bstep (se 1 (by rfl) ⟨774356, by rfl⟩ : syracuseStep 1032475 = 1548713) B1548713
theorem B26427707 : Blo 1028606 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B23806543 : Blo 1028606 23806543 := bstep (se 1 (by rfl) ⟨17854907, by rfl⟩ : syracuseStep 23806543 = 35709815) B35709815
theorem B1884955 : Blo 1028606 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B3916781 : Blo 1028606 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B25118585 : Blo 1028606 25118585 := bstep (se 2 (by rfl) ⟨9419469, by rfl⟩ : syracuseStep 25118585 = 18838939) B18838939
theorem B1953371 : Blo 1028606 1953371 := bstep (se 1 (by rfl) ⟨1465028, by rfl⟩ : syracuseStep 1953371 = 2930057) B2930057
theorem B11751479 : Blo 1028606 11751479 := bstep (se 1 (by rfl) ⟨8813609, by rfl⟩ : syracuseStep 11751479 = 17627219) B17627219
theorem B3133853 : Blo 1028606 3133853 := bstep (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) B1175195
theorem B2316779 : Blo 1028606 2316779 := bstep (se 1 (by rfl) ⟨1737584, by rfl⟩ : syracuseStep 2316779 = 3475169) B3475169
theorem B26401463 : Blo 1028606 26401463 := bstep (se 1 (by rfl) ⟨19801097, by rfl⟩ : syracuseStep 26401463 = 39602195) B39602195
theorem B50126039 : Blo 1028606 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B2940239 : Blo 1028606 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B2317895 : Blo 1028606 2317895 := bstep (se 1 (by rfl) ⟨1738421, by rfl⟩ : syracuseStep 2317895 = 3476843) B3476843
theorem B13198787 : Blo 1028606 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B50226641 : Blo 1028606 50226641 := bstep (se 2 (by rfl) ⟨18834990, by rfl⟩ : syracuseStep 50226641 = 37669981) B37669981
theorem B1304095 : Blo 1028606 1304095 := bstep (se 1 (by rfl) ⟨978071, by rfl⟩ : syracuseStep 1304095 = 1956143) B1956143
theorem B1304191 : Blo 1028606 1304191 := bstep (se 1 (by rfl) ⟨978143, by rfl⟩ : syracuseStep 1304191 = 1956287) B1956287
theorem B2320199 : Blo 1028606 2320199 := bstep (se 1 (by rfl) ⟨1740149, by rfl⟩ : syracuseStep 2320199 = 3480299) B3480299
theorem B1304687 : Blo 1028606 1304687 := bstep (se 1 (by rfl) ⟨978515, by rfl⟩ : syracuseStep 1304687 = 1957031) B1957031
theorem B1468639 : Blo 1028606 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B2353427 : Blo 1028606 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B2320937 : Blo 1028606 2320937 := bstep (se 2 (by rfl) ⟨870351, by rfl⟩ : syracuseStep 2320937 = 1740703) B1740703
theorem B6450299 : Blo 1028606 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B11464345 : Blo 1028606 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B2322935 : Blo 1028606 2322935 := bstep (se 1 (by rfl) ⟨1742201, by rfl⟩ : syracuseStep 2322935 = 3484403) B3484403
theorem B5862527 : Blo 1028606 5862527 := bstep (se 1 (by rfl) ⟨4396895, by rfl⟩ : syracuseStep 5862527 = 8793791) B8793791
theorem B23754829 : Blo 1028606 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B39680927 : Blo 1028606 39680927 := bstep (se 1 (by rfl) ⟨29760695, by rfl⟩ : syracuseStep 39680927 = 59521391) B59521391
theorem B11731067 : Blo 1028606 11731067 := bstep (se 1 (by rfl) ⟨8798300, by rfl⟩ : syracuseStep 11731067 = 17596601) B17596601
theorem B16745723 : Blo 1028606 16745723 := bstep (se 1 (by rfl) ⟨12559292, by rfl⟩ : syracuseStep 16745723 = 25118585) B25118585
theorem B1738793 : Blo 1028606 1738793 := bstep (se 2 (by rfl) ⟨652047, by rfl⟩ : syracuseStep 1738793 = 1304095) B1304095
theorem B3475547 : Blo 1028606 3475547 := bstep (se 1 (by rfl) ⟨2606660, by rfl⟩ : syracuseStep 3475547 = 5213321) B5213321
theorem B1738921 : Blo 1028606 1738921 := bstep (se 2 (by rfl) ⟨652095, by rfl⟩ : syracuseStep 1738921 = 1304191) B1304191
theorem B7834319 : Blo 1028606 7834319 := bstep (se 1 (by rfl) ⟨5875739, by rfl⟩ : syracuseStep 7834319 = 11751479) B11751479
theorem B25038395 : Blo 1028606 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B8360081 : Blo 1028606 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B1544519 : Blo 1028606 1544519 := bstep (se 1 (by rfl) ⟨1158389, by rfl⟩ : syracuseStep 1544519 = 2316779) B2316779
theorem B17600975 : Blo 1028606 17600975 := bstep (se 1 (by rfl) ⟨13200731, by rfl⟩ : syracuseStep 17600975 = 26401463) B26401463
theorem B1545263 : Blo 1028606 1545263 := bstep (se 1 (by rfl) ⟨1158947, by rfl⟩ : syracuseStep 1545263 = 2317895) B2317895
theorem B192681503 : Blo 1028606 192681503 := bstep (se 1 (by rfl) ⟨144511127, by rfl⟩ : syracuseStep 192681503 = 289022255) B289022255
theorem B3479165 : Blo 1028606 3479165 := bstep (se 3 (by rfl) ⟨652343, by rfl⟩ : syracuseStep 3479165 = 1304687) B1304687
theorem B1546799 : Blo 1028606 1546799 := bstep (se 1 (by rfl) ⟨1160099, by rfl⟩ : syracuseStep 1546799 = 2320199) B2320199
theorem B1547291 : Blo 1028606 1547291 := bstep (se 1 (by rfl) ⟨1160468, by rfl⟩ : syracuseStep 1547291 = 2320937) B2320937
theorem B4300199 : Blo 1028606 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B5873417 : Blo 1028606 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B1548623 : Blo 1028606 1548623 := bstep (se 1 (by rfl) ⟨1161467, by rfl⟩ : syracuseStep 1548623 = 2322935) B2322935
theorem B25371119 : Blo 1028606 25371119 := bstep (se 1 (by rfl) ⟨19028339, by rfl⟩ : syracuseStep 25371119 = 38056679) B38056679
theorem B3908351 : Blo 1028606 3908351 := bstep (se 1 (by rfl) ⟨2931263, by rfl⟩ : syracuseStep 3908351 = 5862527) B5862527
theorem B7840637 : Blo 1028606 7840637 := bstep (se 3 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 7840637 = 2940239) B2940239
theorem B7415263 : Blo 1028606 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B11150921 : Blo 1028606 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B26453951 : Blo 1028606 26453951 := bstep (se 1 (by rfl) ⟨19840463, by rfl⟩ : syracuseStep 26453951 = 39680927) B39680927
theorem B5023741 : Blo 1028606 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B4172759 : Blo 1028606 4172759 := bstep (se 1 (by rfl) ⟨3129569, by rfl⟩ : syracuseStep 4172759 = 6259139) B6259139
theorem B481603643 : Blo 1028606 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B1028763 : Blo 1028606 1028763 := bstep (se 1 (by rfl) ⟨771572, by rfl⟩ : syracuseStep 1028763 = 1543145) B1543145
theorem B1028767 : Blo 1028606 1028767 := bstep (se 1 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 1028767 = 1543151) B1543151
theorem B4174591 : Blo 1028606 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1029231 : Blo 1028606 1029231 := bstep (se 1 (by rfl) ⟨771923, by rfl⟩ : syracuseStep 1029231 = 1543847) B1543847
theorem B1029351 : Blo 1028606 1029351 := bstep (se 1 (by rfl) ⟨772013, by rfl⟩ : syracuseStep 1029351 = 1544027) B1544027
theorem B1029863 : Blo 1028606 1029863 := bstep (se 1 (by rfl) ⟨772397, by rfl⟩ : syracuseStep 1029863 = 1544795) B1544795
theorem B1030015 : Blo 1028606 1030015 := bstep (se 1 (by rfl) ⟨772511, by rfl⟩ : syracuseStep 1030015 = 1545023) B1545023
theorem B1030591 : Blo 1028606 1030591 := bstep (se 1 (by rfl) ⟨772943, by rfl⟩ : syracuseStep 1030591 = 1545887) B1545887
theorem B15285793 : Blo 1028606 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B1031783 : Blo 1028606 1031783 := bstep (se 1 (by rfl) ⟨773837, by rfl⟩ : syracuseStep 1031783 = 1547675) B1547675
theorem B1032263 : Blo 1028606 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B1032431 : Blo 1028606 1032431 := bstep (se 1 (by rfl) ⟨774323, by rfl⟩ : syracuseStep 1032431 = 1548647) B1548647
theorem B8799191 : Blo 1028606 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B3918527 : Blo 1028606 3918527 := bstep (se 1 (by rfl) ⟨2938895, by rfl⟩ : syracuseStep 3918527 = 5877791) B5877791
theorem B31673105 : Blo 1028606 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B90655645 : Blo 1028606 90655645 := bstep (se 3 (by rfl) ⟨16997933, by rfl⟩ : syracuseStep 90655645 = 33995867) B33995867
theorem B6606107 : Blo 1028606 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B2609435 : Blo 1028606 2609435 := bstep (se 1 (by rfl) ⟨1957076, by rfl⟩ : syracuseStep 2609435 = 3914153) B3914153
theorem B4182763 : Blo 1028606 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B17618471 : Blo 1028606 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B2315879 : Blo 1028606 2315879 := bstep (se 1 (by rfl) ⟨1736909, by rfl⟩ : syracuseStep 2315879 = 3473819) B3473819
theorem B2611187 : Blo 1028606 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B31742057 : Blo 1028606 31742057 := bstep (se 2 (by rfl) ⟨11903271, by rfl⟩ : syracuseStep 31742057 = 23806543) B23806543
theorem B2316527 : Blo 1028606 2316527 := bstep (se 1 (by rfl) ⟨1737395, by rfl⟩ : syracuseStep 2316527 = 3474791) B3474791
theorem B2513273 : Blo 1028606 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B2317499 : Blo 1028606 2317499 := bstep (se 1 (by rfl) ⟨1738124, by rfl⟩ : syracuseStep 2317499 = 3476249) B3476249
theorem B2317751 : Blo 1028606 2317751 := bstep (se 1 (by rfl) ⟨1738313, by rfl⟩ : syracuseStep 2317751 = 3476627) B3476627
theorem B1302247 : Blo 1028606 1302247 := bstep (se 1 (by rfl) ⟨976685, by rfl⟩ : syracuseStep 1302247 = 1953371) B1953371
theorem B2089235 : Blo 1028606 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B1958185 : Blo 1028606 1958185 := bstep (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) B1468639
theorem B2318939 : Blo 1028606 2318939 := bstep (se 1 (by rfl) ⟨1739204, by rfl⟩ : syracuseStep 2318939 = 3478409) B3478409
theorem B2318975 : Blo 1028606 2318975 := bstep (se 1 (by rfl) ⟨1739231, by rfl⟩ : syracuseStep 2318975 = 3478463) B3478463
theorem B3302183 : Blo 1028606 3302183 := bstep (se 1 (by rfl) ⟨2476637, by rfl⟩ : syracuseStep 3302183 = 4953275) B4953275
theorem B33417359 : Blo 1028606 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B5859611 : Blo 1028606 5859611 := bstep (se 1 (by rfl) ⟨4394708, by rfl⟩ : syracuseStep 5859611 = 8789417) B8789417
theorem B2320667 : Blo 1028606 2320667 := bstep (se 1 (by rfl) ⟨1740500, by rfl⟩ : syracuseStep 2320667 = 3481001) B3481001
theorem B2320703 : Blo 1028606 2320703 := bstep (se 1 (by rfl) ⟨1740527, by rfl⟩ : syracuseStep 2320703 = 3481055) B3481055
theorem B2320847 : Blo 1028606 2320847 := bstep (se 1 (by rfl) ⟨1740635, by rfl⟩ : syracuseStep 2320847 = 3481271) B3481271
theorem B2321351 : Blo 1028606 2321351 := bstep (se 1 (by rfl) ⟨1741013, by rfl⟩ : syracuseStep 2321351 = 3482027) B3482027
theorem B33484427 : Blo 1028606 33484427 := bstep (se 1 (by rfl) ⟨25113320, by rfl⟩ : syracuseStep 33484427 = 50226641) B50226641
theorem B1568951 : Blo 1028606 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B5208299 : Blo 1028606 5208299 := bstep (se 1 (by rfl) ⟨3906224, by rfl⟩ : syracuseStep 5208299 = 7812449) B7812449
theorem B16711073 : Blo 1028606 16711073 := bstep (se 2 (by rfl) ⟨6266652, by rfl⟩ : syracuseStep 16711073 = 12533305) B12533305
theorem B5866127 : Blo 1028606 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B5573387 : Blo 1028606 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B1739623 : Blo 1028606 1739623 := bstep (se 1 (by rfl) ⟨1304717, by rfl⟩ : syracuseStep 1739623 = 2609435) B2609435
theorem B11733983 : Blo 1028606 11733983 := bstep (se 1 (by rfl) ⟨8800487, by rfl⟩ : syracuseStep 11733983 = 17600975) B17600975
theorem B128454335 : Blo 1028606 128454335 := bstep (se 1 (by rfl) ⟨96340751, by rfl⟩ : syracuseStep 128454335 = 192681503) B192681503
theorem B1543919 : Blo 1028606 1543919 := bstep (se 1 (by rfl) ⟨1157939, by rfl⟩ : syracuseStep 1543919 = 2315879) B2315879
theorem B26808245 : Blo 1028606 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B1740791 : Blo 1028606 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B1544351 : Blo 1028606 1544351 := bstep (se 1 (by rfl) ⟨1158263, by rfl⟩ : syracuseStep 1544351 = 2316527) B2316527
theorem B1544999 : Blo 1028606 1544999 := bstep (se 1 (by rfl) ⟨1158749, by rfl⟩ : syracuseStep 1544999 = 2317499) B2317499
theorem B1545167 : Blo 1028606 1545167 := bstep (se 1 (by rfl) ⟨1158875, by rfl⟩ : syracuseStep 1545167 = 2317751) B2317751
theorem B16914079 : Blo 1028606 16914079 := bstep (se 1 (by rfl) ⟨12685559, by rfl⟩ : syracuseStep 16914079 = 25371119) B25371119
theorem B1545959 : Blo 1028606 1545959 := bstep (se 1 (by rfl) ⟨1159469, by rfl⟩ : syracuseStep 1545959 = 2318939) B2318939
theorem B1545983 : Blo 1028606 1545983 := bstep (se 1 (by rfl) ⟨1159487, by rfl⟩ : syracuseStep 1545983 = 2318975) B2318975
theorem B2201455 : Blo 1028606 2201455 := bstep (se 1 (by rfl) ⟨1651091, by rfl⟩ : syracuseStep 2201455 = 3302183) B3302183
theorem B5577017 : Blo 1028606 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B17635967 : Blo 1028606 17635967 := bstep (se 1 (by rfl) ⟨13226975, by rfl⟩ : syracuseStep 17635967 = 26453951) B26453951
theorem B3906407 : Blo 1028606 3906407 := bstep (se 1 (by rfl) ⟨2929805, by rfl⟩ : syracuseStep 3906407 = 5859611) B5859611
theorem B1547111 : Blo 1028606 1547111 := bstep (se 1 (by rfl) ⟨1160333, by rfl⟩ : syracuseStep 1547111 = 2320667) B2320667
theorem B1547135 : Blo 1028606 1547135 := bstep (se 1 (by rfl) ⟨1160351, by rfl⟩ : syracuseStep 1547135 = 2320703) B2320703
theorem B1547231 : Blo 1028606 1547231 := bstep (se 1 (by rfl) ⟨1160423, by rfl⟩ : syracuseStep 1547231 = 2320847) B2320847
theorem B1547567 : Blo 1028606 1547567 := bstep (se 1 (by rfl) ⟨1160675, by rfl⟩ : syracuseStep 1547567 = 2321351) B2321351
theorem B22322951 : Blo 1028606 22322951 := bstep (se 1 (by rfl) ⟨16742213, by rfl⟩ : syracuseStep 22322951 = 33484427) B33484427
theorem B321069095 : Blo 1028606 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B1159195 : Blo 1028606 1159195 := bstep (se 1 (by rfl) ⟨869396, by rfl⟩ : syracuseStep 1159195 = 1738793) B1738793
theorem B5222879 : Blo 1028606 5222879 := bstep (se 1 (by rfl) ⟨3917159, by rfl⟩ : syracuseStep 5222879 = 7834319) B7834319
theorem B21115403 : Blo 1028606 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B4404071 : Blo 1028606 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B16692263 : Blo 1028606 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B6698321 : Blo 1028606 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B1029679 : Blo 1028606 1029679 := bstep (se 1 (by rfl) ⟨772259, by rfl⟩ : syracuseStep 1029679 = 1544519) B1544519
theorem B1030175 : Blo 1028606 1030175 := bstep (se 1 (by rfl) ⟨772631, by rfl⟩ : syracuseStep 1030175 = 1545263) B1545263
theorem B11745647 : Blo 1028606 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B1031199 : Blo 1028606 1031199 := bstep (se 1 (by rfl) ⟨773399, by rfl⟩ : syracuseStep 1031199 = 1546799) B1546799
theorem B1031527 : Blo 1028606 1031527 := bstep (se 1 (by rfl) ⟨773645, by rfl⟩ : syracuseStep 1031527 = 1547291) B1547291
theorem B2866799 : Blo 1028606 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B3915611 : Blo 1028606 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B1392823 : Blo 1028606 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B1032415 : Blo 1028606 1032415 := bstep (se 1 (by rfl) ⟨774311, by rfl⟩ : syracuseStep 1032415 = 1548623) B1548623
theorem B2605567 : Blo 1028606 2605567 := bstep (se 1 (by rfl) ⟨1954175, by rfl⟩ : syracuseStep 2605567 = 3908351) B3908351
theorem B5227091 : Blo 1028606 5227091 := bstep (se 1 (by rfl) ⟨3920318, by rfl⟩ : syracuseStep 5227091 = 7840637) B7840637
theorem B7820711 : Blo 1028606 7820711 := bstep (se 1 (by rfl) ⟨5865533, by rfl⟩ : syracuseStep 7820711 = 11731067) B11731067
theorem B2610913 : Blo 1028606 2610913 := bstep (se 2 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 2610913 = 1958185) B1958185
theorem B11163815 : Blo 1028606 11163815 := bstep (se 1 (by rfl) ⟨8372861, by rfl⟩ : syracuseStep 11163815 = 16745723) B16745723
theorem B2317031 : Blo 1028606 2317031 := bstep (se 1 (by rfl) ⟨1737773, by rfl⟩ : syracuseStep 2317031 = 3475547) B3475547
theorem B2612351 : Blo 1028606 2612351 := bstep (se 1 (by rfl) ⟨1959263, by rfl⟩ : syracuseStep 2612351 = 3918527) B3918527
theorem B9887017 : Blo 1028606 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B2318561 : Blo 1028606 2318561 := bstep (se 2 (by rfl) ⟨869460, by rfl⟩ : syracuseStep 2318561 = 1738921) B1738921
theorem B2319443 : Blo 1028606 2319443 := bstep (se 1 (by rfl) ⟨1739582, by rfl⟩ : syracuseStep 2319443 = 3479165) B3479165
theorem B120874193 : Blo 1028606 120874193 := bstep (se 2 (by rfl) ⟨45327822, by rfl⟩ : syracuseStep 120874193 = 90655645) B90655645
theorem B21161371 : Blo 1028606 21161371 := bstep (se 1 (by rfl) ⟨15871028, by rfl⟩ : syracuseStep 21161371 = 31742057) B31742057
theorem B5566121 : Blo 1028606 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B7433947 : Blo 1028606 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B22278239 : Blo 1028606 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B2781839 : Blo 1028606 2781839 := bstep (se 1 (by rfl) ⟨2086379, by rfl⟩ : syracuseStep 2781839 = 4172759) B4172759
theorem B1045967 : Blo 1028606 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B3472199 : Blo 1028606 3472199 := bstep (se 1 (by rfl) ⟨2604149, by rfl⟩ : syracuseStep 3472199 = 5208299) B5208299
theorem B20381057 : Blo 1028606 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B11140715 : Blo 1028606 11140715 := bstep (se 1 (by rfl) ⟨8355536, by rfl⟩ : syracuseStep 11140715 = 16711073) B16711073
theorem B1736329 : Blo 1028606 1736329 := bstep (se 2 (by rfl) ⟨651123, by rfl⟩ : syracuseStep 1736329 = 1302247) B1302247
theorem B3474089 : Blo 1028606 3474089 := bstep (se 2 (by rfl) ⟨1302783, by rfl⟩ : syracuseStep 3474089 = 2605567) B2605567
theorem B28215161 : Blo 1028606 28215161 := bstep (se 2 (by rfl) ⟨10580685, by rfl⟩ : syracuseStep 28215161 = 21161371) B21161371
theorem B5213807 : Blo 1028606 5213807 := bstep (se 1 (by rfl) ⟨3910355, by rfl⟩ : syracuseStep 5213807 = 7820711) B7820711
theorem B2789245 : Blo 1028606 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B7442543 : Blo 1028606 7442543 := bstep (se 1 (by rfl) ⟨5581907, by rfl⟩ : syracuseStep 7442543 = 11163815) B11163815
theorem B1544687 : Blo 1028606 1544687 := bstep (se 1 (by rfl) ⟨1158515, by rfl⟩ : syracuseStep 1544687 = 2317031) B2317031
theorem B1741567 : Blo 1028606 1741567 := bstep (se 1 (by rfl) ⟨1306175, by rfl⟩ : syracuseStep 1741567 = 2612351) B2612351
theorem B14881967 : Blo 1028606 14881967 := bstep (se 1 (by rfl) ⟨11161475, by rfl⟩ : syracuseStep 14881967 = 22322951) B22322951
theorem B214046063 : Blo 1028606 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B1545593 : Blo 1028606 1545593 := bstep (se 2 (by rfl) ⟨579597, by rfl⟩ : syracuseStep 1545593 = 1159195) B1159195
theorem B1545707 : Blo 1028606 1545707 := bstep (se 1 (by rfl) ⟨1159280, by rfl⟩ : syracuseStep 1545707 = 2318561) B2318561
theorem B1546295 : Blo 1028606 1546295 := bstep (se 1 (by rfl) ⟨1159721, by rfl⟩ : syracuseStep 1546295 = 2319443) B2319443
theorem B80582795 : Blo 1028606 80582795 := bstep (se 1 (by rfl) ⟨60437096, by rfl⟩ : syracuseStep 80582795 = 120874193) B120874193
theorem B22552105 : Blo 1028606 22552105 := bstep (se 2 (by rfl) ⟨8457039, by rfl⟩ : syracuseStep 22552105 = 16914079) B16914079
theorem B3481217 : Blo 1028606 3481217 := bstep (se 2 (by rfl) ⟨1305456, by rfl⟩ : syracuseStep 3481217 = 2610913) B2610913
theorem B3710747 : Blo 1028606 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B14852159 : Blo 1028606 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B3481919 : Blo 1028606 3481919 := bstep (se 1 (by rfl) ⟨2611439, by rfl⟩ : syracuseStep 3481919 = 5222879) B5222879
theorem B4465547 : Blo 1028606 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B13182689 : Blo 1028606 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B1911199 : Blo 1028606 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B3484727 : Blo 1028606 3484727 := bstep (se 1 (by rfl) ⟨2613545, by rfl⟩ : syracuseStep 3484727 = 5227091) B5227091
theorem B3910751 : Blo 1028606 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B3715591 : Blo 1028606 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B11744189 : Blo 1028606 11744189 := bstep (se 3 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 11744189 = 4404071) B4404071
theorem B85636223 : Blo 1028606 85636223 := bstep (se 1 (by rfl) ⟨64227167, by rfl⟩ : syracuseStep 85636223 = 128454335) B128454335
theorem B1029279 : Blo 1028606 1029279 := bstep (se 1 (by rfl) ⟨771959, by rfl⟩ : syracuseStep 1029279 = 1543919) B1543919
theorem B17872163 : Blo 1028606 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B1160527 : Blo 1028606 1160527 := bstep (se 1 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 1160527 = 1740791) B1740791
theorem B1029567 : Blo 1028606 1029567 := bstep (se 1 (by rfl) ⟨772175, by rfl⟩ : syracuseStep 1029567 = 1544351) B1544351
theorem B1029999 : Blo 1028606 1029999 := bstep (se 1 (by rfl) ⟨772499, by rfl⟩ : syracuseStep 1029999 = 1544999) B1544999
theorem B1030111 : Blo 1028606 1030111 := bstep (se 1 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 1030111 = 1545167) B1545167
theorem B1030639 : Blo 1028606 1030639 := bstep (se 1 (by rfl) ⟨772979, by rfl⟩ : syracuseStep 1030639 = 1545959) B1545959
theorem B1030655 : Blo 1028606 1030655 := bstep (se 1 (by rfl) ⟨772991, by rfl⟩ : syracuseStep 1030655 = 1545983) B1545983
theorem B2604271 : Blo 1028606 2604271 := bstep (se 1 (by rfl) ⟨1953203, by rfl⟩ : syracuseStep 2604271 = 3906407) B3906407
theorem B1031407 : Blo 1028606 1031407 := bstep (se 1 (by rfl) ⟨773555, by rfl⟩ : syracuseStep 1031407 = 1547111) B1547111
theorem B1031423 : Blo 1028606 1031423 := bstep (se 1 (by rfl) ⟨773567, by rfl⟩ : syracuseStep 1031423 = 1547135) B1547135
theorem B1031487 : Blo 1028606 1031487 := bstep (se 1 (by rfl) ⟨773615, by rfl⟩ : syracuseStep 1031487 = 1547231) B1547231
theorem B1031711 : Blo 1028606 1031711 := bstep (se 1 (by rfl) ⟨773783, by rfl⟩ : syracuseStep 1031711 = 1547567) B1547567
theorem B9911929 : Blo 1028606 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B2935273 : Blo 1028606 2935273 := bstep (se 2 (by rfl) ⟨1100727, by rfl⟩ : syracuseStep 2935273 = 2201455) B2201455
theorem B14076935 : Blo 1028606 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B1854559 : Blo 1028606 1854559 := bstep (se 1 (by rfl) ⟨1390919, by rfl⟩ : syracuseStep 1854559 = 2781839) B2781839
theorem B11128175 : Blo 1028606 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B2314799 : Blo 1028606 2314799 := bstep (se 1 (by rfl) ⟨1736099, by rfl⟩ : syracuseStep 2314799 = 3472199) B3472199
theorem B2315105 : Blo 1028606 2315105 := bstep (se 2 (by rfl) ⟨868164, by rfl⟩ : syracuseStep 2315105 = 1736329) B1736329
theorem B13587371 : Blo 1028606 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B7427143 : Blo 1028606 7427143 := bstep (se 1 (by rfl) ⟨5570357, by rfl⟩ : syracuseStep 7427143 = 11140715) B11140715
theorem B2610407 : Blo 1028606 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B1857097 : Blo 1028606 1857097 := bstep (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) B1392823
theorem B7822655 : Blo 1028606 7822655 := bstep (se 1 (by rfl) ⟨5866991, by rfl⟩ : syracuseStep 7822655 = 11733983) B11733983
theorem B2319497 : Blo 1028606 2319497 := bstep (se 2 (by rfl) ⟨869811, by rfl⟩ : syracuseStep 2319497 = 1739623) B1739623
theorem B11757311 : Blo 1028606 11757311 := bstep (se 1 (by rfl) ⟨8817983, by rfl⟩ : syracuseStep 11757311 = 17635967) B17635967
theorem B14872045 : Blo 1028606 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B7830431 : Blo 1028606 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B18810107 : Blo 1028606 18810107 := bstep (se 1 (by rfl) ⟨14107580, by rfl⟩ : syracuseStep 18810107 = 28215161) B28215161
theorem B3475871 : Blo 1028606 3475871 := bstep (se 1 (by rfl) ⟨2606903, by rfl⟩ : syracuseStep 3475871 = 5213807) B5213807
theorem B1543199 : Blo 1028606 1543199 := bstep (se 1 (by rfl) ⟨1157399, by rfl⟩ : syracuseStep 1543199 = 2314799) B2314799
theorem B1543403 : Blo 1028606 1543403 := bstep (se 1 (by rfl) ⟨1157552, by rfl⟩ : syracuseStep 1543403 = 2315105) B2315105
theorem B1740271 : Blo 1028606 1740271 := bstep (se 1 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 1740271 = 2610407) B2610407
theorem B19829393 : Blo 1028606 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B5215103 : Blo 1028606 5215103 := bstep (se 1 (by rfl) ⟨3911327, by rfl⟩ : syracuseStep 5215103 = 7822655) B7822655
theorem B9901439 : Blo 1028606 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B4954121 : Blo 1028606 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B1546331 : Blo 1028606 1546331 := bstep (se 1 (by rfl) ⟨1159748, by rfl⟩ : syracuseStep 1546331 = 2319497) B2319497
theorem B8788459 : Blo 1028606 8788459 := bstep (se 1 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 8788459 = 13182689) B13182689
theorem B7838207 : Blo 1028606 7838207 := bstep (se 1 (by rfl) ⟨5878655, by rfl⟩ : syracuseStep 7838207 = 11757311) B11757311
theorem B9902857 : Blo 1028606 9902857 := bstep (se 2 (by rfl) ⟨3713571, by rfl⟩ : syracuseStep 9902857 = 7427143) B7427143
theorem B1547369 : Blo 1028606 1547369 := bstep (se 2 (by rfl) ⟨580263, by rfl⟩ : syracuseStep 1547369 = 1160527) B1160527
theorem B57090815 : Blo 1028606 57090815 := bstep (se 1 (by rfl) ⟨42818111, by rfl⟩ : syracuseStep 57090815 = 85636223) B85636223
theorem B5220287 : Blo 1028606 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B13215905 : Blo 1028606 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B9384623 : Blo 1028606 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B7418783 : Blo 1028606 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B4961695 : Blo 1028606 4961695 := bstep (se 1 (by rfl) ⟨3721271, by rfl⟩ : syracuseStep 4961695 = 7442543) B7442543
theorem B1029791 : Blo 1028606 1029791 := bstep (se 1 (by rfl) ⟨772343, by rfl⟩ : syracuseStep 1029791 = 1544687) B1544687
theorem B9058247 : Blo 1028606 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B3913697 : Blo 1028606 3913697 := bstep (se 2 (by rfl) ⟨1467636, by rfl⟩ : syracuseStep 3913697 = 2935273) B2935273
theorem B1030395 : Blo 1028606 1030395 := bstep (se 1 (by rfl) ⟨772796, by rfl⟩ : syracuseStep 1030395 = 1545593) B1545593
theorem B1030471 : Blo 1028606 1030471 := bstep (se 1 (by rfl) ⟨772853, by rfl⟩ : syracuseStep 1030471 = 1545707) B1545707
theorem B1030863 : Blo 1028606 1030863 := bstep (se 1 (by rfl) ⟨773147, by rfl⟩ : syracuseStep 1030863 = 1546295) B1546295
theorem B53721863 : Blo 1028606 53721863 := bstep (se 1 (by rfl) ⟨40291397, by rfl⟩ : syracuseStep 53721863 = 80582795) B80582795
theorem B2473831 : Blo 1028606 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B2607167 : Blo 1028606 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B2476129 : Blo 1028606 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B11914775 : Blo 1028606 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B30069473 : Blo 1028606 30069473 := bstep (se 2 (by rfl) ⟨11276052, by rfl⟩ : syracuseStep 30069473 = 22552105) B22552105
theorem B2316059 : Blo 1028606 2316059 := bstep (se 1 (by rfl) ⟨1737044, by rfl⟩ : syracuseStep 2316059 = 3474089) B3474089
theorem B2548265 : Blo 1028606 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B9921311 : Blo 1028606 9921311 := bstep (se 1 (by rfl) ⟨7440983, by rfl⟩ : syracuseStep 9921311 = 14881967) B14881967
theorem B142697375 : Blo 1028606 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B2320811 : Blo 1028606 2320811 := bstep (se 1 (by rfl) ⟨1740608, by rfl⟩ : syracuseStep 2320811 = 3481217) B3481217
theorem B2321279 : Blo 1028606 2321279 := bstep (se 1 (by rfl) ⟨1740959, by rfl⟩ : syracuseStep 2321279 = 3481919) B3481919
theorem B9890981 : Blo 1028606 9890981 := bstep (se 4 (by rfl) ⟨927279, by rfl⟩ : syracuseStep 9890981 = 1854559) B1854559
theorem B2977031 : Blo 1028606 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B2322089 : Blo 1028606 2322089 := bstep (se 2 (by rfl) ⟨870783, by rfl⟩ : syracuseStep 2322089 = 1741567) B1741567
theorem B2323151 : Blo 1028606 2323151 := bstep (se 1 (by rfl) ⟨1742363, by rfl⟩ : syracuseStep 2323151 = 3484727) B3484727
theorem B7829459 : Blo 1028606 7829459 := bstep (se 1 (by rfl) ⟨5872094, by rfl⟩ : syracuseStep 7829459 = 11744189) B11744189
theorem B3472361 : Blo 1028606 3472361 := bstep (se 2 (by rfl) ⟨1302135, by rfl⟩ : syracuseStep 3472361 = 2604271) B2604271
theorem B14875973 : Blo 1028606 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B1738111 : Blo 1028606 1738111 := bstep (se 1 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 1738111 = 2607167) B2607167
theorem B80185261 : Blo 1028606 80185261 := bstep (se 3 (by rfl) ⟨15034736, by rfl⟩ : syracuseStep 80185261 = 30069473) B30069473
theorem B3476735 : Blo 1028606 3476735 := bstep (se 1 (by rfl) ⟨2607551, by rfl⟩ : syracuseStep 3476735 = 5215103) B5215103
theorem B1544039 : Blo 1028606 1544039 := bstep (se 1 (by rfl) ⟨1158029, by rfl⟩ : syracuseStep 1544039 = 2316059) B2316059
theorem B95131583 : Blo 1028606 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B3480191 : Blo 1028606 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B1547207 : Blo 1028606 1547207 := bstep (se 1 (by rfl) ⟨1160405, by rfl⟩ : syracuseStep 1547207 = 2320811) B2320811
theorem B1547519 : Blo 1028606 1547519 := bstep (se 1 (by rfl) ⟨1160639, by rfl⟩ : syracuseStep 1547519 = 2321279) B2321279
theorem B6593987 : Blo 1028606 6593987 := bstep (se 1 (by rfl) ⟨4945490, by rfl⟩ : syracuseStep 6593987 = 9890981) B9890981
theorem B1548059 : Blo 1028606 1548059 := bstep (se 1 (by rfl) ⟨1161044, by rfl⟩ : syracuseStep 1548059 = 2322089) B2322089
theorem B1548767 : Blo 1028606 1548767 := bstep (se 1 (by rfl) ⟨1161575, by rfl⟩ : syracuseStep 1548767 = 2323151) B2323151
theorem B7938749 : Blo 1028606 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B6038831 : Blo 1028606 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B5219639 : Blo 1028606 5219639 := bstep (se 1 (by rfl) ⟨3914729, by rfl⟩ : syracuseStep 5219639 = 7829459) B7829459
theorem B1028799 : Blo 1028606 1028799 := bstep (se 1 (by rfl) ⟨771599, by rfl⟩ : syracuseStep 1028799 = 1543199) B1543199
theorem B1028935 : Blo 1028606 1028935 := bstep (se 1 (by rfl) ⟨771701, by rfl⟩ : syracuseStep 1028935 = 1543403) B1543403
theorem B7943183 : Blo 1028606 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B13219595 : Blo 1028606 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B6600959 : Blo 1028606 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B1030887 : Blo 1028606 1030887 := bstep (se 1 (by rfl) ⟨773165, by rfl⟩ : syracuseStep 1030887 = 1546331) B1546331
theorem B5225471 : Blo 1028606 5225471 := bstep (se 1 (by rfl) ⟨3919103, by rfl⟩ : syracuseStep 5225471 = 7838207) B7838207
theorem B1031579 : Blo 1028606 1031579 := bstep (se 1 (by rfl) ⟨773684, by rfl⟩ : syracuseStep 1031579 = 1547369) B1547369
theorem B27181493 : Blo 1028606 27181493 := bstep (se 5 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 27181493 = 2548265) B2548265
theorem B38060543 : Blo 1028606 38060543 := bstep (se 1 (by rfl) ⟨28545407, by rfl⟩ : syracuseStep 38060543 = 57090815) B57090815
theorem B11717945 : Blo 1028606 11717945 := bstep (se 2 (by rfl) ⟨4394229, by rfl⟩ : syracuseStep 11717945 = 8788459) B8788459
theorem B2609131 : Blo 1028606 2609131 := bstep (se 1 (by rfl) ⟨1956848, by rfl⟩ : syracuseStep 2609131 = 3913697) B3913697
theorem B2314907 : Blo 1028606 2314907 := bstep (se 1 (by rfl) ⟨1736180, by rfl⟩ : syracuseStep 2314907 = 3472361) B3472361
theorem B9917315 : Blo 1028606 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B3298441 : Blo 1028606 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B12540071 : Blo 1028606 12540071 := bstep (se 1 (by rfl) ⟨9405053, by rfl⟩ : syracuseStep 12540071 = 18810107) B18810107
theorem B2317247 : Blo 1028606 2317247 := bstep (se 1 (by rfl) ⟨1737935, by rfl⟩ : syracuseStep 2317247 = 3475871) B3475871
theorem B3301505 : Blo 1028606 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B3302747 : Blo 1028606 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B2320361 : Blo 1028606 2320361 := bstep (se 2 (by rfl) ⟨870135, by rfl⟩ : syracuseStep 2320361 = 1740271) B1740271
theorem B6614207 : Blo 1028606 6614207 := bstep (se 1 (by rfl) ⟨4960655, by rfl⟩ : syracuseStep 6614207 = 9921311) B9921311
theorem B8810603 : Blo 1028606 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B6615593 : Blo 1028606 6615593 := bstep (se 2 (by rfl) ⟨2480847, by rfl⟩ : syracuseStep 6615593 = 4961695) B4961695
theorem B6256415 : Blo 1028606 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B4945855 : Blo 1028606 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B13203809 : Blo 1028606 13203809 := bstep (se 2 (by rfl) ⟨4951428, by rfl⟩ : syracuseStep 13203809 = 9902857) B9902857
theorem B35814575 : Blo 1028606 35814575 := bstep (se 1 (by rfl) ⟨26860931, by rfl⟩ : syracuseStep 35814575 = 53721863) B53721863
theorem B18120995 : Blo 1028606 18120995 := bstep (se 1 (by rfl) ⟨13590746, by rfl⟩ : syracuseStep 18120995 = 27181493) B27181493
theorem B1543271 : Blo 1028606 1543271 := bstep (se 1 (by rfl) ⟨1157453, by rfl⟩ : syracuseStep 1543271 = 2314907) B2314907
theorem B8360047 : Blo 1028606 8360047 := bstep (se 1 (by rfl) ⟨6270035, by rfl⟩ : syracuseStep 8360047 = 12540071) B12540071
theorem B1544831 : Blo 1028606 1544831 := bstep (se 1 (by rfl) ⟨1158623, by rfl⟩ : syracuseStep 1544831 = 2317247) B2317247
theorem B4395991 : Blo 1028606 4395991 := bstep (se 1 (by rfl) ⟨3296993, by rfl⟩ : syracuseStep 4395991 = 6593987) B6593987
theorem B3478841 : Blo 1028606 3478841 := bstep (se 2 (by rfl) ⟨1304565, by rfl⟩ : syracuseStep 3478841 = 2609131) B2609131
theorem B2201003 : Blo 1028606 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B3479759 : Blo 1028606 3479759 := bstep (se 1 (by rfl) ⟨2609819, by rfl⟩ : syracuseStep 3479759 = 5219639) B5219639
theorem B2201831 : Blo 1028606 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B1546907 : Blo 1028606 1546907 := bstep (se 1 (by rfl) ⟨1160180, by rfl⟩ : syracuseStep 1546907 = 2320361) B2320361
theorem B4397921 : Blo 1028606 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B6594473 : Blo 1028606 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B5873735 : Blo 1028606 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B4170943 : Blo 1028606 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B4400639 : Blo 1028606 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B3483647 : Blo 1028606 3483647 := bstep (se 1 (by rfl) ⟨2612735, by rfl⟩ : syracuseStep 3483647 = 5225471) B5225471
theorem B25373695 : Blo 1028606 25373695 := bstep (se 1 (by rfl) ⟨19030271, by rfl⟩ : syracuseStep 25373695 = 38060543) B38060543
theorem B7811963 : Blo 1028606 7811963 := bstep (se 1 (by rfl) ⟨5858972, by rfl⟩ : syracuseStep 7811963 = 11717945) B11717945
theorem B1029359 : Blo 1028606 1029359 := bstep (se 1 (by rfl) ⟨772019, by rfl⟩ : syracuseStep 1029359 = 1544039) B1544039
theorem B16103549 : Blo 1028606 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B63421055 : Blo 1028606 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B1031471 : Blo 1028606 1031471 := bstep (se 1 (by rfl) ⟨773603, by rfl⟩ : syracuseStep 1031471 = 1547207) B1547207
theorem B1031679 : Blo 1028606 1031679 := bstep (se 1 (by rfl) ⟨773759, by rfl⟩ : syracuseStep 1031679 = 1547519) B1547519
theorem B1032039 : Blo 1028606 1032039 := bstep (se 1 (by rfl) ⟨774029, by rfl⟩ : syracuseStep 1032039 = 1548059) B1548059
theorem B1032511 : Blo 1028606 1032511 := bstep (se 1 (by rfl) ⟨774383, by rfl⟩ : syracuseStep 1032511 = 1548767) B1548767
theorem B5292499 : Blo 1028606 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B4409471 : Blo 1028606 4409471 := bstep (se 1 (by rfl) ⟨3307103, by rfl⟩ : syracuseStep 4409471 = 6614207) B6614207
theorem B4410395 : Blo 1028606 4410395 := bstep (se 1 (by rfl) ⟨3307796, by rfl⟩ : syracuseStep 4410395 = 6615593) B6615593
theorem B5295455 : Blo 1028606 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B8802539 : Blo 1028606 8802539 := bstep (se 1 (by rfl) ⟨6601904, by rfl⟩ : syracuseStep 8802539 = 13203809) B13203809
theorem B23876383 : Blo 1028606 23876383 := bstep (se 1 (by rfl) ⟨17907287, by rfl⟩ : syracuseStep 23876383 = 35814575) B35814575
theorem B2317481 : Blo 1028606 2317481 := bstep (se 2 (by rfl) ⟨869055, by rfl⟩ : syracuseStep 2317481 = 1738111) B1738111
theorem B2317823 : Blo 1028606 2317823 := bstep (se 1 (by rfl) ⟨1738367, by rfl⟩ : syracuseStep 2317823 = 3476735) B3476735
theorem B106913681 : Blo 1028606 106913681 := bstep (se 2 (by rfl) ⟨40092630, by rfl⟩ : syracuseStep 106913681 = 80185261) B80185261
theorem B6611543 : Blo 1028606 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B2320127 : Blo 1028606 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B8813063 : Blo 1028606 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B5868359 : Blo 1028606 5868359 := bstep (se 1 (by rfl) ⟨4401269, by rfl⟩ : syracuseStep 5868359 = 8802539) B8802539
theorem B1544987 : Blo 1028606 1544987 := bstep (se 1 (by rfl) ⟨1158740, by rfl⟩ : syracuseStep 1544987 = 2317481) B2317481
theorem B1545215 : Blo 1028606 1545215 := bstep (se 1 (by rfl) ⟨1158911, by rfl⟩ : syracuseStep 1545215 = 2317823) B2317823
theorem B71275787 : Blo 1028606 71275787 := bstep (se 1 (by rfl) ⟨53456840, by rfl⟩ : syracuseStep 71275787 = 106913681) B106913681
theorem B4396315 : Blo 1028606 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B11146729 : Blo 1028606 11146729 := bstep (se 2 (by rfl) ⟨4180023, by rfl⟩ : syracuseStep 11146729 = 8360047) B8360047
theorem B1546751 : Blo 1028606 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B5875375 : Blo 1028606 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B42280703 : Blo 1028606 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B7056665 : Blo 1028606 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B1028847 : Blo 1028606 1028847 := bstep (se 1 (by rfl) ⟨771635, by rfl⟩ : syracuseStep 1028847 = 1543271) B1543271
theorem B1029887 : Blo 1028606 1029887 := bstep (se 1 (by rfl) ⟨772415, by rfl⟩ : syracuseStep 1029887 = 1544831) B1544831
theorem B33831593 : Blo 1028606 33831593 := bstep (se 2 (by rfl) ⟨12686847, by rfl⟩ : syracuseStep 33831593 = 25373695) B25373695
theorem B1031271 : Blo 1028606 1031271 := bstep (se 1 (by rfl) ⟨773453, by rfl⟩ : syracuseStep 1031271 = 1546907) B1546907
theorem B2931947 : Blo 1028606 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B3915823 : Blo 1028606 3915823 := bstep (se 1 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 3915823 = 5873735) B5873735
theorem B4407695 : Blo 1028606 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B2933759 : Blo 1028606 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B31835177 : Blo 1028606 31835177 := bstep (se 2 (by rfl) ⟨11938191, by rfl⟩ : syracuseStep 31835177 = 23876383) B23876383
theorem B10735699 : Blo 1028606 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B12080663 : Blo 1028606 12080663 := bstep (se 1 (by rfl) ⟨9060497, by rfl⟩ : syracuseStep 12080663 = 18120995) B18120995
theorem B2939647 : Blo 1028606 2939647 := bstep (se 1 (by rfl) ⟨2204735, by rfl⟩ : syracuseStep 2939647 = 4409471) B4409471
theorem B5561257 : Blo 1028606 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B2940263 : Blo 1028606 2940263 := bstep (se 1 (by rfl) ⟨2205197, by rfl⟩ : syracuseStep 2940263 = 4410395) B4410395
theorem B3530303 : Blo 1028606 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B2319227 : Blo 1028606 2319227 := bstep (se 1 (by rfl) ⟨1739420, by rfl⟩ : syracuseStep 2319227 = 3478841) B3478841
theorem B1467335 : Blo 1028606 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B2319839 : Blo 1028606 2319839 := bstep (se 1 (by rfl) ⟨1739879, by rfl⟩ : syracuseStep 2319839 = 3479759) B3479759
theorem B1467887 : Blo 1028606 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B5861321 : Blo 1028606 5861321 := bstep (se 2 (by rfl) ⟨2197995, by rfl⟩ : syracuseStep 5861321 = 4395991) B4395991
theorem B2322431 : Blo 1028606 2322431 := bstep (se 1 (by rfl) ⟨1741823, by rfl⟩ : syracuseStep 2322431 = 3483647) B3483647
theorem B5207975 : Blo 1028606 5207975 := bstep (se 1 (by rfl) ⟨3905981, by rfl⟩ : syracuseStep 5207975 = 7811963) B7811963
theorem B7833833 : Blo 1028606 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B47517191 : Blo 1028606 47517191 := bstep (se 1 (by rfl) ⟨35637893, by rfl⟩ : syracuseStep 47517191 = 71275787) B71275787
theorem B1546151 : Blo 1028606 1546151 := bstep (se 1 (by rfl) ⟨1159613, by rfl⟩ : syracuseStep 1546151 = 2319227) B2319227
theorem B1546559 : Blo 1028606 1546559 := bstep (se 1 (by rfl) ⟨1159919, by rfl⟩ : syracuseStep 1546559 = 2319839) B2319839
theorem B28187135 : Blo 1028606 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B3907547 : Blo 1028606 3907547 := bstep (se 1 (by rfl) ⟨2930660, by rfl⟩ : syracuseStep 3907547 = 5861321) B5861321
theorem B1548287 : Blo 1028606 1548287 := bstep (se 1 (by rfl) ⟨1161215, by rfl⟩ : syracuseStep 1548287 = 2322431) B2322431
theorem B7415009 : Blo 1028606 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B22554395 : Blo 1028606 22554395 := bstep (se 1 (by rfl) ⟨16915796, by rfl⟩ : syracuseStep 22554395 = 33831593) B33831593
theorem B5221097 : Blo 1028606 5221097 := bstep (se 2 (by rfl) ⟨1957911, by rfl⟩ : syracuseStep 5221097 = 3915823) B3915823
theorem B3912239 : Blo 1028606 3912239 := bstep (se 1 (by rfl) ⟨2934179, by rfl⟩ : syracuseStep 3912239 = 5868359) B5868359
theorem B3912893 : Blo 1028606 3912893 := bstep (se 3 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 3912893 = 1467335) B1467335
theorem B1029991 : Blo 1028606 1029991 := bstep (se 1 (by rfl) ⟨772493, by rfl⟩ : syracuseStep 1029991 = 1544987) B1544987
theorem B1030143 : Blo 1028606 1030143 := bstep (se 1 (by rfl) ⟨772607, by rfl⟩ : syracuseStep 1030143 = 1545215) B1545215
theorem B3914365 : Blo 1028606 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B1031167 : Blo 1028606 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B14862305 : Blo 1028606 14862305 := bstep (se 2 (by rfl) ⟨5573364, by rfl⟩ : syracuseStep 14862305 = 11146729) B11146729
theorem B4704443 : Blo 1028606 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B3919529 : Blo 1028606 3919529 := bstep (se 2 (by rfl) ⟨1469823, by rfl⟩ : syracuseStep 3919529 = 2939647) B2939647
theorem B1954631 : Blo 1028606 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B2938463 : Blo 1028606 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B1955839 : Blo 1028606 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B21223451 : Blo 1028606 21223451 := bstep (se 1 (by rfl) ⟨15917588, by rfl⟩ : syracuseStep 21223451 = 31835177) B31835177
theorem B8053775 : Blo 1028606 8053775 := bstep (se 1 (by rfl) ⟨6040331, by rfl⟩ : syracuseStep 8053775 = 12080663) B12080663
theorem B1960175 : Blo 1028606 1960175 := bstep (se 1 (by rfl) ⟨1470131, by rfl⟩ : syracuseStep 1960175 = 2940263) B2940263
theorem B2353535 : Blo 1028606 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B14314265 : Blo 1028606 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B5861753 : Blo 1028606 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B3471983 : Blo 1028606 3471983 := bstep (se 1 (by rfl) ⟨2603987, by rfl⟩ : syracuseStep 3471983 = 5207975) B5207975
theorem B5212349 : Blo 1028606 5212349 := bstep (se 3 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 5212349 = 1954631) B1954631
theorem B3480731 : Blo 1028606 3480731 := bstep (se 1 (by rfl) ⟨2610548, by rfl⟩ : syracuseStep 3480731 = 5221097) B5221097
theorem B9542843 : Blo 1028606 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B3907835 : Blo 1028606 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B5219153 : Blo 1028606 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B9908203 : Blo 1028606 9908203 := bstep (se 1 (by rfl) ⟨7431152, by rfl⟩ : syracuseStep 9908203 = 14862305) B14862305
theorem B5222555 : Blo 1028606 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B1030767 : Blo 1028606 1030767 := bstep (se 1 (by rfl) ⟨773075, by rfl⟩ : syracuseStep 1030767 = 1546151) B1546151
theorem B1031039 : Blo 1028606 1031039 := bstep (se 1 (by rfl) ⟨773279, by rfl⟩ : syracuseStep 1031039 = 1546559) B1546559
theorem B18791423 : Blo 1028606 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B2605031 : Blo 1028606 2605031 := bstep (se 1 (by rfl) ⟨1953773, by rfl⟩ : syracuseStep 2605031 = 3907547) B3907547
theorem B1032191 : Blo 1028606 1032191 := bstep (se 1 (by rfl) ⟨774143, by rfl⟩ : syracuseStep 1032191 = 1548287) B1548287
theorem B2607785 : Blo 1028606 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B2608159 : Blo 1028606 2608159 := bstep (se 1 (by rfl) ⟨1956119, by rfl⟩ : syracuseStep 2608159 = 3912239) B3912239
theorem B2608595 : Blo 1028606 2608595 := bstep (se 1 (by rfl) ⟨1956446, by rfl⟩ : syracuseStep 2608595 = 3912893) B3912893
theorem B2314655 : Blo 1028606 2314655 := bstep (se 1 (by rfl) ⟨1735991, by rfl⟩ : syracuseStep 2314655 = 3471983) B3471983
theorem B3136295 : Blo 1028606 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B31678127 : Blo 1028606 31678127 := bstep (se 1 (by rfl) ⟨23758595, by rfl⟩ : syracuseStep 31678127 = 47517191) B47517191
theorem B2613019 : Blo 1028606 2613019 := bstep (se 1 (by rfl) ⟨1959764, by rfl⟩ : syracuseStep 2613019 = 3919529) B3919529
theorem B1958975 : Blo 1028606 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B14148967 : Blo 1028606 14148967 := bstep (se 1 (by rfl) ⟨10611725, by rfl⟩ : syracuseStep 14148967 = 21223451) B21223451
theorem B5369183 : Blo 1028606 5369183 := bstep (se 1 (by rfl) ⟨4026887, by rfl⟩ : syracuseStep 5369183 = 8053775) B8053775
theorem B4943339 : Blo 1028606 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B15036263 : Blo 1028606 15036263 := bstep (se 1 (by rfl) ⟨11277197, by rfl⟩ : syracuseStep 15036263 = 22554395) B22554395
theorem B1306783 : Blo 1028606 1306783 := bstep (se 1 (by rfl) ⟨980087, by rfl⟩ : syracuseStep 1306783 = 1960175) B1960175
theorem B1569023 : Blo 1028606 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B3474899 : Blo 1028606 3474899 := bstep (se 1 (by rfl) ⟨2606174, by rfl⟩ : syracuseStep 3474899 = 5212349) B5212349
theorem B1738523 : Blo 1028606 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B1739063 : Blo 1028606 1739063 := bstep (se 1 (by rfl) ⟨1304297, by rfl⟩ : syracuseStep 1739063 = 2608595) B2608595
theorem B1543103 : Blo 1028606 1543103 := bstep (se 1 (by rfl) ⟨1157327, by rfl⟩ : syracuseStep 1543103 = 2314655) B2314655
theorem B3477545 : Blo 1028606 3477545 := bstep (se 2 (by rfl) ⟨1304079, by rfl⟩ : syracuseStep 3477545 = 2608159) B2608159
theorem B6361895 : Blo 1028606 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B13210937 : Blo 1028606 13210937 := bstep (se 2 (by rfl) ⟨4954101, by rfl⟩ : syracuseStep 13210937 = 9908203) B9908203
theorem B1742377 : Blo 1028606 1742377 := bstep (se 2 (by rfl) ⟨653391, by rfl⟩ : syracuseStep 1742377 = 1306783) B1306783
theorem B3479435 : Blo 1028606 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B3579455 : Blo 1028606 3579455 := bstep (se 1 (by rfl) ⟨2684591, by rfl⟩ : syracuseStep 3579455 = 5369183) B5369183
theorem B3481703 : Blo 1028606 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B12527615 : Blo 1028606 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B3484025 : Blo 1028606 3484025 := bstep (se 2 (by rfl) ⟨1306509, by rfl⟩ : syracuseStep 3484025 = 2613019) B2613019
theorem B21118751 : Blo 1028606 21118751 := bstep (se 1 (by rfl) ⟨15839063, by rfl⟩ : syracuseStep 21118751 = 31678127) B31678127
theorem B2605223 : Blo 1028606 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B3295559 : Blo 1028606 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B18865289 : Blo 1028606 18865289 := bstep (se 2 (by rfl) ⟨7074483, by rfl⟩ : syracuseStep 18865289 = 14148967) B14148967
theorem B2090863 : Blo 1028606 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B2320487 : Blo 1028606 2320487 := bstep (se 1 (by rfl) ⟨1740365, by rfl⟩ : syracuseStep 2320487 = 3480731) B3480731
theorem B1305983 : Blo 1028606 1305983 := bstep (se 1 (by rfl) ⟨979487, by rfl⟩ : syracuseStep 1305983 = 1958975) B1958975
theorem B10024175 : Blo 1028606 10024175 := bstep (se 1 (by rfl) ⟨7518131, by rfl⟩ : syracuseStep 10024175 = 15036263) B15036263
theorem B1046015 : Blo 1028606 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B1736687 : Blo 1028606 1736687 := bstep (se 1 (by rfl) ⟨1302515, by rfl⟩ : syracuseStep 1736687 = 2605031) B2605031
theorem B1736815 : Blo 1028606 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B2197039 : Blo 1028606 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B1546991 : Blo 1028606 1546991 := bstep (se 1 (by rfl) ⟨1160243, by rfl⟩ : syracuseStep 1546991 = 2320487) B2320487
theorem B50307437 : Blo 1028606 50307437 := bstep (se 3 (by rfl) ⟨9432644, by rfl⟩ : syracuseStep 50307437 = 18865289) B18865289
theorem B3482621 : Blo 1028606 3482621 := bstep (se 3 (by rfl) ⟨652991, by rfl⟩ : syracuseStep 3482621 = 1305983) B1305983
theorem B11151269 : Blo 1028606 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1157791 : Blo 1028606 1157791 := bstep (se 1 (by rfl) ⟨868343, by rfl⟩ : syracuseStep 1157791 = 1736687) B1736687
theorem B1159015 : Blo 1028606 1159015 := bstep (se 1 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 1159015 = 1738523) B1738523
theorem B1159375 : Blo 1028606 1159375 := bstep (se 1 (by rfl) ⟨869531, by rfl⟩ : syracuseStep 1159375 = 1739063) B1739063
theorem B1028735 : Blo 1028606 1028735 := bstep (se 1 (by rfl) ⟨771551, by rfl⟩ : syracuseStep 1028735 = 1543103) B1543103
theorem B4241263 : Blo 1028606 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B14079167 : Blo 1028606 14079167 := bstep (se 1 (by rfl) ⟨10559375, by rfl⟩ : syracuseStep 14079167 = 21118751) B21118751
theorem B2316599 : Blo 1028606 2316599 := bstep (se 1 (by rfl) ⟨1737449, by rfl⟩ : syracuseStep 2316599 = 3474899) B3474899
theorem B2318363 : Blo 1028606 2318363 := bstep (se 1 (by rfl) ⟨1738772, by rfl⟩ : syracuseStep 2318363 = 3477545) B3477545
theorem B26731133 : Blo 1028606 26731133 := bstep (se 3 (by rfl) ⟨5012087, by rfl⟩ : syracuseStep 26731133 = 10024175) B10024175
theorem B8807291 : Blo 1028606 8807291 := bstep (se 1 (by rfl) ⟨6605468, by rfl⟩ : syracuseStep 8807291 = 13210937) B13210937
theorem B2319623 : Blo 1028606 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B2386303 : Blo 1028606 2386303 := bstep (se 1 (by rfl) ⟨1789727, by rfl⟩ : syracuseStep 2386303 = 3579455) B3579455
theorem B2321135 : Blo 1028606 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B8351743 : Blo 1028606 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B2322683 : Blo 1028606 2322683 := bstep (se 1 (by rfl) ⟨1742012, by rfl⟩ : syracuseStep 2322683 = 3484025) B3484025
theorem B2323169 : Blo 1028606 2323169 := bstep (se 2 (by rfl) ⟨871188, by rfl⟩ : syracuseStep 2323169 = 1742377) B1742377
theorem B44629973 : Blo 1028606 44629973 := bstep (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) B1046015
theorem B134153165 : Blo 1028606 134153165 := bstep (se 3 (by rfl) ⟨25153718, by rfl⟩ : syracuseStep 134153165 = 50307437) B50307437
theorem B1543721 : Blo 1028606 1543721 := bstep (se 2 (by rfl) ⟨578895, by rfl⟩ : syracuseStep 1543721 = 1157791) B1157791
theorem B1544399 : Blo 1028606 1544399 := bstep (se 1 (by rfl) ⟨1158299, by rfl⟩ : syracuseStep 1544399 = 2316599) B2316599
theorem B1545353 : Blo 1028606 1545353 := bstep (se 2 (by rfl) ⟨579507, by rfl⟩ : syracuseStep 1545353 = 1159015) B1159015
theorem B1545575 : Blo 1028606 1545575 := bstep (se 1 (by rfl) ⟨1159181, by rfl⟩ : syracuseStep 1545575 = 2318363) B2318363
theorem B1545833 : Blo 1028606 1545833 := bstep (se 2 (by rfl) ⟨579687, by rfl⟩ : syracuseStep 1545833 = 1159375) B1159375
theorem B5871527 : Blo 1028606 5871527 := bstep (se 1 (by rfl) ⟨4403645, by rfl⟩ : syracuseStep 5871527 = 8807291) B8807291
theorem B1546415 : Blo 1028606 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B1547423 : Blo 1028606 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B1548455 : Blo 1028606 1548455 := bstep (se 1 (by rfl) ⟨1161341, by rfl⟩ : syracuseStep 1548455 = 2322683) B2322683
theorem B1548779 : Blo 1028606 1548779 := bstep (se 1 (by rfl) ⟨1161584, by rfl⟩ : syracuseStep 1548779 = 2323169) B2323169
theorem B12726949 : Blo 1028606 12726949 := bstep (se 4 (by rfl) ⟨1193151, by rfl⟩ : syracuseStep 12726949 = 2386303) B2386303
theorem B2929385 : Blo 1028606 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B9386111 : Blo 1028606 9386111 := bstep (se 1 (by rfl) ⟨7039583, by rfl⟩ : syracuseStep 9386111 = 14079167) B14079167
theorem B1031327 : Blo 1028606 1031327 := bstep (se 1 (by rfl) ⟨773495, by rfl⟩ : syracuseStep 1031327 = 1546991) B1546991
theorem B5655017 : Blo 1028606 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B2315753 : Blo 1028606 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B11135657 : Blo 1028606 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B17820755 : Blo 1028606 17820755 := bstep (se 1 (by rfl) ⟨13365566, by rfl⟩ : syracuseStep 17820755 = 26731133) B26731133
theorem B2321747 : Blo 1028606 2321747 := bstep (se 1 (by rfl) ⟨1741310, by rfl⟩ : syracuseStep 2321747 = 3482621) B3482621
theorem B7434179 : Blo 1028606 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B29753315 : Blo 1028606 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B3770011 : Blo 1028606 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B1543835 : Blo 1028606 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B29695085 : Blo 1028606 29695085 := bstep (se 3 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 29695085 = 11135657) B11135657
theorem B1547831 : Blo 1028606 1547831 := bstep (se 1 (by rfl) ⟨1160873, by rfl⟩ : syracuseStep 1547831 = 2321747) B2321747
theorem B4956119 : Blo 1028606 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B19835543 : Blo 1028606 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B89435443 : Blo 1028606 89435443 := bstep (se 1 (by rfl) ⟨67076582, by rfl⟩ : syracuseStep 89435443 = 134153165) B134153165
theorem B1029147 : Blo 1028606 1029147 := bstep (se 1 (by rfl) ⟨771860, by rfl⟩ : syracuseStep 1029147 = 1543721) B1543721
theorem B1029599 : Blo 1028606 1029599 := bstep (se 1 (by rfl) ⟨772199, by rfl⟩ : syracuseStep 1029599 = 1544399) B1544399
theorem B1030235 : Blo 1028606 1030235 := bstep (se 1 (by rfl) ⟨772676, by rfl⟩ : syracuseStep 1030235 = 1545353) B1545353
theorem B1030383 : Blo 1028606 1030383 := bstep (se 1 (by rfl) ⟨772787, by rfl⟩ : syracuseStep 1030383 = 1545575) B1545575
theorem B1030555 : Blo 1028606 1030555 := bstep (se 1 (by rfl) ⟨772916, by rfl⟩ : syracuseStep 1030555 = 1545833) B1545833
theorem B3914351 : Blo 1028606 3914351 := bstep (se 1 (by rfl) ⟨2935763, by rfl⟩ : syracuseStep 3914351 = 5871527) B5871527
theorem B1030943 : Blo 1028606 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B1031615 : Blo 1028606 1031615 := bstep (se 1 (by rfl) ⟨773711, by rfl⟩ : syracuseStep 1031615 = 1547423) B1547423
theorem B1032303 : Blo 1028606 1032303 := bstep (se 1 (by rfl) ⟨774227, by rfl⟩ : syracuseStep 1032303 = 1548455) B1548455
theorem B1032519 : Blo 1028606 1032519 := bstep (se 1 (by rfl) ⟨774389, by rfl⟩ : syracuseStep 1032519 = 1548779) B1548779
theorem B11880503 : Blo 1028606 11880503 := bstep (se 1 (by rfl) ⟨8910377, by rfl⟩ : syracuseStep 11880503 = 17820755) B17820755
theorem B1952923 : Blo 1028606 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B16969265 : Blo 1028606 16969265 := bstep (se 2 (by rfl) ⟨6363474, by rfl⟩ : syracuseStep 16969265 = 12726949) B12726949
theorem B6257407 : Blo 1028606 6257407 := bstep (se 1 (by rfl) ⟨4693055, by rfl⟩ : syracuseStep 6257407 = 9386111) B9386111
theorem B119247257 : Blo 1028606 119247257 := bstep (se 2 (by rfl) ⟨44717721, by rfl⟩ : syracuseStep 119247257 = 89435443) B89435443
theorem B19796723 : Blo 1028606 19796723 := bstep (se 1 (by rfl) ⟨14847542, by rfl⟩ : syracuseStep 19796723 = 29695085) B29695085
theorem B11312843 : Blo 1028606 11312843 := bstep (se 1 (by rfl) ⟨8484632, by rfl⟩ : syracuseStep 11312843 = 16969265) B16969265
theorem B5026681 : Blo 1028606 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B1029223 : Blo 1028606 1029223 := bstep (se 1 (by rfl) ⟨771917, by rfl⟩ : syracuseStep 1029223 = 1543835) B1543835
theorem B2603897 : Blo 1028606 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B1031887 : Blo 1028606 1031887 := bstep (se 1 (by rfl) ⟨773915, by rfl⟩ : syracuseStep 1031887 = 1547831) B1547831
theorem B13223695 : Blo 1028606 13223695 := bstep (se 1 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 13223695 = 19835543) B19835543
theorem B8343209 : Blo 1028606 8343209 := bstep (se 2 (by rfl) ⟨3128703, by rfl⟩ : syracuseStep 8343209 = 6257407) B6257407
theorem B2609567 : Blo 1028606 2609567 := bstep (se 1 (by rfl) ⟨1957175, by rfl⟩ : syracuseStep 2609567 = 3914351) B3914351
theorem B7920335 : Blo 1028606 7920335 := bstep (se 1 (by rfl) ⟨5940251, by rfl⟩ : syracuseStep 7920335 = 11880503) B11880503
theorem B3304079 : Blo 1028606 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B17631593 : Blo 1028606 17631593 := bstep (se 2 (by rfl) ⟨6611847, by rfl⟩ : syracuseStep 17631593 = 13223695) B13223695
theorem B79498171 : Blo 1028606 79498171 := bstep (se 1 (by rfl) ⟨59623628, by rfl⟩ : syracuseStep 79498171 = 119247257) B119247257
theorem B1739711 : Blo 1028606 1739711 := bstep (se 1 (by rfl) ⟨1304783, by rfl⟩ : syracuseStep 1739711 = 2609567) B2609567
theorem B5280223 : Blo 1028606 5280223 := bstep (se 1 (by rfl) ⟨3960167, by rfl⟩ : syracuseStep 5280223 = 7920335) B7920335
theorem B26808965 : Blo 1028606 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B2202719 : Blo 1028606 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B30167581 : Blo 1028606 30167581 := bstep (se 3 (by rfl) ⟨5656421, by rfl⟩ : syracuseStep 30167581 = 11312843) B11312843
theorem B13197815 : Blo 1028606 13197815 := bstep (se 1 (by rfl) ⟨9898361, by rfl⟩ : syracuseStep 13197815 = 19796723) B19796723
theorem B22248557 : Blo 1028606 22248557 := bstep (se 3 (by rfl) ⟨4171604, by rfl⟩ : syracuseStep 22248557 = 8343209) B8343209
theorem B1735931 : Blo 1028606 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B5873917 : Blo 1028606 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B1157287 : Blo 1028606 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B1159807 : Blo 1028606 1159807 := bstep (se 1 (by rfl) ⟨869855, by rfl⟩ : syracuseStep 1159807 = 1739711) B1739711
theorem B17872643 : Blo 1028606 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B8798543 : Blo 1028606 8798543 := bstep (se 1 (by rfl) ⟨6598907, by rfl⟩ : syracuseStep 8798543 = 13197815) B13197815
theorem B40223441 : Blo 1028606 40223441 := bstep (se 2 (by rfl) ⟨15083790, by rfl⟩ : syracuseStep 40223441 = 30167581) B30167581
theorem B14832371 : Blo 1028606 14832371 := bstep (se 1 (by rfl) ⟨11124278, by rfl⟩ : syracuseStep 14832371 = 22248557) B22248557
theorem B11754395 : Blo 1028606 11754395 := bstep (se 1 (by rfl) ⟨8815796, by rfl⟩ : syracuseStep 11754395 = 17631593) B17631593
theorem B105997561 : Blo 1028606 105997561 := bstep (se 2 (by rfl) ⟨39749085, by rfl⟩ : syracuseStep 105997561 = 79498171) B79498171
theorem B7040297 : Blo 1028606 7040297 := bstep (se 2 (by rfl) ⟨2640111, by rfl⟩ : syracuseStep 7040297 = 5280223) B5280223
theorem B5865695 : Blo 1028606 5865695 := bstep (se 1 (by rfl) ⟨4399271, by rfl⟩ : syracuseStep 5865695 = 8798543) B8798543
theorem B7831889 : Blo 1028606 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B1543049 : Blo 1028606 1543049 := bstep (se 2 (by rfl) ⟨578643, by rfl⟩ : syracuseStep 1543049 = 1157287) B1157287
theorem B7836263 : Blo 1028606 7836263 := bstep (se 1 (by rfl) ⟨5877197, by rfl⟩ : syracuseStep 7836263 = 11754395) B11754395
theorem B1546409 : Blo 1028606 1546409 := bstep (se 2 (by rfl) ⟨579903, by rfl⟩ : syracuseStep 1546409 = 1159807) B1159807
theorem B565320325 : Blo 1028606 565320325 := bstep (se 4 (by rfl) ⟨52998780, by rfl⟩ : syracuseStep 565320325 = 105997561) B105997561
theorem B26815627 : Blo 1028606 26815627 := bstep (se 1 (by rfl) ⟨20111720, by rfl⟩ : syracuseStep 26815627 = 40223441) B40223441
theorem B11915095 : Blo 1028606 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B9888247 : Blo 1028606 9888247 := bstep (se 1 (by rfl) ⟨7416185, by rfl⟩ : syracuseStep 9888247 = 14832371) B14832371
theorem B18774125 : Blo 1028606 18774125 := bstep (se 3 (by rfl) ⟨3520148, by rfl⟩ : syracuseStep 18774125 = 7040297) B7040297
theorem B35754169 : Blo 1028606 35754169 := bstep (se 2 (by rfl) ⟨13407813, by rfl⟩ : syracuseStep 35754169 = 26815627) B26815627
theorem B3910463 : Blo 1028606 3910463 := bstep (se 1 (by rfl) ⟨2932847, by rfl⟩ : syracuseStep 3910463 = 5865695) B5865695
theorem B5221259 : Blo 1028606 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B13184329 : Blo 1028606 13184329 := bstep (se 2 (by rfl) ⟨4944123, by rfl⟩ : syracuseStep 13184329 = 9888247) B9888247
theorem B1028699 : Blo 1028606 1028699 := bstep (se 1 (by rfl) ⟨771524, by rfl⟩ : syracuseStep 1028699 = 1543049) B1543049
theorem B5224175 : Blo 1028606 5224175 := bstep (se 1 (by rfl) ⟨3918131, by rfl⟩ : syracuseStep 5224175 = 7836263) B7836263
theorem B1030939 : Blo 1028606 1030939 := bstep (se 1 (by rfl) ⟨773204, by rfl⟩ : syracuseStep 1030939 = 1546409) B1546409
theorem B15886793 : Blo 1028606 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B753760433 : Blo 1028606 753760433 := bstep (se 2 (by rfl) ⟨282660162, by rfl⟩ : syracuseStep 753760433 = 565320325) B565320325
theorem B12516083 : Blo 1028606 12516083 := bstep (se 1 (by rfl) ⟨9387062, by rfl⟩ : syracuseStep 12516083 = 18774125) B18774125
theorem B10591195 : Blo 1028606 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B3480839 : Blo 1028606 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B3482783 : Blo 1028606 3482783 := bstep (se 1 (by rfl) ⟨2612087, by rfl⟩ : syracuseStep 3482783 = 5224175) B5224175
theorem B502506955 : Blo 1028606 502506955 := bstep (se 1 (by rfl) ⟨376880216, by rfl⟩ : syracuseStep 502506955 = 753760433) B753760433
theorem B17579105 : Blo 1028606 17579105 := bstep (se 2 (by rfl) ⟨6592164, by rfl⟩ : syracuseStep 17579105 = 13184329) B13184329
theorem B2606975 : Blo 1028606 2606975 := bstep (se 1 (by rfl) ⟨1955231, by rfl⟩ : syracuseStep 2606975 = 3910463) B3910463
theorem B8344055 : Blo 1028606 8344055 := bstep (se 1 (by rfl) ⟨6258041, by rfl⟩ : syracuseStep 8344055 = 12516083) B12516083
theorem B47672225 : Blo 1028606 47672225 := bstep (se 2 (by rfl) ⟨17877084, by rfl⟩ : syracuseStep 47672225 = 35754169) B35754169
theorem B1737983 : Blo 1028606 1737983 := bstep (se 1 (by rfl) ⟨1303487, by rfl⟩ : syracuseStep 1737983 = 2606975) B2606975
theorem B2680037093 : Blo 1028606 2680037093 := bstep (se 4 (by rfl) ⟨251253477, by rfl⟩ : syracuseStep 2680037093 = 502506955) B502506955
theorem B11719403 : Blo 1028606 11719403 := bstep (se 1 (by rfl) ⟨8789552, by rfl⟩ : syracuseStep 11719403 = 17579105) B17579105
theorem B5562703 : Blo 1028606 5562703 := bstep (se 1 (by rfl) ⟨4172027, by rfl⟩ : syracuseStep 5562703 = 8344055) B8344055
theorem B2320559 : Blo 1028606 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B2321855 : Blo 1028606 2321855 := bstep (se 1 (by rfl) ⟨1741391, by rfl⟩ : syracuseStep 2321855 = 3482783) B3482783
theorem B31781483 : Blo 1028606 31781483 := bstep (se 1 (by rfl) ⟨23836112, by rfl⟩ : syracuseStep 31781483 = 47672225) B47672225
theorem B14121593 : Blo 1028606 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B1547039 : Blo 1028606 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B1547903 : Blo 1028606 1547903 := bstep (se 1 (by rfl) ⟨1160927, by rfl⟩ : syracuseStep 1547903 = 2321855) B2321855
theorem B9414395 : Blo 1028606 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B7416937 : Blo 1028606 7416937 := bstep (se 2 (by rfl) ⟨2781351, by rfl⟩ : syracuseStep 7416937 = 5562703) B5562703
theorem B1158655 : Blo 1028606 1158655 := bstep (se 1 (by rfl) ⟨868991, by rfl⟩ : syracuseStep 1158655 = 1737983) B1737983
theorem B7812935 : Blo 1028606 7812935 := bstep (se 1 (by rfl) ⟨5859701, by rfl⟩ : syracuseStep 7812935 = 11719403) B11719403
theorem B1786691395 : Blo 1028606 1786691395 := bstep (se 1 (by rfl) ⟨1340018546, by rfl⟩ : syracuseStep 1786691395 = 2680037093) B2680037093
theorem B21187655 : Blo 1028606 21187655 := bstep (se 1 (by rfl) ⟨15890741, by rfl⟩ : syracuseStep 21187655 = 31781483) B31781483
theorem B14125103 : Blo 1028606 14125103 := bstep (se 1 (by rfl) ⟨10593827, by rfl⟩ : syracuseStep 14125103 = 21187655) B21187655
theorem B1544873 : Blo 1028606 1544873 := bstep (se 2 (by rfl) ⟨579327, by rfl⟩ : syracuseStep 1544873 = 1158655) B1158655
theorem B1031359 : Blo 1028606 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B1031935 : Blo 1028606 1031935 := bstep (se 1 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 1031935 = 1547903) B1547903
theorem B6276263 : Blo 1028606 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B2382255193 : Blo 1028606 2382255193 := bstep (se 2 (by rfl) ⟨893345697, by rfl⟩ : syracuseStep 2382255193 = 1786691395) B1786691395
theorem B9889249 : Blo 1028606 9889249 := bstep (se 2 (by rfl) ⟨3708468, by rfl⟩ : syracuseStep 9889249 = 7416937) B7416937
theorem B5208623 : Blo 1028606 5208623 := bstep (se 1 (by rfl) ⟨3906467, by rfl⟩ : syracuseStep 5208623 = 7812935) B7812935
theorem B3176340257 : Blo 1028606 3176340257 := bstep (se 2 (by rfl) ⟨1191127596, by rfl⟩ : syracuseStep 3176340257 = 2382255193) B2382255193
theorem B9416735 : Blo 1028606 9416735 := bstep (se 1 (by rfl) ⟨7062551, by rfl⟩ : syracuseStep 9416735 = 14125103) B14125103
theorem B13185665 : Blo 1028606 13185665 := bstep (se 2 (by rfl) ⟨4944624, by rfl⟩ : syracuseStep 13185665 = 9889249) B9889249
theorem B1029915 : Blo 1028606 1029915 := bstep (se 1 (by rfl) ⟨772436, by rfl⟩ : syracuseStep 1029915 = 1544873) B1544873
theorem B16736701 : Blo 1028606 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B3472415 : Blo 1028606 3472415 := bstep (se 1 (by rfl) ⟨2604311, by rfl⟩ : syracuseStep 3472415 = 5208623) B5208623
theorem B22315601 : Blo 1028606 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B8790443 : Blo 1028606 8790443 := bstep (se 1 (by rfl) ⟨6592832, by rfl⟩ : syracuseStep 8790443 = 13185665) B13185665
theorem B6277823 : Blo 1028606 6277823 := bstep (se 1 (by rfl) ⟨4708367, by rfl⟩ : syracuseStep 6277823 = 9416735) B9416735
theorem B2314943 : Blo 1028606 2314943 := bstep (se 1 (by rfl) ⟨1736207, by rfl⟩ : syracuseStep 2314943 = 3472415) B3472415
theorem B2117560171 : Blo 1028606 2117560171 := bstep (se 1 (by rfl) ⟨1588170128, by rfl⟩ : syracuseStep 2117560171 = 3176340257) B3176340257
theorem B14877067 : Blo 1028606 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B1543295 : Blo 1028606 1543295 := bstep (se 1 (by rfl) ⟨1157471, by rfl⟩ : syracuseStep 1543295 = 2314943) B2314943
theorem B4185215 : Blo 1028606 4185215 := bstep (se 1 (by rfl) ⟨3138911, by rfl⟩ : syracuseStep 4185215 = 6277823) B6277823
theorem B2823413561 : Blo 1028606 2823413561 := bstep (se 2 (by rfl) ⟨1058780085, by rfl⟩ : syracuseStep 2823413561 = 2117560171) B2117560171
theorem B5860295 : Blo 1028606 5860295 := bstep (se 1 (by rfl) ⟨4395221, by rfl⟩ : syracuseStep 5860295 = 8790443) B8790443
theorem B2790143 : Blo 1028606 2790143 := bstep (se 1 (by rfl) ⟨2092607, by rfl⟩ : syracuseStep 2790143 = 4185215) B4185215
theorem B3906863 : Blo 1028606 3906863 := bstep (se 1 (by rfl) ⟨2930147, by rfl⟩ : syracuseStep 3906863 = 5860295) B5860295
theorem B19836089 : Blo 1028606 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B1028863 : Blo 1028606 1028863 := bstep (se 1 (by rfl) ⟨771647, by rfl⟩ : syracuseStep 1028863 = 1543295) B1543295
theorem B1882275707 : Blo 1028606 1882275707 := bstep (se 1 (by rfl) ⟨1411706780, by rfl⟩ : syracuseStep 1882275707 = 2823413561) B2823413561
theorem B2604575 : Blo 1028606 2604575 := bstep (se 1 (by rfl) ⟨1953431, by rfl⟩ : syracuseStep 2604575 = 3906863) B3906863
theorem B13224059 : Blo 1028606 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B1860095 : Blo 1028606 1860095 := bstep (se 1 (by rfl) ⟨1395071, by rfl⟩ : syracuseStep 1860095 = 2790143) B2790143
theorem B1254850471 : Blo 1028606 1254850471 := bstep (se 1 (by rfl) ⟨941137853, by rfl⟩ : syracuseStep 1254850471 = 1882275707) B1882275707
theorem B8816039 : Blo 1028606 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B4960253 : Blo 1028606 4960253 := bstep (se 3 (by rfl) ⟨930047, by rfl⟩ : syracuseStep 4960253 = 1860095) B1860095
theorem B6692535845 : Blo 1028606 6692535845 := bstep (se 4 (by rfl) ⟨627425235, by rfl⟩ : syracuseStep 6692535845 = 1254850471) B1254850471
theorem B1736383 : Blo 1028606 1736383 := bstep (se 1 (by rfl) ⟨1302287, by rfl⟩ : syracuseStep 1736383 = 2604575) B2604575
theorem B5877359 : Blo 1028606 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B2315177 : Blo 1028606 2315177 := bstep (se 2 (by rfl) ⟨868191, by rfl⟩ : syracuseStep 2315177 = 1736383) B1736383
theorem B3306835 : Blo 1028606 3306835 := bstep (se 1 (by rfl) ⟨2480126, by rfl⟩ : syracuseStep 3306835 = 4960253) B4960253
theorem B4461690563 : Blo 1028606 4461690563 := bstep (se 1 (by rfl) ⟨3346267922, by rfl⟩ : syracuseStep 4461690563 = 6692535845) B6692535845
theorem B1543451 : Blo 1028606 1543451 := bstep (se 1 (by rfl) ⟨1157588, by rfl⟩ : syracuseStep 1543451 = 2315177) B2315177
theorem B2974460375 : Blo 1028606 2974460375 := bstep (se 1 (by rfl) ⟨2230845281, by rfl⟩ : syracuseStep 2974460375 = 4461690563) B4461690563
theorem B4409113 : Blo 1028606 4409113 := bstep (se 2 (by rfl) ⟨1653417, by rfl⟩ : syracuseStep 4409113 = 3306835) B3306835
theorem B3918239 : Blo 1028606 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B1028967 : Blo 1028606 1028967 := bstep (se 1 (by rfl) ⟨771725, by rfl⟩ : syracuseStep 1028967 = 1543451) B1543451
theorem B5878817 : Blo 1028606 5878817 := bstep (se 2 (by rfl) ⟨2204556, by rfl⟩ : syracuseStep 5878817 = 4409113) B4409113
theorem B1982973583 : Blo 1028606 1982973583 := bstep (se 1 (by rfl) ⟨1487230187, by rfl⟩ : syracuseStep 1982973583 = 2974460375) B2974460375
theorem B2612159 : Blo 1028606 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B1741439 : Blo 1028606 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B2643964777 : Blo 1028606 2643964777 := bstep (se 2 (by rfl) ⟨991486791, by rfl⟩ : syracuseStep 2643964777 = 1982973583) B1982973583
theorem B3919211 : Blo 1028606 3919211 := bstep (se 1 (by rfl) ⟨2939408, by rfl⟩ : syracuseStep 3919211 = 5878817) B5878817
theorem B3525286369 : Blo 1028606 3525286369 := bstep (se 2 (by rfl) ⟨1321982388, by rfl⟩ : syracuseStep 3525286369 = 2643964777) B2643964777
theorem B1160959 : Blo 1028606 1160959 := bstep (se 1 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 1160959 = 1741439) B1741439
theorem B2612807 : Blo 1028606 2612807 := bstep (se 1 (by rfl) ⟨1959605, by rfl⟩ : syracuseStep 2612807 = 3919211) B3919211
theorem B1741871 : Blo 1028606 1741871 := bstep (se 1 (by rfl) ⟨1306403, by rfl⟩ : syracuseStep 1741871 = 2612807) B2612807
theorem B1547945 : Blo 1028606 1547945 := bstep (se 2 (by rfl) ⟨580479, by rfl⟩ : syracuseStep 1547945 = 1160959) B1160959
theorem B4700381825 : Blo 1028606 4700381825 := bstep (se 2 (by rfl) ⟨1762643184, by rfl⟩ : syracuseStep 4700381825 = 3525286369) B3525286369
theorem B1161247 : Blo 1028606 1161247 := bstep (se 1 (by rfl) ⟨870935, by rfl⟩ : syracuseStep 1161247 = 1741871) B1741871
theorem B1031963 : Blo 1028606 1031963 := bstep (se 1 (by rfl) ⟨773972, by rfl⟩ : syracuseStep 1031963 = 1547945) B1547945
theorem B3133587883 : Blo 1028606 3133587883 := bstep (se 1 (by rfl) ⟨2350190912, by rfl⟩ : syracuseStep 3133587883 = 4700381825) B4700381825
theorem B4178117177 : Blo 1028606 4178117177 := bstep (se 2 (by rfl) ⟨1566793941, by rfl⟩ : syracuseStep 4178117177 = 3133587883) B3133587883
theorem B1548329 : Blo 1028606 1548329 := bstep (se 2 (by rfl) ⟨580623, by rfl⟩ : syracuseStep 1548329 = 1161247) B1161247
theorem B2785411451 : Blo 1028606 2785411451 := bstep (se 1 (by rfl) ⟨2089058588, by rfl⟩ : syracuseStep 2785411451 = 4178117177) B4178117177
theorem B1032219 : Blo 1028606 1032219 := bstep (se 1 (by rfl) ⟨774164, by rfl⟩ : syracuseStep 1032219 = 1548329) B1548329
theorem B1856940967 : Blo 1028606 1856940967 := bstep (se 1 (by rfl) ⟨1392705725, by rfl⟩ : syracuseStep 1856940967 = 2785411451) B2785411451
theorem B2475921289 : Blo 1028606 2475921289 := bstep (se 2 (by rfl) ⟨928470483, by rfl⟩ : syracuseStep 2475921289 = 1856940967) B1856940967
theorem B3301228385 : Blo 1028606 3301228385 := bstep (se 2 (by rfl) ⟨1237960644, by rfl⟩ : syracuseStep 3301228385 = 2475921289) B2475921289
theorem B2200818923 : Blo 1028606 2200818923 := bstep (se 1 (by rfl) ⟨1650614192, by rfl⟩ : syracuseStep 2200818923 = 3301228385) B3301228385
theorem B1467212615 : Blo 1028606 1467212615 := bstep (se 1 (by rfl) ⟨1100409461, by rfl⟩ : syracuseStep 1467212615 = 2200818923) B2200818923
theorem B978141743 : Blo 1028606 978141743 := bstep (se 1 (by rfl) ⟨733606307, by rfl⟩ : syracuseStep 978141743 = 1467212615) B1467212615
theorem B652094495 : Blo 1028606 652094495 := bstep (se 1 (by rfl) ⟨489070871, by rfl⟩ : syracuseStep 652094495 = 978141743) B978141743
theorem B434729663 : Blo 1028606 434729663 := bstep (se 1 (by rfl) ⟨326047247, by rfl⟩ : syracuseStep 434729663 = 652094495) B652094495
theorem B289819775 : Blo 1028606 289819775 := bstep (se 1 (by rfl) ⟨217364831, by rfl⟩ : syracuseStep 289819775 = 434729663) B434729663
theorem B193213183 : Blo 1028606 193213183 := bstep (se 1 (by rfl) ⟨144909887, by rfl⟩ : syracuseStep 193213183 = 289819775) B289819775
theorem B257617577 : Blo 1028606 257617577 := bstep (se 2 (by rfl) ⟨96606591, by rfl⟩ : syracuseStep 257617577 = 193213183) B193213183
theorem B171745051 : Blo 1028606 171745051 := bstep (se 1 (by rfl) ⟨128808788, by rfl⟩ : syracuseStep 171745051 = 257617577) B257617577
theorem B228993401 : Blo 1028606 228993401 := bstep (se 2 (by rfl) ⟨85872525, by rfl⟩ : syracuseStep 228993401 = 171745051) B171745051
theorem B152662267 : Blo 1028606 152662267 := bstep (se 1 (by rfl) ⟨114496700, by rfl⟩ : syracuseStep 152662267 = 228993401) B228993401
theorem B203549689 : Blo 1028606 203549689 := bstep (se 2 (by rfl) ⟨76331133, by rfl⟩ : syracuseStep 203549689 = 152662267) B152662267
theorem B271399585 : Blo 1028606 271399585 := bstep (se 2 (by rfl) ⟨101774844, by rfl⟩ : syracuseStep 271399585 = 203549689) B203549689
theorem B361866113 : Blo 1028606 361866113 := bstep (se 2 (by rfl) ⟨135699792, by rfl⟩ : syracuseStep 361866113 = 271399585) B271399585
theorem B241244075 : Blo 1028606 241244075 := bstep (se 1 (by rfl) ⟨180933056, by rfl⟩ : syracuseStep 241244075 = 361866113) B361866113
theorem B160829383 : Blo 1028606 160829383 := bstep (se 1 (by rfl) ⟨120622037, by rfl⟩ : syracuseStep 160829383 = 241244075) B241244075
theorem B214439177 : Blo 1028606 214439177 := bstep (se 2 (by rfl) ⟨80414691, by rfl⟩ : syracuseStep 214439177 = 160829383) B160829383
theorem B142959451 : Blo 1028606 142959451 := bstep (se 1 (by rfl) ⟨107219588, by rfl⟩ : syracuseStep 142959451 = 214439177) B214439177
theorem B190612601 : Blo 1028606 190612601 := bstep (se 2 (by rfl) ⟨71479725, by rfl⟩ : syracuseStep 190612601 = 142959451) B142959451
theorem B127075067 : Blo 1028606 127075067 := bstep (se 1 (by rfl) ⟨95306300, by rfl⟩ : syracuseStep 127075067 = 190612601) B190612601
theorem B84716711 : Blo 1028606 84716711 := bstep (se 1 (by rfl) ⟨63537533, by rfl⟩ : syracuseStep 84716711 = 127075067) B127075067
theorem B56477807 : Blo 1028606 56477807 := bstep (se 1 (by rfl) ⟨42358355, by rfl⟩ : syracuseStep 56477807 = 84716711) B84716711
theorem B37651871 : Blo 1028606 37651871 := bstep (se 1 (by rfl) ⟨28238903, by rfl⟩ : syracuseStep 37651871 = 56477807) B56477807
theorem B25101247 : Blo 1028606 25101247 := bstep (se 1 (by rfl) ⟨18825935, by rfl⟩ : syracuseStep 25101247 = 37651871) B37651871
theorem B33468329 : Blo 1028606 33468329 := bstep (se 2 (by rfl) ⟨12550623, by rfl⟩ : syracuseStep 33468329 = 25101247) B25101247
theorem B22312219 : Blo 1028606 22312219 := bstep (se 1 (by rfl) ⟨16734164, by rfl⟩ : syracuseStep 22312219 = 33468329) B33468329
theorem B29749625 : Blo 1028606 29749625 := bstep (se 2 (by rfl) ⟨11156109, by rfl⟩ : syracuseStep 29749625 = 22312219) B22312219
theorem B19833083 : Blo 1028606 19833083 := bstep (se 1 (by rfl) ⟨14874812, by rfl⟩ : syracuseStep 19833083 = 29749625) B29749625
theorem B13222055 : Blo 1028606 13222055 := bstep (se 1 (by rfl) ⟨9916541, by rfl⟩ : syracuseStep 13222055 = 19833083) B19833083
theorem B8814703 : Blo 1028606 8814703 := bstep (se 1 (by rfl) ⟨6611027, by rfl⟩ : syracuseStep 8814703 = 13222055) B13222055
theorem B11752937 : Blo 1028606 11752937 := bstep (se 2 (by rfl) ⟨4407351, by rfl⟩ : syracuseStep 11752937 = 8814703) B8814703
theorem B7835291 : Blo 1028606 7835291 := bstep (se 1 (by rfl) ⟨5876468, by rfl⟩ : syracuseStep 7835291 = 11752937) B11752937
theorem B5223527 : Blo 1028606 5223527 := bstep (se 1 (by rfl) ⟨3917645, by rfl⟩ : syracuseStep 5223527 = 7835291) B7835291
theorem B3482351 : Blo 1028606 3482351 := bstep (se 1 (by rfl) ⟨2611763, by rfl⟩ : syracuseStep 3482351 = 5223527) B5223527
theorem B2321567 : Blo 1028606 2321567 := bstep (se 1 (by rfl) ⟨1741175, by rfl⟩ : syracuseStep 2321567 = 3482351) B3482351
theorem B1547711 : Blo 1028606 1547711 := bstep (se 1 (by rfl) ⟨1160783, by rfl⟩ : syracuseStep 1547711 = 2321567) B2321567
theorem B1031807 : Blo 1028606 1031807 := bstep (se 1 (by rfl) ⟨773855, by rfl⟩ : syracuseStep 1031807 = 1547711) B1547711

theorem C0 (j : ℕ) (h1 : 257151 ≤ j) (h2 : j ≤ 257850) : Blo 1028606 (4 * j + 3) := by
  interval_cases j
  · exact B1028607
  · exact B1028611
  · exact B1028615
  · exact B1028619
  · exact B1028623
  · exact B1028627
  · exact B1028631
  · exact B1028635
  · exact B1028639
  · exact B1028643
  · exact B1028647
  · exact B1028651
  · exact B1028655
  · exact B1028659
  · exact B1028663
  · exact B1028667
  · exact B1028671
  · exact B1028675
  · exact B1028679
  · exact B1028683
  · exact B1028687
  · exact B1028691
  · exact B1028695
  · exact B1028699
  · exact B1028703
  · exact B1028707
  · exact B1028711
  · exact B1028715
  · exact B1028719
  · exact B1028723
  · exact B1028727
  · exact B1028731
  · exact B1028735
  · exact B1028739
  · exact B1028743
  · exact B1028747
  · exact B1028751
  · exact B1028755
  · exact B1028759
  · exact B1028763
  · exact B1028767
  · exact B1028771
  · exact B1028775
  · exact B1028779
  · exact B1028783
  · exact B1028787
  · exact B1028791
  · exact B1028795
  · exact B1028799
  · exact B1028803
  · exact B1028807
  · exact B1028811
  · exact B1028815
  · exact B1028819
  · exact B1028823
  · exact B1028827
  · exact B1028831
  · exact B1028835
  · exact B1028839
  · exact B1028843
  · exact B1028847
  · exact B1028851
  · exact B1028855
  · exact B1028859
  · exact B1028863
  · exact B1028867
  · exact B1028871
  · exact B1028875
  · exact B1028879
  · exact B1028883
  · exact B1028887
  · exact B1028891
  · exact B1028895
  · exact B1028899
  · exact B1028903
  · exact B1028907
  · exact B1028911
  · exact B1028915
  · exact B1028919
  · exact B1028923
  · exact B1028927
  · exact B1028931
  · exact B1028935
  · exact B1028939
  · exact B1028943
  · exact B1028947
  · exact B1028951
  · exact B1028955
  · exact B1028959
  · exact B1028963
  · exact B1028967
  · exact B1028971
  · exact B1028975
  · exact B1028979
  · exact B1028983
  · exact B1028987
  · exact B1028991
  · exact B1028995
  · exact B1028999
  · exact B1029003
  · exact B1029007
  · exact B1029011
  · exact B1029015
  · exact B1029019
  · exact B1029023
  · exact B1029027
  · exact B1029031
  · exact B1029035
  · exact B1029039
  · exact B1029043
  · exact B1029047
  · exact B1029051
  · exact B1029055
  · exact B1029059
  · exact B1029063
  · exact B1029067
  · exact B1029071
  · exact B1029075
  · exact B1029079
  · exact B1029083
  · exact B1029087
  · exact B1029091
  · exact B1029095
  · exact B1029099
  · exact B1029103
  · exact B1029107
  · exact B1029111
  · exact B1029115
  · exact B1029119
  · exact B1029123
  · exact B1029127
  · exact B1029131
  · exact B1029135
  · exact B1029139
  · exact B1029143
  · exact B1029147
  · exact B1029151
  · exact B1029155
  · exact B1029159
  · exact B1029163
  · exact B1029167
  · exact B1029171
  · exact B1029175
  · exact B1029179
  · exact B1029183
  · exact B1029187
  · exact B1029191
  · exact B1029195
  · exact B1029199
  · exact B1029203
  · exact B1029207
  · exact B1029211
  · exact B1029215
  · exact B1029219
  · exact B1029223
  · exact B1029227
  · exact B1029231
  · exact B1029235
  · exact B1029239
  · exact B1029243
  · exact B1029247
  · exact B1029251
  · exact B1029255
  · exact B1029259
  · exact B1029263
  · exact B1029267
  · exact B1029271
  · exact B1029275
  · exact B1029279
  · exact B1029283
  · exact B1029287
  · exact B1029291
  · exact B1029295
  · exact B1029299
  · exact B1029303
  · exact B1029307
  · exact B1029311
  · exact B1029315
  · exact B1029319
  · exact B1029323
  · exact B1029327
  · exact B1029331
  · exact B1029335
  · exact B1029339
  · exact B1029343
  · exact B1029347
  · exact B1029351
  · exact B1029355
  · exact B1029359
  · exact B1029363
  · exact B1029367
  · exact B1029371
  · exact B1029375
  · exact B1029379
  · exact B1029383
  · exact B1029387
  · exact B1029391
  · exact B1029395
  · exact B1029399
  · exact B1029403
  · exact B1029407
  · exact B1029411
  · exact B1029415
  · exact B1029419
  · exact B1029423
  · exact B1029427
  · exact B1029431
  · exact B1029435
  · exact B1029439
  · exact B1029443
  · exact B1029447
  · exact B1029451
  · exact B1029455
  · exact B1029459
  · exact B1029463
  · exact B1029467
  · exact B1029471
  · exact B1029475
  · exact B1029479
  · exact B1029483
  · exact B1029487
  · exact B1029491
  · exact B1029495
  · exact B1029499
  · exact B1029503
  · exact B1029507
  · exact B1029511
  · exact B1029515
  · exact B1029519
  · exact B1029523
  · exact B1029527
  · exact B1029531
  · exact B1029535
  · exact B1029539
  · exact B1029543
  · exact B1029547
  · exact B1029551
  · exact B1029555
  · exact B1029559
  · exact B1029563
  · exact B1029567
  · exact B1029571
  · exact B1029575
  · exact B1029579
  · exact B1029583
  · exact B1029587
  · exact B1029591
  · exact B1029595
  · exact B1029599
  · exact B1029603
  · exact B1029607
  · exact B1029611
  · exact B1029615
  · exact B1029619
  · exact B1029623
  · exact B1029627
  · exact B1029631
  · exact B1029635
  · exact B1029639
  · exact B1029643
  · exact B1029647
  · exact B1029651
  · exact B1029655
  · exact B1029659
  · exact B1029663
  · exact B1029667
  · exact B1029671
  · exact B1029675
  · exact B1029679
  · exact B1029683
  · exact B1029687
  · exact B1029691
  · exact B1029695
  · exact B1029699
  · exact B1029703
  · exact B1029707
  · exact B1029711
  · exact B1029715
  · exact B1029719
  · exact B1029723
  · exact B1029727
  · exact B1029731
  · exact B1029735
  · exact B1029739
  · exact B1029743
  · exact B1029747
  · exact B1029751
  · exact B1029755
  · exact B1029759
  · exact B1029763
  · exact B1029767
  · exact B1029771
  · exact B1029775
  · exact B1029779
  · exact B1029783
  · exact B1029787
  · exact B1029791
  · exact B1029795
  · exact B1029799
  · exact B1029803
  · exact B1029807
  · exact B1029811
  · exact B1029815
  · exact B1029819
  · exact B1029823
  · exact B1029827
  · exact B1029831
  · exact B1029835
  · exact B1029839
  · exact B1029843
  · exact B1029847
  · exact B1029851
  · exact B1029855
  · exact B1029859
  · exact B1029863
  · exact B1029867
  · exact B1029871
  · exact B1029875
  · exact B1029879
  · exact B1029883
  · exact B1029887
  · exact B1029891
  · exact B1029895
  · exact B1029899
  · exact B1029903
  · exact B1029907
  · exact B1029911
  · exact B1029915
  · exact B1029919
  · exact B1029923
  · exact B1029927
  · exact B1029931
  · exact B1029935
  · exact B1029939
  · exact B1029943
  · exact B1029947
  · exact B1029951
  · exact B1029955
  · exact B1029959
  · exact B1029963
  · exact B1029967
  · exact B1029971
  · exact B1029975
  · exact B1029979
  · exact B1029983
  · exact B1029987
  · exact B1029991
  · exact B1029995
  · exact B1029999
  · exact B1030003
  · exact B1030007
  · exact B1030011
  · exact B1030015
  · exact B1030019
  · exact B1030023
  · exact B1030027
  · exact B1030031
  · exact B1030035
  · exact B1030039
  · exact B1030043
  · exact B1030047
  · exact B1030051
  · exact B1030055
  · exact B1030059
  · exact B1030063
  · exact B1030067
  · exact B1030071
  · exact B1030075
  · exact B1030079
  · exact B1030083
  · exact B1030087
  · exact B1030091
  · exact B1030095
  · exact B1030099
  · exact B1030103
  · exact B1030107
  · exact B1030111
  · exact B1030115
  · exact B1030119
  · exact B1030123
  · exact B1030127
  · exact B1030131
  · exact B1030135
  · exact B1030139
  · exact B1030143
  · exact B1030147
  · exact B1030151
  · exact B1030155
  · exact B1030159
  · exact B1030163
  · exact B1030167
  · exact B1030171
  · exact B1030175
  · exact B1030179
  · exact B1030183
  · exact B1030187
  · exact B1030191
  · exact B1030195
  · exact B1030199
  · exact B1030203
  · exact B1030207
  · exact B1030211
  · exact B1030215
  · exact B1030219
  · exact B1030223
  · exact B1030227
  · exact B1030231
  · exact B1030235
  · exact B1030239
  · exact B1030243
  · exact B1030247
  · exact B1030251
  · exact B1030255
  · exact B1030259
  · exact B1030263
  · exact B1030267
  · exact B1030271
  · exact B1030275
  · exact B1030279
  · exact B1030283
  · exact B1030287
  · exact B1030291
  · exact B1030295
  · exact B1030299
  · exact B1030303
  · exact B1030307
  · exact B1030311
  · exact B1030315
  · exact B1030319
  · exact B1030323
  · exact B1030327
  · exact B1030331
  · exact B1030335
  · exact B1030339
  · exact B1030343
  · exact B1030347
  · exact B1030351
  · exact B1030355
  · exact B1030359
  · exact B1030363
  · exact B1030367
  · exact B1030371
  · exact B1030375
  · exact B1030379
  · exact B1030383
  · exact B1030387
  · exact B1030391
  · exact B1030395
  · exact B1030399
  · exact B1030403
  · exact B1030407
  · exact B1030411
  · exact B1030415
  · exact B1030419
  · exact B1030423
  · exact B1030427
  · exact B1030431
  · exact B1030435
  · exact B1030439
  · exact B1030443
  · exact B1030447
  · exact B1030451
  · exact B1030455
  · exact B1030459
  · exact B1030463
  · exact B1030467
  · exact B1030471
  · exact B1030475
  · exact B1030479
  · exact B1030483
  · exact B1030487
  · exact B1030491
  · exact B1030495
  · exact B1030499
  · exact B1030503
  · exact B1030507
  · exact B1030511
  · exact B1030515
  · exact B1030519
  · exact B1030523
  · exact B1030527
  · exact B1030531
  · exact B1030535
  · exact B1030539
  · exact B1030543
  · exact B1030547
  · exact B1030551
  · exact B1030555
  · exact B1030559
  · exact B1030563
  · exact B1030567
  · exact B1030571
  · exact B1030575
  · exact B1030579
  · exact B1030583
  · exact B1030587
  · exact B1030591
  · exact B1030595
  · exact B1030599
  · exact B1030603
  · exact B1030607
  · exact B1030611
  · exact B1030615
  · exact B1030619
  · exact B1030623
  · exact B1030627
  · exact B1030631
  · exact B1030635
  · exact B1030639
  · exact B1030643
  · exact B1030647
  · exact B1030651
  · exact B1030655
  · exact B1030659
  · exact B1030663
  · exact B1030667
  · exact B1030671
  · exact B1030675
  · exact B1030679
  · exact B1030683
  · exact B1030687
  · exact B1030691
  · exact B1030695
  · exact B1030699
  · exact B1030703
  · exact B1030707
  · exact B1030711
  · exact B1030715
  · exact B1030719
  · exact B1030723
  · exact B1030727
  · exact B1030731
  · exact B1030735
  · exact B1030739
  · exact B1030743
  · exact B1030747
  · exact B1030751
  · exact B1030755
  · exact B1030759
  · exact B1030763
  · exact B1030767
  · exact B1030771
  · exact B1030775
  · exact B1030779
  · exact B1030783
  · exact B1030787
  · exact B1030791
  · exact B1030795
  · exact B1030799
  · exact B1030803
  · exact B1030807
  · exact B1030811
  · exact B1030815
  · exact B1030819
  · exact B1030823
  · exact B1030827
  · exact B1030831
  · exact B1030835
  · exact B1030839
  · exact B1030843
  · exact B1030847
  · exact B1030851
  · exact B1030855
  · exact B1030859
  · exact B1030863
  · exact B1030867
  · exact B1030871
  · exact B1030875
  · exact B1030879
  · exact B1030883
  · exact B1030887
  · exact B1030891
  · exact B1030895
  · exact B1030899
  · exact B1030903
  · exact B1030907
  · exact B1030911
  · exact B1030915
  · exact B1030919
  · exact B1030923
  · exact B1030927
  · exact B1030931
  · exact B1030935
  · exact B1030939
  · exact B1030943
  · exact B1030947
  · exact B1030951
  · exact B1030955
  · exact B1030959
  · exact B1030963
  · exact B1030967
  · exact B1030971
  · exact B1030975
  · exact B1030979
  · exact B1030983
  · exact B1030987
  · exact B1030991
  · exact B1030995
  · exact B1030999
  · exact B1031003
  · exact B1031007
  · exact B1031011
  · exact B1031015
  · exact B1031019
  · exact B1031023
  · exact B1031027
  · exact B1031031
  · exact B1031035
  · exact B1031039
  · exact B1031043
  · exact B1031047
  · exact B1031051
  · exact B1031055
  · exact B1031059
  · exact B1031063
  · exact B1031067
  · exact B1031071
  · exact B1031075
  · exact B1031079
  · exact B1031083
  · exact B1031087
  · exact B1031091
  · exact B1031095
  · exact B1031099
  · exact B1031103
  · exact B1031107
  · exact B1031111
  · exact B1031115
  · exact B1031119
  · exact B1031123
  · exact B1031127
  · exact B1031131
  · exact B1031135
  · exact B1031139
  · exact B1031143
  · exact B1031147
  · exact B1031151
  · exact B1031155
  · exact B1031159
  · exact B1031163
  · exact B1031167
  · exact B1031171
  · exact B1031175
  · exact B1031179
  · exact B1031183
  · exact B1031187
  · exact B1031191
  · exact B1031195
  · exact B1031199
  · exact B1031203
  · exact B1031207
  · exact B1031211
  · exact B1031215
  · exact B1031219
  · exact B1031223
  · exact B1031227
  · exact B1031231
  · exact B1031235
  · exact B1031239
  · exact B1031243
  · exact B1031247
  · exact B1031251
  · exact B1031255
  · exact B1031259
  · exact B1031263
  · exact B1031267
  · exact B1031271
  · exact B1031275
  · exact B1031279
  · exact B1031283
  · exact B1031287
  · exact B1031291
  · exact B1031295
  · exact B1031299
  · exact B1031303
  · exact B1031307
  · exact B1031311
  · exact B1031315
  · exact B1031319
  · exact B1031323
  · exact B1031327
  · exact B1031331
  · exact B1031335
  · exact B1031339
  · exact B1031343
  · exact B1031347
  · exact B1031351
  · exact B1031355
  · exact B1031359
  · exact B1031363
  · exact B1031367
  · exact B1031371
  · exact B1031375
  · exact B1031379
  · exact B1031383
  · exact B1031387
  · exact B1031391
  · exact B1031395
  · exact B1031399
  · exact B1031403

theorem C1 (j : ℕ) (h1 : 257851 ≤ j) (h2 : j ≤ 258150) : Blo 1028606 (4 * j + 3) := by
  interval_cases j
  · exact B1031407
  · exact B1031411
  · exact B1031415
  · exact B1031419
  · exact B1031423
  · exact B1031427
  · exact B1031431
  · exact B1031435
  · exact B1031439
  · exact B1031443
  · exact B1031447
  · exact B1031451
  · exact B1031455
  · exact B1031459
  · exact B1031463
  · exact B1031467
  · exact B1031471
  · exact B1031475
  · exact B1031479
  · exact B1031483
  · exact B1031487
  · exact B1031491
  · exact B1031495
  · exact B1031499
  · exact B1031503
  · exact B1031507
  · exact B1031511
  · exact B1031515
  · exact B1031519
  · exact B1031523
  · exact B1031527
  · exact B1031531
  · exact B1031535
  · exact B1031539
  · exact B1031543
  · exact B1031547
  · exact B1031551
  · exact B1031555
  · exact B1031559
  · exact B1031563
  · exact B1031567
  · exact B1031571
  · exact B1031575
  · exact B1031579
  · exact B1031583
  · exact B1031587
  · exact B1031591
  · exact B1031595
  · exact B1031599
  · exact B1031603
  · exact B1031607
  · exact B1031611
  · exact B1031615
  · exact B1031619
  · exact B1031623
  · exact B1031627
  · exact B1031631
  · exact B1031635
  · exact B1031639
  · exact B1031643
  · exact B1031647
  · exact B1031651
  · exact B1031655
  · exact B1031659
  · exact B1031663
  · exact B1031667
  · exact B1031671
  · exact B1031675
  · exact B1031679
  · exact B1031683
  · exact B1031687
  · exact B1031691
  · exact B1031695
  · exact B1031699
  · exact B1031703
  · exact B1031707
  · exact B1031711
  · exact B1031715
  · exact B1031719
  · exact B1031723
  · exact B1031727
  · exact B1031731
  · exact B1031735
  · exact B1031739
  · exact B1031743
  · exact B1031747
  · exact B1031751
  · exact B1031755
  · exact B1031759
  · exact B1031763
  · exact B1031767
  · exact B1031771
  · exact B1031775
  · exact B1031779
  · exact B1031783
  · exact B1031787
  · exact B1031791
  · exact B1031795
  · exact B1031799
  · exact B1031803
  · exact B1031807
  · exact B1031811
  · exact B1031815
  · exact B1031819
  · exact B1031823
  · exact B1031827
  · exact B1031831
  · exact B1031835
  · exact B1031839
  · exact B1031843
  · exact B1031847
  · exact B1031851
  · exact B1031855
  · exact B1031859
  · exact B1031863
  · exact B1031867
  · exact B1031871
  · exact B1031875
  · exact B1031879
  · exact B1031883
  · exact B1031887
  · exact B1031891
  · exact B1031895
  · exact B1031899
  · exact B1031903
  · exact B1031907
  · exact B1031911
  · exact B1031915
  · exact B1031919
  · exact B1031923
  · exact B1031927
  · exact B1031931
  · exact B1031935
  · exact B1031939
  · exact B1031943
  · exact B1031947
  · exact B1031951
  · exact B1031955
  · exact B1031959
  · exact B1031963
  · exact B1031967
  · exact B1031971
  · exact B1031975
  · exact B1031979
  · exact B1031983
  · exact B1031987
  · exact B1031991
  · exact B1031995
  · exact B1031999
  · exact B1032003
  · exact B1032007
  · exact B1032011
  · exact B1032015
  · exact B1032019
  · exact B1032023
  · exact B1032027
  · exact B1032031
  · exact B1032035
  · exact B1032039
  · exact B1032043
  · exact B1032047
  · exact B1032051
  · exact B1032055
  · exact B1032059
  · exact B1032063
  · exact B1032067
  · exact B1032071
  · exact B1032075
  · exact B1032079
  · exact B1032083
  · exact B1032087
  · exact B1032091
  · exact B1032095
  · exact B1032099
  · exact B1032103
  · exact B1032107
  · exact B1032111
  · exact B1032115
  · exact B1032119
  · exact B1032123
  · exact B1032127
  · exact B1032131
  · exact B1032135
  · exact B1032139
  · exact B1032143
  · exact B1032147
  · exact B1032151
  · exact B1032155
  · exact B1032159
  · exact B1032163
  · exact B1032167
  · exact B1032171
  · exact B1032175
  · exact B1032179
  · exact B1032183
  · exact B1032187
  · exact B1032191
  · exact B1032195
  · exact B1032199
  · exact B1032203
  · exact B1032207
  · exact B1032211
  · exact B1032215
  · exact B1032219
  · exact B1032223
  · exact B1032227
  · exact B1032231
  · exact B1032235
  · exact B1032239
  · exact B1032243
  · exact B1032247
  · exact B1032251
  · exact B1032255
  · exact B1032259
  · exact B1032263
  · exact B1032267
  · exact B1032271
  · exact B1032275
  · exact B1032279
  · exact B1032283
  · exact B1032287
  · exact B1032291
  · exact B1032295
  · exact B1032299
  · exact B1032303
  · exact B1032307
  · exact B1032311
  · exact B1032315
  · exact B1032319
  · exact B1032323
  · exact B1032327
  · exact B1032331
  · exact B1032335
  · exact B1032339
  · exact B1032343
  · exact B1032347
  · exact B1032351
  · exact B1032355
  · exact B1032359
  · exact B1032363
  · exact B1032367
  · exact B1032371
  · exact B1032375
  · exact B1032379
  · exact B1032383
  · exact B1032387
  · exact B1032391
  · exact B1032395
  · exact B1032399
  · exact B1032403
  · exact B1032407
  · exact B1032411
  · exact B1032415
  · exact B1032419
  · exact B1032423
  · exact B1032427
  · exact B1032431
  · exact B1032435
  · exact B1032439
  · exact B1032443
  · exact B1032447
  · exact B1032451
  · exact B1032455
  · exact B1032459
  · exact B1032463
  · exact B1032467
  · exact B1032471
  · exact B1032475
  · exact B1032479
  · exact B1032483
  · exact B1032487
  · exact B1032491
  · exact B1032495
  · exact B1032499
  · exact B1032503
  · exact B1032507
  · exact B1032511
  · exact B1032515
  · exact B1032519
  · exact B1032523
  · exact B1032527
  · exact B1032531
  · exact B1032535
  · exact B1032539
  · exact B1032543
  · exact B1032547
  · exact B1032551
  · exact B1032555
  · exact B1032559
  · exact B1032563
  · exact B1032567
  · exact B1032571
  · exact B1032575
  · exact B1032579
  · exact B1032583
  · exact B1032587
  · exact B1032591
  · exact B1032595
  · exact B1032599
  · exact B1032603

theorem solution (m : ℕ) (hlo : 1028606 ≤ m) (hhi : m ≤ 1032606) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 257151 ≤ j := by omega
    have hj2 : j ≤ 258150 := by omega
    have hb : Blo 1028606 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 257851 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
