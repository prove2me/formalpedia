-- Prove2me | solution 1 for syracuse_descends_range_916578_920578
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:52.354028+00:00
-- url     : https://prove2.me/submissions/2908717a-9804-4d2d-a829-78f8fd081f4e

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


theorem B1376261 : Blo 916578 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B983053 : Blo 916578 983053 := bbase (se 3 (by rfl) ⟨184322, by rfl⟩ : syracuseStep 983053 = 368645) (by norm_num)
theorem B1376285 : Blo 916578 1376285 := bbase (se 3 (by rfl) ⟨258053, by rfl⟩ : syracuseStep 1376285 = 516107) (by norm_num)
theorem B2293805 : Blo 916578 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B2064437 : Blo 916578 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B1376309 : Blo 916578 1376309 := bbase (se 5 (by rfl) ⟨64514, by rfl⟩ : syracuseStep 1376309 = 129029) (by norm_num)
theorem B4653125 : Blo 916578 4653125 := bbase (se 4 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 4653125 = 872461) (by norm_num)
theorem B1376333 : Blo 916578 1376333 := bbase (se 3 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 1376333 = 516125) (by norm_num)
theorem B1376357 : Blo 916578 1376357 := bbase (se 4 (by rfl) ⟨129033, by rfl⟩ : syracuseStep 1376357 = 258067) (by norm_num)
theorem B2064509 : Blo 916578 2064509 := bbase (se 3 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 2064509 = 774191) (by norm_num)
theorem B1376381 : Blo 916578 1376381 := bbase (se 3 (by rfl) ⟨258071, by rfl⟩ : syracuseStep 1376381 = 516143) (by norm_num)
theorem B1376405 : Blo 916578 1376405 := bbase (se 6 (by rfl) ⟨32259, by rfl⟩ : syracuseStep 1376405 = 64519) (by norm_num)
theorem B1376429 : Blo 916578 1376429 := bbase (se 3 (by rfl) ⟨258080, by rfl⟩ : syracuseStep 1376429 = 516161) (by norm_num)
theorem B2064581 : Blo 916578 2064581 := bbase (se 4 (by rfl) ⟨193554, by rfl⟩ : syracuseStep 2064581 = 387109) (by norm_num)
theorem B1376453 : Blo 916578 1376453 := bbase (se 4 (by rfl) ⟨129042, by rfl⟩ : syracuseStep 1376453 = 258085) (by norm_num)
theorem B1376477 : Blo 916578 1376477 := bbase (se 3 (by rfl) ⟨258089, by rfl⟩ : syracuseStep 1376477 = 516179) (by norm_num)
theorem B2326765 : Blo 916578 2326765 := bbase (se 3 (by rfl) ⟨436268, by rfl⟩ : syracuseStep 2326765 = 872537) (by norm_num)
theorem B1376501 : Blo 916578 1376501 := bbase (se 5 (by rfl) ⟨64523, by rfl⟩ : syracuseStep 1376501 = 129047) (by norm_num)
theorem B2064653 : Blo 916578 2064653 := bbase (se 3 (by rfl) ⟨387122, by rfl⟩ : syracuseStep 2064653 = 774245) (by norm_num)
theorem B1376525 : Blo 916578 1376525 := bbase (se 3 (by rfl) ⟨258098, by rfl⟩ : syracuseStep 1376525 = 516197) (by norm_num)
theorem B1376549 : Blo 916578 1376549 := bbase (se 4 (by rfl) ⟨129051, by rfl⟩ : syracuseStep 1376549 = 258103) (by norm_num)
theorem B1376573 : Blo 916578 1376573 := bbase (se 3 (by rfl) ⟨258107, by rfl⟩ : syracuseStep 1376573 = 516215) (by norm_num)
theorem B2064725 : Blo 916578 2064725 := bbase (se 10 (by rfl) ⟨3024, by rfl⟩ : syracuseStep 2064725 = 6049) (by norm_num)
theorem B1376597 : Blo 916578 1376597 := bbase (se 10 (by rfl) ⟨2016, by rfl⟩ : syracuseStep 1376597 = 4033) (by norm_num)
theorem B2326877 : Blo 916578 2326877 := bbase (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) (by norm_num)
theorem B1376621 : Blo 916578 1376621 := bbase (se 3 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 1376621 = 516233) (by norm_num)
theorem B1376645 : Blo 916578 1376645 := bbase (se 4 (by rfl) ⟨129060, by rfl⟩ : syracuseStep 1376645 = 258121) (by norm_num)
theorem B2064797 : Blo 916578 2064797 := bbase (se 3 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 2064797 = 774299) (by norm_num)
theorem B1376669 : Blo 916578 1376669 := bbase (se 3 (by rfl) ⟨258125, by rfl⟩ : syracuseStep 1376669 = 516251) (by norm_num)
theorem B1376693 : Blo 916578 1376693 := bbase (se 5 (by rfl) ⟨64532, by rfl⟩ : syracuseStep 1376693 = 129065) (by norm_num)
theorem B2097605 : Blo 916578 2097605 := bbase (se 4 (by rfl) ⟨196650, by rfl⟩ : syracuseStep 2097605 = 393301) (by norm_num)
theorem B1376717 : Blo 916578 1376717 := bbase (se 3 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 1376717 = 516269) (by norm_num)
theorem B1769933 : Blo 916578 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B2064869 : Blo 916578 2064869 := bbase (se 4 (by rfl) ⟨193581, by rfl⟩ : syracuseStep 2064869 = 387163) (by norm_num)
theorem B1376741 : Blo 916578 1376741 := bbase (se 4 (by rfl) ⟨129069, by rfl⟩ : syracuseStep 1376741 = 258139) (by norm_num)
theorem B4719077 : Blo 916578 4719077 := bbase (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) (by norm_num)
theorem B1376765 : Blo 916578 1376765 := bbase (se 3 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 1376765 = 516287) (by norm_num)
theorem B1376789 : Blo 916578 1376789 := bbase (se 6 (by rfl) ⟨32268, by rfl⟩ : syracuseStep 1376789 = 64537) (by norm_num)
theorem B2327069 : Blo 916578 2327069 := bbase (se 3 (by rfl) ⟨436325, by rfl⟩ : syracuseStep 2327069 = 872651) (by norm_num)
theorem B2064941 : Blo 916578 2064941 := bbase (se 3 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 2064941 = 774353) (by norm_num)
theorem B1376813 : Blo 916578 1376813 := bbase (se 3 (by rfl) ⟨258152, by rfl⟩ : syracuseStep 1376813 = 516305) (by norm_num)
theorem B1180217 : Blo 916578 1180217 := bbase (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) (by norm_num)
theorem B1376837 : Blo 916578 1376837 := bbase (se 4 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 1376837 = 258157) (by norm_num)
theorem B1376861 : Blo 916578 1376861 := bbase (se 3 (by rfl) ⟨258161, by rfl⟩ : syracuseStep 1376861 = 516323) (by norm_num)
theorem B4194917 : Blo 916578 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B2065013 : Blo 916578 2065013 := bbase (se 5 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 2065013 = 193595) (by norm_num)
theorem B1376885 : Blo 916578 1376885 := bbase (se 5 (by rfl) ⟨64541, by rfl⟩ : syracuseStep 1376885 = 129083) (by norm_num)
theorem B1376909 : Blo 916578 1376909 := bbase (se 3 (by rfl) ⟨258170, by rfl⟩ : syracuseStep 1376909 = 516341) (by norm_num)
theorem B1376933 : Blo 916578 1376933 := bbase (se 4 (by rfl) ⟨129087, by rfl⟩ : syracuseStep 1376933 = 258175) (by norm_num)
theorem B2065085 : Blo 916578 2065085 := bbase (se 3 (by rfl) ⟨387203, by rfl⟩ : syracuseStep 2065085 = 774407) (by norm_num)
theorem B1376957 : Blo 916578 1376957 := bbase (se 3 (by rfl) ⟨258179, by rfl⟩ : syracuseStep 1376957 = 516359) (by norm_num)
theorem B1376981 : Blo 916578 1376981 := bbase (se 7 (by rfl) ⟨16136, by rfl⟩ : syracuseStep 1376981 = 32273) (by norm_num)
theorem B1377005 : Blo 916578 1377005 := bbase (se 3 (by rfl) ⟨258188, by rfl⟩ : syracuseStep 1377005 = 516377) (by norm_num)
theorem B2065157 : Blo 916578 2065157 := bbase (se 4 (by rfl) ⟨193608, by rfl⟩ : syracuseStep 2065157 = 387217) (by norm_num)
theorem B1377029 : Blo 916578 1377029 := bbase (se 4 (by rfl) ⟨129096, by rfl⟩ : syracuseStep 1377029 = 258193) (by norm_num)
theorem B1377053 : Blo 916578 1377053 := bbase (se 3 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 1377053 = 516395) (by norm_num)
theorem B1377077 : Blo 916578 1377077 := bbase (se 5 (by rfl) ⟨64550, by rfl⟩ : syracuseStep 1377077 = 129101) (by norm_num)
theorem B2065229 : Blo 916578 2065229 := bbase (se 3 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 2065229 = 774461) (by norm_num)
theorem B1377101 : Blo 916578 1377101 := bbase (se 3 (by rfl) ⟨258206, by rfl⟩ : syracuseStep 1377101 = 516413) (by norm_num)
theorem B1377125 : Blo 916578 1377125 := bbase (se 4 (by rfl) ⟨129105, by rfl⟩ : syracuseStep 1377125 = 258211) (by norm_num)
theorem B2327413 : Blo 916578 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B1377149 : Blo 916578 1377149 := bbase (se 3 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 1377149 = 516431) (by norm_num)
theorem B2065301 : Blo 916578 2065301 := bbase (se 6 (by rfl) ⟨48405, by rfl⟩ : syracuseStep 2065301 = 96811) (by norm_num)
theorem B1377173 : Blo 916578 1377173 := bbase (se 6 (by rfl) ⟨32277, by rfl⟩ : syracuseStep 1377173 = 64555) (by norm_num)
theorem B1377197 : Blo 916578 1377197 := bbase (se 3 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 1377197 = 516449) (by norm_num)
theorem B1377221 : Blo 916578 1377221 := bbase (se 4 (by rfl) ⟨129114, by rfl⟩ : syracuseStep 1377221 = 258229) (by norm_num)
theorem B2065373 : Blo 916578 2065373 := bbase (se 3 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 2065373 = 774515) (by norm_num)
theorem B1377245 : Blo 916578 1377245 := bbase (se 3 (by rfl) ⟨258233, by rfl⟩ : syracuseStep 1377245 = 516467) (by norm_num)
theorem B2327525 : Blo 916578 2327525 := bbase (se 4 (by rfl) ⟨218205, by rfl⟩ : syracuseStep 2327525 = 436411) (by norm_num)
theorem B1377269 : Blo 916578 1377269 := bbase (se 5 (by rfl) ⟨64559, by rfl⟩ : syracuseStep 1377269 = 129119) (by norm_num)
theorem B1180669 : Blo 916578 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B1377293 : Blo 916578 1377293 := bbase (se 3 (by rfl) ⟨258242, by rfl⟩ : syracuseStep 1377293 = 516485) (by norm_num)
theorem B2065445 : Blo 916578 2065445 := bbase (se 4 (by rfl) ⟨193635, by rfl⟩ : syracuseStep 2065445 = 387271) (by norm_num)
theorem B1377317 : Blo 916578 1377317 := bbase (se 4 (by rfl) ⟨129123, by rfl⟩ : syracuseStep 1377317 = 258247) (by norm_num)
theorem B1377341 : Blo 916578 1377341 := bbase (se 3 (by rfl) ⟨258251, by rfl⟩ : syracuseStep 1377341 = 516503) (by norm_num)
theorem B1377365 : Blo 916578 1377365 := bbase (se 8 (by rfl) ⟨8070, by rfl⟩ : syracuseStep 1377365 = 16141) (by norm_num)
theorem B2065517 : Blo 916578 2065517 := bbase (se 3 (by rfl) ⟨387284, by rfl⟩ : syracuseStep 2065517 = 774569) (by norm_num)
theorem B1377389 : Blo 916578 1377389 := bbase (se 3 (by rfl) ⟨258260, by rfl⟩ : syracuseStep 1377389 = 516521) (by norm_num)
theorem B1377413 : Blo 916578 1377413 := bbase (se 4 (by rfl) ⟨129132, by rfl⟩ : syracuseStep 1377413 = 258265) (by norm_num)
theorem B1377437 : Blo 916578 1377437 := bbase (se 3 (by rfl) ⟨258269, by rfl⟩ : syracuseStep 1377437 = 516539) (by norm_num)
theorem B2327717 : Blo 916578 2327717 := bbase (se 4 (by rfl) ⟨218223, by rfl⟩ : syracuseStep 2327717 = 436447) (by norm_num)
theorem B2065589 : Blo 916578 2065589 := bbase (se 5 (by rfl) ⟨96824, by rfl⟩ : syracuseStep 2065589 = 193649) (by norm_num)
theorem B1377461 : Blo 916578 1377461 := bbase (se 5 (by rfl) ⟨64568, by rfl⟩ : syracuseStep 1377461 = 129137) (by norm_num)
theorem B1377485 : Blo 916578 1377485 := bbase (se 3 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 1377485 = 516557) (by norm_num)
theorem B1377509 : Blo 916578 1377509 := bbase (se 4 (by rfl) ⟨129141, by rfl⟩ : syracuseStep 1377509 = 258283) (by norm_num)
theorem B2065661 : Blo 916578 2065661 := bbase (se 3 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 2065661 = 774623) (by norm_num)
theorem B1377533 : Blo 916578 1377533 := bbase (se 3 (by rfl) ⟨258287, by rfl⟩ : syracuseStep 1377533 = 516575) (by norm_num)
theorem B1377557 : Blo 916578 1377557 := bbase (se 6 (by rfl) ⟨32286, by rfl⟩ : syracuseStep 1377557 = 64573) (by norm_num)
theorem B1377581 : Blo 916578 1377581 := bbase (se 3 (by rfl) ⟨258296, by rfl⟩ : syracuseStep 1377581 = 516593) (by norm_num)
theorem B2065733 : Blo 916578 2065733 := bbase (se 4 (by rfl) ⟨193662, by rfl⟩ : syracuseStep 2065733 = 387325) (by norm_num)
theorem B1377605 : Blo 916578 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B4654421 : Blo 916578 4654421 := bbase (se 12 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 4654421 = 3409) (by norm_num)
theorem B1377629 : Blo 916578 1377629 := bbase (se 3 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 1377629 = 516611) (by norm_num)
theorem B1377653 : Blo 916578 1377653 := bbase (se 5 (by rfl) ⟨64577, by rfl⟩ : syracuseStep 1377653 = 129155) (by norm_num)
theorem B2065805 : Blo 916578 2065805 := bbase (se 3 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 2065805 = 774677) (by norm_num)
theorem B1377677 : Blo 916578 1377677 := bbase (se 3 (by rfl) ⟨258314, by rfl⟩ : syracuseStep 1377677 = 516629) (by norm_num)
theorem B1377701 : Blo 916578 1377701 := bbase (se 4 (by rfl) ⟨129159, by rfl⟩ : syracuseStep 1377701 = 258319) (by norm_num)
theorem B1377725 : Blo 916578 1377725 := bbase (se 3 (by rfl) ⟨258323, by rfl⟩ : syracuseStep 1377725 = 516647) (by norm_num)
theorem B2065877 : Blo 916578 2065877 := bbase (se 7 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 2065877 = 48419) (by norm_num)
theorem B1377749 : Blo 916578 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B1377773 : Blo 916578 1377773 := bbase (se 3 (by rfl) ⟨258332, by rfl⟩ : syracuseStep 1377773 = 516665) (by norm_num)
theorem B2328061 : Blo 916578 2328061 := bbase (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) (by norm_num)
theorem B1377797 : Blo 916578 1377797 := bbase (se 4 (by rfl) ⟨129168, by rfl⟩ : syracuseStep 1377797 = 258337) (by norm_num)
theorem B2065949 : Blo 916578 2065949 := bbase (se 3 (by rfl) ⟨387365, by rfl⟩ : syracuseStep 2065949 = 774731) (by norm_num)
theorem B1377821 : Blo 916578 1377821 := bbase (se 3 (by rfl) ⟨258341, by rfl⟩ : syracuseStep 1377821 = 516683) (by norm_num)
theorem B1377845 : Blo 916578 1377845 := bbase (se 5 (by rfl) ⟨64586, by rfl⟩ : syracuseStep 1377845 = 129173) (by norm_num)
theorem B1377869 : Blo 916578 1377869 := bbase (se 3 (by rfl) ⟨258350, by rfl⟩ : syracuseStep 1377869 = 516701) (by norm_num)
theorem B2066021 : Blo 916578 2066021 := bbase (se 4 (by rfl) ⟨193689, by rfl⟩ : syracuseStep 2066021 = 387379) (by norm_num)
theorem B1377893 : Blo 916578 1377893 := bbase (se 4 (by rfl) ⟨129177, by rfl⟩ : syracuseStep 1377893 = 258355) (by norm_num)
theorem B2328173 : Blo 916578 2328173 := bbase (se 3 (by rfl) ⟨436532, by rfl⟩ : syracuseStep 2328173 = 873065) (by norm_num)
theorem B1377917 : Blo 916578 1377917 := bbase (se 3 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 1377917 = 516719) (by norm_num)
theorem B1377941 : Blo 916578 1377941 := bbase (se 6 (by rfl) ⟨32295, by rfl⟩ : syracuseStep 1377941 = 64591) (by norm_num)
theorem B2066093 : Blo 916578 2066093 := bbase (se 3 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 2066093 = 774785) (by norm_num)
theorem B1377965 : Blo 916578 1377965 := bbase (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) (by norm_num)
theorem B1377989 : Blo 916578 1377989 := bbase (se 4 (by rfl) ⟨129186, by rfl⟩ : syracuseStep 1377989 = 258373) (by norm_num)
theorem B1378013 : Blo 916578 1378013 := bbase (se 3 (by rfl) ⟨258377, by rfl⟩ : syracuseStep 1378013 = 516755) (by norm_num)
theorem B2066165 : Blo 916578 2066165 := bbase (se 5 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 2066165 = 193703) (by norm_num)
theorem B1378037 : Blo 916578 1378037 := bbase (se 5 (by rfl) ⟨64595, by rfl⟩ : syracuseStep 1378037 = 129191) (by norm_num)
theorem B1378061 : Blo 916578 1378061 := bbase (se 3 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 1378061 = 516773) (by norm_num)
theorem B2098973 : Blo 916578 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B1378085 : Blo 916578 1378085 := bbase (se 4 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 1378085 = 258391) (by norm_num)
theorem B2328365 : Blo 916578 2328365 := bbase (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) (by norm_num)
theorem B2066237 : Blo 916578 2066237 := bbase (se 3 (by rfl) ⟨387419, by rfl⟩ : syracuseStep 2066237 = 774839) (by norm_num)
theorem B1378109 : Blo 916578 1378109 := bbase (se 3 (by rfl) ⟨258395, by rfl⟩ : syracuseStep 1378109 = 516791) (by norm_num)
theorem B1378133 : Blo 916578 1378133 := bbase (se 9 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 1378133 = 8075) (by norm_num)
theorem B1378157 : Blo 916578 1378157 := bbase (se 3 (by rfl) ⟨258404, by rfl⟩ : syracuseStep 1378157 = 516809) (by norm_num)
theorem B2066309 : Blo 916578 2066309 := bbase (se 4 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 2066309 = 387433) (by norm_num)
theorem B1378181 : Blo 916578 1378181 := bbase (se 4 (by rfl) ⟨129204, by rfl⟩ : syracuseStep 1378181 = 258409) (by norm_num)
theorem B1378205 : Blo 916578 1378205 := bbase (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) (by norm_num)
theorem B1378229 : Blo 916578 1378229 := bbase (se 5 (by rfl) ⟨64604, by rfl⟩ : syracuseStep 1378229 = 129209) (by norm_num)
theorem B2787269 : Blo 916578 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B2066381 : Blo 916578 2066381 := bbase (se 3 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 2066381 = 774893) (by norm_num)
theorem B1378253 : Blo 916578 1378253 := bbase (se 3 (by rfl) ⟨258422, by rfl⟩ : syracuseStep 1378253 = 516845) (by norm_num)
theorem B1378277 : Blo 916578 1378277 := bbase (se 4 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 1378277 = 258427) (by norm_num)
theorem B1378301 : Blo 916578 1378301 := bbase (se 3 (by rfl) ⟨258431, by rfl⟩ : syracuseStep 1378301 = 516863) (by norm_num)
theorem B2066453 : Blo 916578 2066453 := bbase (se 6 (by rfl) ⟨48432, by rfl⟩ : syracuseStep 2066453 = 96865) (by norm_num)
theorem B1378325 : Blo 916578 1378325 := bbase (se 6 (by rfl) ⟨32304, by rfl⟩ : syracuseStep 1378325 = 64609) (by norm_num)
theorem B1378349 : Blo 916578 1378349 := bbase (se 3 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 1378349 = 516881) (by norm_num)
theorem B7440437 : Blo 916578 7440437 := bbase (se 5 (by rfl) ⟨348770, by rfl⟩ : syracuseStep 7440437 = 697541) (by norm_num)
theorem B1378373 : Blo 916578 1378373 := bbase (se 4 (by rfl) ⟨129222, by rfl⟩ : syracuseStep 1378373 = 258445) (by norm_num)
theorem B2066525 : Blo 916578 2066525 := bbase (se 3 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 2066525 = 774947) (by norm_num)
theorem B1378397 : Blo 916578 1378397 := bbase (se 3 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 1378397 = 516899) (by norm_num)
theorem B1378421 : Blo 916578 1378421 := bbase (se 5 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 1378421 = 129227) (by norm_num)
theorem B2328709 : Blo 916578 2328709 := bbase (se 4 (by rfl) ⟨218316, by rfl⟩ : syracuseStep 2328709 = 436633) (by norm_num)
theorem B1378445 : Blo 916578 1378445 := bbase (se 3 (by rfl) ⟨258458, by rfl⟩ : syracuseStep 1378445 = 516917) (by norm_num)
theorem B2066597 : Blo 916578 2066597 := bbase (se 4 (by rfl) ⟨193743, by rfl⟩ : syracuseStep 2066597 = 387487) (by norm_num)
theorem B1378469 : Blo 916578 1378469 := bbase (se 4 (by rfl) ⟨129231, by rfl⟩ : syracuseStep 1378469 = 258463) (by norm_num)
theorem B1378493 : Blo 916578 1378493 := bbase (se 3 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 1378493 = 516935) (by norm_num)
theorem B1378517 : Blo 916578 1378517 := bbase (se 7 (by rfl) ⟨16154, by rfl⟩ : syracuseStep 1378517 = 32309) (by norm_num)
theorem B2066669 : Blo 916578 2066669 := bbase (se 3 (by rfl) ⟨387500, by rfl⟩ : syracuseStep 2066669 = 775001) (by norm_num)
theorem B1378541 : Blo 916578 1378541 := bbase (se 3 (by rfl) ⟨258476, by rfl⟩ : syracuseStep 1378541 = 516953) (by norm_num)
theorem B2328821 : Blo 916578 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B1378565 : Blo 916578 1378565 := bbase (se 4 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 1378565 = 258481) (by norm_num)
theorem B10455317 : Blo 916578 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B1378589 : Blo 916578 1378589 := bbase (se 3 (by rfl) ⟨258485, by rfl⟩ : syracuseStep 1378589 = 516971) (by norm_num)
theorem B2066741 : Blo 916578 2066741 := bbase (se 5 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 2066741 = 193757) (by norm_num)
theorem B1378613 : Blo 916578 1378613 := bbase (se 5 (by rfl) ⟨64622, by rfl⟩ : syracuseStep 1378613 = 129245) (by norm_num)
theorem B1378637 : Blo 916578 1378637 := bbase (se 3 (by rfl) ⟨258494, by rfl⟩ : syracuseStep 1378637 = 516989) (by norm_num)
theorem B1116509 : Blo 916578 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B1378661 : Blo 916578 1378661 := bbase (se 4 (by rfl) ⟨129249, by rfl⟩ : syracuseStep 1378661 = 258499) (by norm_num)
theorem B2066813 : Blo 916578 2066813 := bbase (se 3 (by rfl) ⟨387527, by rfl⟩ : syracuseStep 2066813 = 775055) (by norm_num)
theorem B1378685 : Blo 916578 1378685 := bbase (se 3 (by rfl) ⟨258503, by rfl⟩ : syracuseStep 1378685 = 517007) (by norm_num)
theorem B1378709 : Blo 916578 1378709 := bbase (se 6 (by rfl) ⟨32313, by rfl⟩ : syracuseStep 1378709 = 64627) (by norm_num)
theorem B6293909 : Blo 916578 6293909 := bbase (se 6 (by rfl) ⟨147513, by rfl⟩ : syracuseStep 6293909 = 295027) (by norm_num)
theorem B1378733 : Blo 916578 1378733 := bbase (se 3 (by rfl) ⟨258512, by rfl⟩ : syracuseStep 1378733 = 517025) (by norm_num)
theorem B2329013 : Blo 916578 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B2066885 : Blo 916578 2066885 := bbase (se 4 (by rfl) ⟨193770, by rfl⟩ : syracuseStep 2066885 = 387541) (by norm_num)
theorem B1378757 : Blo 916578 1378757 := bbase (se 4 (by rfl) ⟨129258, by rfl⟩ : syracuseStep 1378757 = 258517) (by norm_num)
theorem B1378781 : Blo 916578 1378781 := bbase (se 3 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 1378781 = 517043) (by norm_num)
theorem B1378805 : Blo 916578 1378805 := bbase (se 5 (by rfl) ⟨64631, by rfl⟩ : syracuseStep 1378805 = 129263) (by norm_num)
theorem B2066957 : Blo 916578 2066957 := bbase (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) (by norm_num)
theorem B1378829 : Blo 916578 1378829 := bbase (se 3 (by rfl) ⟨258530, by rfl⟩ : syracuseStep 1378829 = 517061) (by norm_num)
theorem B1378853 : Blo 916578 1378853 := bbase (se 4 (by rfl) ⟨129267, by rfl⟩ : syracuseStep 1378853 = 258535) (by norm_num)
theorem B1378877 : Blo 916578 1378877 := bbase (se 3 (by rfl) ⟨258539, by rfl⟩ : syracuseStep 1378877 = 517079) (by norm_num)
theorem B3312197 : Blo 916578 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B2067029 : Blo 916578 2067029 := bbase (se 8 (by rfl) ⟨12111, by rfl⟩ : syracuseStep 2067029 = 24223) (by norm_num)
theorem B1378901 : Blo 916578 1378901 := bbase (se 8 (by rfl) ⟨8079, by rfl⟩ : syracuseStep 1378901 = 16159) (by norm_num)
theorem B4655717 : Blo 916578 4655717 := bbase (se 4 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 4655717 = 872947) (by norm_num)
theorem B1378925 : Blo 916578 1378925 := bbase (se 3 (by rfl) ⟨258548, by rfl⟩ : syracuseStep 1378925 = 517097) (by norm_num)
theorem B1378949 : Blo 916578 1378949 := bbase (se 4 (by rfl) ⟨129276, by rfl⟩ : syracuseStep 1378949 = 258553) (by norm_num)
theorem B2067101 : Blo 916578 2067101 := bbase (se 3 (by rfl) ⟨387581, by rfl⟩ : syracuseStep 2067101 = 775163) (by norm_num)
theorem B1378973 : Blo 916578 1378973 := bbase (se 3 (by rfl) ⟨258557, by rfl⟩ : syracuseStep 1378973 = 517115) (by norm_num)
theorem B1378997 : Blo 916578 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B1379021 : Blo 916578 1379021 := bbase (se 3 (by rfl) ⟨258566, by rfl⟩ : syracuseStep 1379021 = 517133) (by norm_num)
theorem B2067173 : Blo 916578 2067173 := bbase (se 4 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 2067173 = 387595) (by norm_num)
theorem B1379045 : Blo 916578 1379045 := bbase (se 4 (by rfl) ⟨129285, by rfl⟩ : syracuseStep 1379045 = 258571) (by norm_num)
theorem B1379069 : Blo 916578 1379069 := bbase (se 3 (by rfl) ⟨258575, by rfl⟩ : syracuseStep 1379069 = 517151) (by norm_num)
theorem B2329357 : Blo 916578 2329357 := bbase (se 3 (by rfl) ⟨436754, by rfl⟩ : syracuseStep 2329357 = 873509) (by norm_num)
theorem B1379093 : Blo 916578 1379093 := bbase (se 6 (by rfl) ⟨32322, by rfl⟩ : syracuseStep 1379093 = 64645) (by norm_num)
theorem B2067245 : Blo 916578 2067245 := bbase (se 3 (by rfl) ⟨387608, by rfl⟩ : syracuseStep 2067245 = 775217) (by norm_num)
theorem B1379117 : Blo 916578 1379117 := bbase (se 3 (by rfl) ⟨258584, by rfl⟩ : syracuseStep 1379117 = 517169) (by norm_num)
theorem B1379141 : Blo 916578 1379141 := bbase (se 4 (by rfl) ⟨129294, by rfl⟩ : syracuseStep 1379141 = 258589) (by norm_num)
theorem B1379165 : Blo 916578 1379165 := bbase (se 3 (by rfl) ⟨258593, by rfl⟩ : syracuseStep 1379165 = 517187) (by norm_num)
theorem B2067317 : Blo 916578 2067317 := bbase (se 5 (by rfl) ⟨96905, by rfl⟩ : syracuseStep 2067317 = 193811) (by norm_num)
theorem B1379189 : Blo 916578 1379189 := bbase (se 5 (by rfl) ⟨64649, by rfl⟩ : syracuseStep 1379189 = 129299) (by norm_num)
theorem B2329469 : Blo 916578 2329469 := bbase (se 3 (by rfl) ⟨436775, by rfl⟩ : syracuseStep 2329469 = 873551) (by norm_num)
theorem B1379213 : Blo 916578 1379213 := bbase (se 3 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 1379213 = 517205) (by norm_num)
theorem B1379237 : Blo 916578 1379237 := bbase (se 4 (by rfl) ⟨129303, by rfl⟩ : syracuseStep 1379237 = 258607) (by norm_num)
theorem B2067389 : Blo 916578 2067389 := bbase (se 3 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 2067389 = 775271) (by norm_num)
theorem B1379261 : Blo 916578 1379261 := bbase (se 3 (by rfl) ⟨258611, by rfl⟩ : syracuseStep 1379261 = 517223) (by norm_num)
theorem B1379285 : Blo 916578 1379285 := bbase (se 7 (by rfl) ⟨16163, by rfl⟩ : syracuseStep 1379285 = 32327) (by norm_num)
theorem B1379309 : Blo 916578 1379309 := bbase (se 3 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 1379309 = 517241) (by norm_num)
theorem B2067461 : Blo 916578 2067461 := bbase (se 4 (by rfl) ⟨193824, by rfl⟩ : syracuseStep 2067461 = 387649) (by norm_num)
theorem B1379333 : Blo 916578 1379333 := bbase (se 4 (by rfl) ⟨129312, by rfl⟩ : syracuseStep 1379333 = 258625) (by norm_num)
theorem B1379357 : Blo 916578 1379357 := bbase (se 3 (by rfl) ⟨258629, by rfl⟩ : syracuseStep 1379357 = 517259) (by norm_num)
theorem B1379381 : Blo 916578 1379381 := bbase (se 5 (by rfl) ⟨64658, by rfl⟩ : syracuseStep 1379381 = 129317) (by norm_num)
theorem B2329661 : Blo 916578 2329661 := bbase (se 3 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 2329661 = 873623) (by norm_num)
theorem B2067533 : Blo 916578 2067533 := bbase (se 3 (by rfl) ⟨387662, by rfl⟩ : syracuseStep 2067533 = 775325) (by norm_num)
theorem B1379405 : Blo 916578 1379405 := bbase (se 3 (by rfl) ⟨258638, by rfl⟩ : syracuseStep 1379405 = 517277) (by norm_num)
theorem B1379429 : Blo 916578 1379429 := bbase (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) (by norm_num)
theorem B1379453 : Blo 916578 1379453 := bbase (se 3 (by rfl) ⟨258647, by rfl⟩ : syracuseStep 1379453 = 517295) (by norm_num)
theorem B2067605 : Blo 916578 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B1379477 : Blo 916578 1379477 := bbase (se 6 (by rfl) ⟨32331, by rfl⟩ : syracuseStep 1379477 = 64663) (by norm_num)
theorem B1379501 : Blo 916578 1379501 := bbase (se 3 (by rfl) ⟨258656, by rfl⟩ : syracuseStep 1379501 = 517313) (by norm_num)
theorem B1379525 : Blo 916578 1379525 := bbase (se 4 (by rfl) ⟨129330, by rfl⟩ : syracuseStep 1379525 = 258661) (by norm_num)
theorem B2067677 : Blo 916578 2067677 := bbase (se 3 (by rfl) ⟨387689, by rfl⟩ : syracuseStep 2067677 = 775379) (by norm_num)
theorem B1379549 : Blo 916578 1379549 := bbase (se 3 (by rfl) ⟨258665, by rfl⟩ : syracuseStep 1379549 = 517331) (by norm_num)
theorem B1379573 : Blo 916578 1379573 := bbase (se 5 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 1379573 = 129335) (by norm_num)
theorem B1379597 : Blo 916578 1379597 := bbase (se 3 (by rfl) ⟨258674, by rfl⟩ : syracuseStep 1379597 = 517349) (by norm_num)
theorem B4197653 : Blo 916578 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B2067749 : Blo 916578 2067749 := bbase (se 4 (by rfl) ⟨193851, by rfl⟩ : syracuseStep 2067749 = 387703) (by norm_num)
theorem B1379621 : Blo 916578 1379621 := bbase (se 4 (by rfl) ⟨129339, by rfl⟩ : syracuseStep 1379621 = 258679) (by norm_num)
theorem B1379645 : Blo 916578 1379645 := bbase (se 3 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 1379645 = 517367) (by norm_num)
theorem B1379669 : Blo 916578 1379669 := bbase (se 11 (by rfl) ⟨1010, by rfl⟩ : syracuseStep 1379669 = 2021) (by norm_num)
theorem B2067821 : Blo 916578 2067821 := bbase (se 3 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 2067821 = 775433) (by norm_num)
theorem B1379693 : Blo 916578 1379693 := bbase (se 3 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 1379693 = 517385) (by norm_num)
theorem B1379717 : Blo 916578 1379717 := bbase (se 4 (by rfl) ⟨129348, by rfl⟩ : syracuseStep 1379717 = 258697) (by norm_num)
theorem B2330005 : Blo 916578 2330005 := bbase (se 6 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 2330005 = 109219) (by norm_num)
theorem B1379741 : Blo 916578 1379741 := bbase (se 3 (by rfl) ⟨258701, by rfl⟩ : syracuseStep 1379741 = 517403) (by norm_num)
theorem B2067893 : Blo 916578 2067893 := bbase (se 5 (by rfl) ⟨96932, by rfl⟩ : syracuseStep 2067893 = 193865) (by norm_num)
theorem B1379765 : Blo 916578 1379765 := bbase (se 5 (by rfl) ⟨64676, by rfl⟩ : syracuseStep 1379765 = 129353) (by norm_num)
theorem B1379789 : Blo 916578 1379789 := bbase (se 3 (by rfl) ⟨258710, by rfl⟩ : syracuseStep 1379789 = 517421) (by norm_num)
theorem B1379813 : Blo 916578 1379813 := bbase (se 4 (by rfl) ⟨129357, by rfl⟩ : syracuseStep 1379813 = 258715) (by norm_num)
theorem B2067965 : Blo 916578 2067965 := bbase (se 3 (by rfl) ⟨387743, by rfl⟩ : syracuseStep 2067965 = 775487) (by norm_num)
theorem B1379837 : Blo 916578 1379837 := bbase (se 3 (by rfl) ⟨258719, by rfl⟩ : syracuseStep 1379837 = 517439) (by norm_num)
theorem B2330117 : Blo 916578 2330117 := bbase (se 4 (by rfl) ⟨218448, by rfl⟩ : syracuseStep 2330117 = 436897) (by norm_num)
theorem B1379861 : Blo 916578 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B1379885 : Blo 916578 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1674821 : Blo 916578 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B2068037 : Blo 916578 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1379909 : Blo 916578 1379909 := bbase (se 4 (by rfl) ⟨129366, by rfl⟩ : syracuseStep 1379909 = 258733) (by norm_num)
theorem B1379933 : Blo 916578 1379933 := bbase (se 3 (by rfl) ⟨258737, by rfl⟩ : syracuseStep 1379933 = 517475) (by norm_num)
theorem B1379957 : Blo 916578 1379957 := bbase (se 5 (by rfl) ⟨64685, by rfl⟩ : syracuseStep 1379957 = 129371) (by norm_num)
theorem B2068109 : Blo 916578 2068109 := bbase (se 3 (by rfl) ⟨387770, by rfl⟩ : syracuseStep 2068109 = 775541) (by norm_num)
theorem B1379981 : Blo 916578 1379981 := bbase (se 3 (by rfl) ⟨258746, by rfl⟩ : syracuseStep 1379981 = 517493) (by norm_num)
theorem B1380005 : Blo 916578 1380005 := bbase (se 4 (by rfl) ⟨129375, by rfl⟩ : syracuseStep 1380005 = 258751) (by norm_num)
theorem B1380029 : Blo 916578 1380029 := bbase (se 3 (by rfl) ⟨258755, by rfl⟩ : syracuseStep 1380029 = 517511) (by norm_num)
theorem B2068181 : Blo 916578 2068181 := bbase (se 7 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 2068181 = 48473) (by norm_num)
theorem B1380053 : Blo 916578 1380053 := bbase (se 7 (by rfl) ⟨16172, by rfl⟩ : syracuseStep 1380053 = 32345) (by norm_num)
theorem B1380077 : Blo 916578 1380077 := bbase (se 3 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 1380077 = 517529) (by norm_num)
theorem B1740541 : Blo 916578 1740541 := bbase (se 3 (by rfl) ⟨326351, by rfl⟩ : syracuseStep 1740541 = 652703) (by norm_num)
theorem B1380101 : Blo 916578 1380101 := bbase (se 4 (by rfl) ⟨129384, by rfl⟩ : syracuseStep 1380101 = 258769) (by norm_num)
theorem B2068253 : Blo 916578 2068253 := bbase (se 3 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 2068253 = 775595) (by norm_num)
theorem B1380125 : Blo 916578 1380125 := bbase (se 3 (by rfl) ⟨258773, by rfl⟩ : syracuseStep 1380125 = 517547) (by norm_num)
theorem B1380149 : Blo 916578 1380149 := bbase (se 5 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 1380149 = 129389) (by norm_num)
theorem B1380173 : Blo 916578 1380173 := bbase (se 3 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 1380173 = 517565) (by norm_num)
theorem B25431893 : Blo 916578 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B2068325 : Blo 916578 2068325 := bbase (se 4 (by rfl) ⟨193905, by rfl⟩ : syracuseStep 2068325 = 387811) (by norm_num)
theorem B1380197 : Blo 916578 1380197 := bbase (se 4 (by rfl) ⟨129393, by rfl⟩ : syracuseStep 1380197 = 258787) (by norm_num)
theorem B4657013 : Blo 916578 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B1380221 : Blo 916578 1380221 := bbase (se 3 (by rfl) ⟨258791, by rfl⟩ : syracuseStep 1380221 = 517583) (by norm_num)
theorem B1740685 : Blo 916578 1740685 := bbase (se 3 (by rfl) ⟨326378, by rfl⟩ : syracuseStep 1740685 = 652757) (by norm_num)
theorem B1380245 : Blo 916578 1380245 := bbase (se 6 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 1380245 = 64699) (by norm_num)
theorem B2068397 : Blo 916578 2068397 := bbase (se 3 (by rfl) ⟨387824, by rfl⟩ : syracuseStep 2068397 = 775649) (by norm_num)
theorem B1380269 : Blo 916578 1380269 := bbase (se 3 (by rfl) ⟨258800, by rfl⟩ : syracuseStep 1380269 = 517601) (by norm_num)
theorem B1380293 : Blo 916578 1380293 := bbase (se 4 (by rfl) ⟨129402, by rfl⟩ : syracuseStep 1380293 = 258805) (by norm_num)
theorem B1380317 : Blo 916578 1380317 := bbase (se 3 (by rfl) ⟨258809, by rfl⟩ : syracuseStep 1380317 = 517619) (by norm_num)
theorem B2068469 : Blo 916578 2068469 := bbase (se 5 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 2068469 = 193919) (by norm_num)
theorem B1380341 : Blo 916578 1380341 := bbase (se 5 (by rfl) ⟨64703, by rfl⟩ : syracuseStep 1380341 = 129407) (by norm_num)
theorem B1380365 : Blo 916578 1380365 := bbase (se 3 (by rfl) ⟨258818, by rfl⟩ : syracuseStep 1380365 = 517637) (by norm_num)
theorem B1380389 : Blo 916578 1380389 := bbase (se 4 (by rfl) ⟨129411, by rfl⟩ : syracuseStep 1380389 = 258823) (by norm_num)
theorem B1740845 : Blo 916578 1740845 := bbase (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) (by norm_num)
theorem B2068541 : Blo 916578 2068541 := bbase (se 3 (by rfl) ⟨387851, by rfl⟩ : syracuseStep 2068541 = 775703) (by norm_num)
theorem B1380413 : Blo 916578 1380413 := bbase (se 3 (by rfl) ⟨258827, by rfl⟩ : syracuseStep 1380413 = 517655) (by norm_num)
theorem B1380437 : Blo 916578 1380437 := bbase (se 8 (by rfl) ⟨8088, by rfl⟩ : syracuseStep 1380437 = 16177) (by norm_num)
theorem B1380461 : Blo 916578 1380461 := bbase (se 3 (by rfl) ⟨258836, by rfl⟩ : syracuseStep 1380461 = 517673) (by norm_num)
theorem B3313781 : Blo 916578 3313781 := bbase (se 5 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 3313781 = 310667) (by norm_num)
theorem B2068613 : Blo 916578 2068613 := bbase (se 4 (by rfl) ⟨193932, by rfl⟩ : syracuseStep 2068613 = 387865) (by norm_num)
theorem B1380485 : Blo 916578 1380485 := bbase (se 4 (by rfl) ⟨129420, by rfl⟩ : syracuseStep 1380485 = 258841) (by norm_num)
theorem B1380509 : Blo 916578 1380509 := bbase (se 3 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 1380509 = 517691) (by norm_num)
theorem B1380533 : Blo 916578 1380533 := bbase (se 5 (by rfl) ⟨64712, by rfl⟩ : syracuseStep 1380533 = 129425) (by norm_num)
theorem B1740989 : Blo 916578 1740989 := bbase (se 3 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 1740989 = 652871) (by norm_num)
theorem B2068685 : Blo 916578 2068685 := bbase (se 3 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 2068685 = 775757) (by norm_num)
theorem B1380557 : Blo 916578 1380557 := bbase (se 3 (by rfl) ⟨258854, by rfl⟩ : syracuseStep 1380557 = 517709) (by norm_num)
theorem B1380581 : Blo 916578 1380581 := bbase (se 4 (by rfl) ⟨129429, by rfl⟩ : syracuseStep 1380581 = 258859) (by norm_num)
theorem B1380605 : Blo 916578 1380605 := bbase (se 3 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 1380605 = 517727) (by norm_num)
theorem B2068757 : Blo 916578 2068757 := bbase (se 6 (by rfl) ⟨48486, by rfl⟩ : syracuseStep 2068757 = 96973) (by norm_num)
theorem B1380629 : Blo 916578 1380629 := bbase (se 6 (by rfl) ⟨32358, by rfl⟩ : syracuseStep 1380629 = 64717) (by norm_num)
theorem B1380653 : Blo 916578 1380653 := bbase (se 3 (by rfl) ⟨258872, by rfl⟩ : syracuseStep 1380653 = 517745) (by norm_num)
theorem B1380677 : Blo 916578 1380677 := bbase (se 4 (by rfl) ⟨129438, by rfl⟩ : syracuseStep 1380677 = 258877) (by norm_num)
theorem B2068829 : Blo 916578 2068829 := bbase (se 3 (by rfl) ⟨387905, by rfl⟩ : syracuseStep 2068829 = 775811) (by norm_num)
theorem B1380701 : Blo 916578 1380701 := bbase (se 3 (by rfl) ⟨258881, by rfl⟩ : syracuseStep 1380701 = 517763) (by norm_num)
theorem B1380725 : Blo 916578 1380725 := bbase (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) (by norm_num)
theorem B1380749 : Blo 916578 1380749 := bbase (se 3 (by rfl) ⟨258890, by rfl⟩ : syracuseStep 1380749 = 517781) (by norm_num)
theorem B2068901 : Blo 916578 2068901 := bbase (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) (by norm_num)
theorem B1380773 : Blo 916578 1380773 := bbase (se 4 (by rfl) ⟨129447, by rfl⟩ : syracuseStep 1380773 = 258895) (by norm_num)
theorem B3969461 : Blo 916578 3969461 := bbase (se 5 (by rfl) ⟨186068, by rfl⟩ : syracuseStep 3969461 = 372137) (by norm_num)
theorem B1380797 : Blo 916578 1380797 := bbase (se 3 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 1380797 = 517799) (by norm_num)
theorem B1380821 : Blo 916578 1380821 := bbase (se 7 (by rfl) ⟨16181, by rfl⟩ : syracuseStep 1380821 = 32363) (by norm_num)
theorem B1741277 : Blo 916578 1741277 := bbase (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) (by norm_num)
theorem B2068973 : Blo 916578 2068973 := bbase (se 3 (by rfl) ⟨387932, by rfl⟩ : syracuseStep 2068973 = 775865) (by norm_num)
theorem B1380845 : Blo 916578 1380845 := bbase (se 3 (by rfl) ⟨258908, by rfl⟩ : syracuseStep 1380845 = 517817) (by norm_num)
theorem B2069045 : Blo 916578 2069045 := bbase (se 5 (by rfl) ⟨96986, by rfl⟩ : syracuseStep 2069045 = 193973) (by norm_num)
theorem B7967317 : Blo 916578 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B1741429 : Blo 916578 1741429 := bbase (se 5 (by rfl) ⟨81629, by rfl⟩ : syracuseStep 1741429 = 163259) (by norm_num)
theorem B2069117 : Blo 916578 2069117 := bbase (se 3 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 2069117 = 775919) (by norm_num)
theorem B2069189 : Blo 916578 2069189 := bbase (se 4 (by rfl) ⟨193986, by rfl⟩ : syracuseStep 2069189 = 387973) (by norm_num)
theorem B2069261 : Blo 916578 2069261 := bbase (se 3 (by rfl) ⟨387986, by rfl⟩ : syracuseStep 2069261 = 775973) (by norm_num)
theorem B2069333 : Blo 916578 2069333 := bbase (se 9 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 2069333 = 12125) (by norm_num)
theorem B922501 : Blo 916578 922501 := bbase (se 4 (by rfl) ⟨86484, by rfl⟩ : syracuseStep 922501 = 172969) (by norm_num)
theorem B2069405 : Blo 916578 2069405 := bbase (se 3 (by rfl) ⟨388013, by rfl⟩ : syracuseStep 2069405 = 776027) (by norm_num)
theorem B1741733 : Blo 916578 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B2069477 : Blo 916578 2069477 := bbase (se 4 (by rfl) ⟨194013, by rfl⟩ : syracuseStep 2069477 = 388027) (by norm_num)
theorem B2069549 : Blo 916578 2069549 := bbase (se 3 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 2069549 = 776081) (by norm_num)
theorem B2233405 : Blo 916578 2233405 := bbase (se 3 (by rfl) ⟨418763, by rfl⟩ : syracuseStep 2233405 = 837527) (by norm_num)
theorem B2069621 : Blo 916578 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B4658309 : Blo 916578 4658309 := bbase (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) (by norm_num)
theorem B2069693 : Blo 916578 2069693 := bbase (se 3 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 2069693 = 776135) (by norm_num)
theorem B2069765 : Blo 916578 2069765 := bbase (se 4 (by rfl) ⟨194040, by rfl⟩ : syracuseStep 2069765 = 388081) (by norm_num)
theorem B2069837 : Blo 916578 2069837 := bbase (se 3 (by rfl) ⟨388094, by rfl⟩ : syracuseStep 2069837 = 776189) (by norm_num)
theorem B2069909 : Blo 916578 2069909 := bbase (se 6 (by rfl) ⟨48513, by rfl⟩ : syracuseStep 2069909 = 97027) (by norm_num)
theorem B2069981 : Blo 916578 2069981 := bbase (se 3 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 2069981 = 776243) (by norm_num)
theorem B2070053 : Blo 916578 2070053 := bbase (se 4 (by rfl) ⟨194067, by rfl⟩ : syracuseStep 2070053 = 388135) (by norm_num)
theorem B2070125 : Blo 916578 2070125 := bbase (se 3 (by rfl) ⟨388148, by rfl⟩ : syracuseStep 2070125 = 776297) (by norm_num)
theorem B1742485 : Blo 916578 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B2070197 : Blo 916578 2070197 := bbase (se 5 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 2070197 = 194081) (by norm_num)
theorem B2070269 : Blo 916578 2070269 := bbase (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) (by norm_num)
theorem B1742629 : Blo 916578 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B2070341 : Blo 916578 2070341 := bbase (se 4 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 2070341 = 388189) (by norm_num)
theorem B2070413 : Blo 916578 2070413 := bbase (se 3 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 2070413 = 776405) (by norm_num)
theorem B1742789 : Blo 916578 1742789 := bbase (se 4 (by rfl) ⟨163386, by rfl⟩ : syracuseStep 1742789 = 326773) (by norm_num)
theorem B2070485 : Blo 916578 2070485 := bbase (se 7 (by rfl) ⟨24263, by rfl⟩ : syracuseStep 2070485 = 48527) (by norm_num)
theorem B2070557 : Blo 916578 2070557 := bbase (se 3 (by rfl) ⟨388229, by rfl⟩ : syracuseStep 2070557 = 776459) (by norm_num)
theorem B1742933 : Blo 916578 1742933 := bbase (se 8 (by rfl) ⟨10212, by rfl⟩ : syracuseStep 1742933 = 20425) (by norm_num)
theorem B2070629 : Blo 916578 2070629 := bbase (se 4 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 2070629 = 388243) (by norm_num)
theorem B2070701 : Blo 916578 2070701 := bbase (se 3 (by rfl) ⟨388256, by rfl⟩ : syracuseStep 2070701 = 776513) (by norm_num)
theorem B2070773 : Blo 916578 2070773 := bbase (se 5 (by rfl) ⟨97067, by rfl⟩ : syracuseStep 2070773 = 194135) (by norm_num)
theorem B2070845 : Blo 916578 2070845 := bbase (se 3 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 2070845 = 776567) (by norm_num)
theorem B1743221 : Blo 916578 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B2070917 : Blo 916578 2070917 := bbase (se 4 (by rfl) ⟨194148, by rfl⟩ : syracuseStep 2070917 = 388297) (by norm_num)
theorem B4659605 : Blo 916578 4659605 := bbase (se 6 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 4659605 = 218419) (by norm_num)
theorem B2070989 : Blo 916578 2070989 := bbase (se 3 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 2070989 = 776621) (by norm_num)
theorem B1743373 : Blo 916578 1743373 := bbase (se 3 (by rfl) ⟨326882, by rfl⟩ : syracuseStep 1743373 = 653765) (by norm_num)
theorem B2071061 : Blo 916578 2071061 := bbase (se 6 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 2071061 = 97081) (by norm_num)
theorem B1546789 : Blo 916578 1546789 := bbase (se 4 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 1546789 = 290023) (by norm_num)
theorem B2071133 : Blo 916578 2071133 := bbase (se 3 (by rfl) ⟨388337, by rfl⟩ : syracuseStep 2071133 = 776675) (by norm_num)
theorem B1546877 : Blo 916578 1546877 := bbase (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) (by norm_num)
theorem B2071205 : Blo 916578 2071205 := bbase (se 4 (by rfl) ⟨194175, by rfl⟩ : syracuseStep 2071205 = 388351) (by norm_num)
theorem B2071277 : Blo 916578 2071277 := bbase (se 3 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 2071277 = 776729) (by norm_num)
theorem B1547005 : Blo 916578 1547005 := bbase (se 3 (by rfl) ⟨290063, by rfl⟩ : syracuseStep 1547005 = 580127) (by norm_num)
theorem B1743677 : Blo 916578 1743677 := bbase (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) (by norm_num)
theorem B1547093 : Blo 916578 1547093 := bbase (se 9 (by rfl) ⟨4532, by rfl⟩ : syracuseStep 1547093 = 9065) (by norm_num)
theorem B2235269 : Blo 916578 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1547221 : Blo 916578 1547221 := bbase (se 7 (by rfl) ⟨18131, by rfl⟩ : syracuseStep 1547221 = 36263) (by norm_num)
theorem B1547309 : Blo 916578 1547309 := bbase (se 3 (by rfl) ⟨290120, by rfl⟩ : syracuseStep 1547309 = 580241) (by norm_num)
theorem B1547437 : Blo 916578 1547437 := bbase (se 3 (by rfl) ⟨290144, by rfl⟩ : syracuseStep 1547437 = 580289) (by norm_num)
theorem B2202805 : Blo 916578 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1547525 : Blo 916578 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B3480853 : Blo 916578 3480853 := bbase (se 6 (by rfl) ⟨81582, by rfl⟩ : syracuseStep 3480853 = 163165) (by norm_num)
theorem B1416509 : Blo 916578 1416509 := bbase (se 3 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 1416509 = 531191) (by norm_num)
theorem B1547653 : Blo 916578 1547653 := bbase (se 4 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 1547653 = 290185) (by norm_num)
theorem B3317125 : Blo 916578 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B6987221 : Blo 916578 6987221 := bbase (se 7 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 6987221 = 163763) (by norm_num)
theorem B1547741 : Blo 916578 1547741 := bbase (se 3 (by rfl) ⟨290201, by rfl⟩ : syracuseStep 1547741 = 580403) (by norm_num)
theorem B3317269 : Blo 916578 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B1744429 : Blo 916578 1744429 := bbase (se 3 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 1744429 = 654161) (by norm_num)
theorem B3481157 : Blo 916578 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B1547869 : Blo 916578 1547869 := bbase (se 3 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 1547869 = 580451) (by norm_num)
theorem B1547957 : Blo 916578 1547957 := bbase (se 5 (by rfl) ⟨72560, by rfl⟩ : syracuseStep 1547957 = 145121) (by norm_num)
theorem B1744573 : Blo 916578 1744573 := bbase (se 3 (by rfl) ⟨327107, by rfl⟩ : syracuseStep 1744573 = 654215) (by norm_num)
theorem B1548085 : Blo 916578 1548085 := bbase (se 5 (by rfl) ⟨72566, by rfl⟩ : syracuseStep 1548085 = 145133) (by norm_num)
theorem B1744733 : Blo 916578 1744733 := bbase (se 3 (by rfl) ⟨327137, by rfl⟩ : syracuseStep 1744733 = 654275) (by norm_num)
theorem B2203517 : Blo 916578 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B1548173 : Blo 916578 1548173 := bbase (se 3 (by rfl) ⟨290282, by rfl⟩ : syracuseStep 1548173 = 580565) (by norm_num)
theorem B1744877 : Blo 916578 1744877 := bbase (se 3 (by rfl) ⟨327164, by rfl⟩ : syracuseStep 1744877 = 654329) (by norm_num)
theorem B1548301 : Blo 916578 1548301 := bbase (se 3 (by rfl) ⟨290306, by rfl⟩ : syracuseStep 1548301 = 580613) (by norm_num)
theorem B1548389 : Blo 916578 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B1548517 : Blo 916578 1548517 := bbase (se 4 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 1548517 = 290347) (by norm_num)
theorem B1745165 : Blo 916578 1745165 := bbase (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) (by norm_num)
theorem B1548605 : Blo 916578 1548605 := bbase (se 3 (by rfl) ⟨290363, by rfl⟩ : syracuseStep 1548605 = 580727) (by norm_num)
theorem B1745317 : Blo 916578 1745317 := bbase (se 4 (by rfl) ⟨163623, by rfl⟩ : syracuseStep 1745317 = 327247) (by norm_num)
theorem B1548733 : Blo 916578 1548733 := bbase (se 3 (by rfl) ⟨290387, by rfl⟩ : syracuseStep 1548733 = 580775) (by norm_num)
theorem B1548821 : Blo 916578 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B2204189 : Blo 916578 2204189 := bbase (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) (by norm_num)
theorem B1548949 : Blo 916578 1548949 := bbase (se 6 (by rfl) ⟨36303, by rfl⟩ : syracuseStep 1548949 = 72607) (by norm_num)
theorem B1745621 : Blo 916578 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B1549037 : Blo 916578 1549037 := bbase (se 3 (by rfl) ⟨290444, by rfl⟩ : syracuseStep 1549037 = 580889) (by norm_num)
theorem B2794277 : Blo 916578 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B53715797 : Blo 916578 53715797 := bbase (se 9 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 53715797 = 314741) (by norm_num)
theorem B1549165 : Blo 916578 1549165 := bbase (se 3 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 1549165 = 580937) (by norm_num)
theorem B1549253 : Blo 916578 1549253 := bbase (se 4 (by rfl) ⟨145242, by rfl⟩ : syracuseStep 1549253 = 290485) (by norm_num)
theorem B992245 : Blo 916578 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B1549381 : Blo 916578 1549381 := bbase (se 4 (by rfl) ⟨145254, by rfl⟩ : syracuseStep 1549381 = 290509) (by norm_num)
theorem B1549469 : Blo 916578 1549469 := bbase (se 3 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 1549469 = 581051) (by norm_num)
theorem B1549597 : Blo 916578 1549597 := bbase (se 3 (by rfl) ⟨290549, by rfl⟩ : syracuseStep 1549597 = 581099) (by norm_num)
theorem B1549685 : Blo 916578 1549685 := bbase (se 5 (by rfl) ⟨72641, by rfl⟩ : syracuseStep 1549685 = 145283) (by norm_num)
theorem B1746373 : Blo 916578 1746373 := bbase (se 4 (by rfl) ⟨163722, by rfl⟩ : syracuseStep 1746373 = 327445) (by norm_num)
theorem B1549813 : Blo 916578 1549813 := bbase (se 5 (by rfl) ⟨72647, by rfl⟩ : syracuseStep 1549813 = 145295) (by norm_num)
theorem B1549901 : Blo 916578 1549901 := bbase (se 3 (by rfl) ⟨290606, by rfl⟩ : syracuseStep 1549901 = 581213) (by norm_num)
theorem B1746517 : Blo 916578 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B3483269 : Blo 916578 3483269 := bbase (se 4 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 3483269 = 653113) (by norm_num)
theorem B1550029 : Blo 916578 1550029 := bbase (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) (by norm_num)
theorem B1746677 : Blo 916578 1746677 := bbase (se 5 (by rfl) ⟨81875, by rfl⟩ : syracuseStep 1746677 = 163751) (by norm_num)
theorem B1550117 : Blo 916578 1550117 := bbase (se 4 (by rfl) ⟨145323, by rfl⟩ : syracuseStep 1550117 = 290647) (by norm_num)
theorem B1812325 : Blo 916578 1812325 := bbase (se 4 (by rfl) ⟨169905, by rfl⟩ : syracuseStep 1812325 = 339811) (by norm_num)
theorem B1746821 : Blo 916578 1746821 := bbase (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) (by norm_num)
theorem B3483557 : Blo 916578 3483557 := bbase (se 4 (by rfl) ⟨326583, by rfl⟩ : syracuseStep 3483557 = 653167) (by norm_num)
theorem B1550245 : Blo 916578 1550245 := bbase (se 4 (by rfl) ⟨145335, by rfl⟩ : syracuseStep 1550245 = 290671) (by norm_num)
theorem B1550333 : Blo 916578 1550333 := bbase (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) (by norm_num)
theorem B1550461 : Blo 916578 1550461 := bbase (se 3 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 1550461 = 581423) (by norm_num)
theorem B1747109 : Blo 916578 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B1550549 : Blo 916578 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B2205949 : Blo 916578 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B1747261 : Blo 916578 1747261 := bbase (se 3 (by rfl) ⟨327611, by rfl⟩ : syracuseStep 1747261 = 655223) (by norm_num)
theorem B1550677 : Blo 916578 1550677 := bbase (se 10 (by rfl) ⟨2271, by rfl⟩ : syracuseStep 1550677 = 4543) (by norm_num)
theorem B993629 : Blo 916578 993629 := bbase (se 3 (by rfl) ⟨186305, by rfl⟩ : syracuseStep 993629 = 372611) (by norm_num)
theorem B1550765 : Blo 916578 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B8825365 : Blo 916578 8825365 := bbase (se 6 (by rfl) ⟨206844, by rfl⟩ : syracuseStep 8825365 = 413689) (by norm_num)
theorem B1550893 : Blo 916578 1550893 := bbase (se 3 (by rfl) ⟨290792, by rfl⟩ : syracuseStep 1550893 = 581585) (by norm_num)
theorem B1747565 : Blo 916578 1747565 := bbase (se 3 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 1747565 = 655337) (by norm_num)
theorem B1550981 : Blo 916578 1550981 := bbase (se 4 (by rfl) ⟨145404, by rfl⟩ : syracuseStep 1550981 = 290809) (by norm_num)
theorem B1551109 : Blo 916578 1551109 := bbase (se 4 (by rfl) ⟨145416, by rfl⟩ : syracuseStep 1551109 = 290833) (by norm_num)
theorem B1551197 : Blo 916578 1551197 := bbase (se 3 (by rfl) ⟨290849, by rfl⟩ : syracuseStep 1551197 = 581699) (by norm_num)
theorem B2206565 : Blo 916578 2206565 := bbase (se 4 (by rfl) ⟨206865, by rfl⟩ : syracuseStep 2206565 = 413731) (by norm_num)
theorem B1551325 : Blo 916578 1551325 := bbase (se 3 (by rfl) ⟨290873, by rfl⟩ : syracuseStep 1551325 = 581747) (by norm_num)
theorem B1551413 : Blo 916578 1551413 := bbase (se 5 (by rfl) ⟨72722, by rfl⟩ : syracuseStep 1551413 = 145445) (by norm_num)
theorem B3484741 : Blo 916578 3484741 := bbase (se 4 (by rfl) ⟨326694, by rfl⟩ : syracuseStep 3484741 = 653389) (by norm_num)
theorem B1551541 : Blo 916578 1551541 := bbase (se 5 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 1551541 = 145457) (by norm_num)
theorem B1551629 : Blo 916578 1551629 := bbase (se 3 (by rfl) ⟨290930, by rfl⟩ : syracuseStep 1551629 = 581861) (by norm_num)
theorem B3485045 : Blo 916578 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B1551757 : Blo 916578 1551757 := bbase (se 3 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 1551757 = 581909) (by norm_num)
theorem B5385685 : Blo 916578 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B1551845 : Blo 916578 1551845 := bbase (se 4 (by rfl) ⟨145485, by rfl⟩ : syracuseStep 1551845 = 290971) (by norm_num)
theorem B2207333 : Blo 916578 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B1551973 : Blo 916578 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B2207341 : Blo 916578 2207341 := bbase (se 3 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 2207341 = 827753) (by norm_num)
theorem B8171189 : Blo 916578 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B1552061 : Blo 916578 1552061 := bbase (se 3 (by rfl) ⟨291011, by rfl⟩ : syracuseStep 1552061 = 582023) (by norm_num)
theorem B1552189 : Blo 916578 1552189 := bbase (se 3 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 1552189 = 582071) (by norm_num)
theorem B1552277 : Blo 916578 1552277 := bbase (se 6 (by rfl) ⟨36381, by rfl⟩ : syracuseStep 1552277 = 72763) (by norm_num)
theorem B1552405 : Blo 916578 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B1552493 : Blo 916578 1552493 := bbase (se 3 (by rfl) ⟨291092, by rfl⟩ : syracuseStep 1552493 = 582185) (by norm_num)
theorem B1552621 : Blo 916578 1552621 := bbase (se 3 (by rfl) ⟨291116, by rfl⟩ : syracuseStep 1552621 = 582233) (by norm_num)
theorem B1552709 : Blo 916578 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B2208149 : Blo 916578 2208149 := bbase (se 6 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 2208149 = 103507) (by norm_num)
theorem B13250965 : Blo 916578 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B1552837 : Blo 916578 1552837 := bbase (se 4 (by rfl) ⟨145578, by rfl⟩ : syracuseStep 1552837 = 291157) (by norm_num)
theorem B2241037 : Blo 916578 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1552925 : Blo 916578 1552925 := bbase (se 3 (by rfl) ⟨291173, by rfl⟩ : syracuseStep 1552925 = 582347) (by norm_num)
theorem B1553053 : Blo 916578 1553053 := bbase (se 3 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 1553053 = 582395) (by norm_num)
theorem B930541 : Blo 916578 930541 := bbase (se 3 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 930541 = 348953) (by norm_num)
theorem B996085 : Blo 916578 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B1553141 : Blo 916578 1553141 := bbase (se 5 (by rfl) ⟨72803, by rfl⟩ : syracuseStep 1553141 = 145607) (by norm_num)
theorem B1553269 : Blo 916578 1553269 := bbase (se 5 (by rfl) ⟨72809, by rfl⟩ : syracuseStep 1553269 = 145619) (by norm_num)
theorem B1160077 : Blo 916578 1160077 := bbase (se 3 (by rfl) ⟨217514, by rfl⟩ : syracuseStep 1160077 = 435029) (by norm_num)
theorem B1553357 : Blo 916578 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B1160173 : Blo 916578 1160173 := bbase (se 3 (by rfl) ⟨217532, by rfl⟩ : syracuseStep 1160173 = 435065) (by norm_num)
theorem B996401 : Blo 916578 996401 := bbase (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) (by norm_num)
theorem B3093605 : Blo 916578 3093605 := bbase (se 4 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 3093605 = 580051) (by norm_num)
theorem B1160345 : Blo 916578 1160345 := bbase (se 2 (by rfl) ⟨435129, by rfl⟩ : syracuseStep 1160345 = 870259) (by norm_num)
theorem B1160401 : Blo 916578 1160401 := bbase (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) (by norm_num)
theorem B1914149 : Blo 916578 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1160497 : Blo 916578 1160497 := bbase (se 2 (by rfl) ⟨435186, by rfl⟩ : syracuseStep 1160497 = 870373) (by norm_num)
theorem B3487157 : Blo 916578 3487157 := bbase (se 5 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 3487157 = 326921) (by norm_num)
theorem B1160669 : Blo 916578 1160669 := bbase (se 3 (by rfl) ⟨217625, by rfl⟩ : syracuseStep 1160669 = 435251) (by norm_num)
theorem B3094037 : Blo 916578 3094037 := bbase (se 6 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 3094037 = 145033) (by norm_num)
theorem B1160725 : Blo 916578 1160725 := bbase (se 6 (by rfl) ⟨27204, by rfl⟩ : syracuseStep 1160725 = 54409) (by norm_num)
theorem B931385 : Blo 916578 931385 := bbase (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) (by norm_num)
theorem B1160821 : Blo 916578 1160821 := bbase (se 5 (by rfl) ⟨54413, by rfl⟩ : syracuseStep 1160821 = 108827) (by norm_num)
theorem B3487445 : Blo 916578 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B1652501 : Blo 916578 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1160993 : Blo 916578 1160993 := bbase (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) (by norm_num)
theorem B1161049 : Blo 916578 1161049 := bbase (se 2 (by rfl) ⟨435393, by rfl⟩ : syracuseStep 1161049 = 870787) (by norm_num)
theorem B1161145 : Blo 916578 1161145 := bbase (se 2 (by rfl) ⟨435429, by rfl⟩ : syracuseStep 1161145 = 870859) (by norm_num)
theorem B3094469 : Blo 916578 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B931933 : Blo 916578 931933 := bbase (se 3 (by rfl) ⟨174737, by rfl⟩ : syracuseStep 931933 = 349475) (by norm_num)
theorem B1161317 : Blo 916578 1161317 := bbase (se 4 (by rfl) ⟨108873, by rfl⟩ : syracuseStep 1161317 = 217747) (by norm_num)
theorem B1161373 : Blo 916578 1161373 := bbase (se 3 (by rfl) ⟨217757, by rfl⟩ : syracuseStep 1161373 = 435515) (by norm_num)
theorem B1161469 : Blo 916578 1161469 := bbase (se 3 (by rfl) ⟨217775, by rfl⟩ : syracuseStep 1161469 = 435551) (by norm_num)
theorem B1554733 : Blo 916578 1554733 := bbase (se 3 (by rfl) ⟨291512, by rfl⟩ : syracuseStep 1554733 = 583025) (by norm_num)
theorem B3094901 : Blo 916578 3094901 := bbase (se 5 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 3094901 = 290147) (by norm_num)
theorem B1161641 : Blo 916578 1161641 := bbase (se 2 (by rfl) ⟨435615, by rfl⟩ : syracuseStep 1161641 = 871231) (by norm_num)
theorem B1161697 : Blo 916578 1161697 := bbase (se 2 (by rfl) ⟨435636, by rfl⟩ : syracuseStep 1161697 = 871273) (by norm_num)
theorem B1161793 : Blo 916578 1161793 := bbase (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) (by norm_num)
theorem B1161965 : Blo 916578 1161965 := bbase (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) (by norm_num)
theorem B1325821 : Blo 916578 1325821 := bbase (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) (by norm_num)
theorem B3095333 : Blo 916578 3095333 := bbase (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) (by norm_num)
theorem B1162021 : Blo 916578 1162021 := bbase (se 4 (by rfl) ⟨108939, by rfl⟩ : syracuseStep 1162021 = 217879) (by norm_num)
theorem B22362965 : Blo 916578 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B3488629 : Blo 916578 3488629 := bbase (se 5 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 3488629 = 327059) (by norm_num)
theorem B1162117 : Blo 916578 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B1031161 : Blo 916578 1031161 := bbase (se 2 (by rfl) ⟨386685, by rfl⟩ : syracuseStep 1031161 = 773371) (by norm_num)
theorem B1031197 : Blo 916578 1031197 := bbase (se 3 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 1031197 = 386699) (by norm_num)
theorem B1653805 : Blo 916578 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B1162289 : Blo 916578 1162289 := bbase (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) (by norm_num)
theorem B1031233 : Blo 916578 1031233 := bbase (se 2 (by rfl) ⟨386712, by rfl⟩ : syracuseStep 1031233 = 773425) (by norm_num)
theorem B1031269 : Blo 916578 1031269 := bbase (se 4 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 1031269 = 193363) (by norm_num)
theorem B2210917 : Blo 916578 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B1162345 : Blo 916578 1162345 := bbase (se 2 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 1162345 = 871759) (by norm_num)
theorem B1031305 : Blo 916578 1031305 := bbase (se 2 (by rfl) ⟨386739, by rfl⟩ : syracuseStep 1031305 = 773479) (by norm_num)
theorem B3488933 : Blo 916578 3488933 := bbase (se 4 (by rfl) ⟨327087, by rfl⟩ : syracuseStep 3488933 = 654175) (by norm_num)
theorem B1031341 : Blo 916578 1031341 := bbase (se 3 (by rfl) ⟨193376, by rfl⟩ : syracuseStep 1031341 = 386753) (by norm_num)
theorem B1653949 : Blo 916578 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B1162441 : Blo 916578 1162441 := bbase (se 2 (by rfl) ⟨435915, by rfl⟩ : syracuseStep 1162441 = 871831) (by norm_num)
theorem B1031377 : Blo 916578 1031377 := bbase (se 2 (by rfl) ⟨386766, by rfl⟩ : syracuseStep 1031377 = 773533) (by norm_num)
theorem B3095765 : Blo 916578 3095765 := bbase (se 7 (by rfl) ⟨36278, by rfl⟩ : syracuseStep 3095765 = 72557) (by norm_num)
theorem B1031413 : Blo 916578 1031413 := bbase (se 5 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 1031413 = 96695) (by norm_num)
theorem B1031449 : Blo 916578 1031449 := bbase (se 2 (by rfl) ⟨386793, by rfl⟩ : syracuseStep 1031449 = 773587) (by norm_num)
theorem B1031485 : Blo 916578 1031485 := bbase (se 3 (by rfl) ⟨193403, by rfl⟩ : syracuseStep 1031485 = 386807) (by norm_num)
theorem B1031521 : Blo 916578 1031521 := bbase (se 2 (by rfl) ⟨386820, by rfl⟩ : syracuseStep 1031521 = 773641) (by norm_num)
theorem B1162613 : Blo 916578 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B1031557 : Blo 916578 1031557 := bbase (se 4 (by rfl) ⟨96708, by rfl⟩ : syracuseStep 1031557 = 193417) (by norm_num)
theorem B1031593 : Blo 916578 1031593 := bbase (se 2 (by rfl) ⟨386847, by rfl⟩ : syracuseStep 1031593 = 773695) (by norm_num)
theorem B1162669 : Blo 916578 1162669 := bbase (se 3 (by rfl) ⟨218000, by rfl⟩ : syracuseStep 1162669 = 436001) (by norm_num)
theorem B1031629 : Blo 916578 1031629 := bbase (se 3 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 1031629 = 386861) (by norm_num)
theorem B1654253 : Blo 916578 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B1031665 : Blo 916578 1031665 := bbase (se 2 (by rfl) ⟨386874, by rfl⟩ : syracuseStep 1031665 = 773749) (by norm_num)
theorem B1162765 : Blo 916578 1162765 := bbase (se 3 (by rfl) ⟨218018, by rfl⟩ : syracuseStep 1162765 = 436037) (by norm_num)
theorem B1031701 : Blo 916578 1031701 := bbase (se 6 (by rfl) ⟨24180, by rfl⟩ : syracuseStep 1031701 = 48361) (by norm_num)
theorem B7945781 : Blo 916578 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B1031737 : Blo 916578 1031737 := bbase (se 2 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 1031737 = 773803) (by norm_num)
theorem B1031773 : Blo 916578 1031773 := bbase (se 3 (by rfl) ⟨193457, by rfl⟩ : syracuseStep 1031773 = 386915) (by norm_num)
theorem B2211437 : Blo 916578 2211437 := bbase (se 3 (by rfl) ⟨414644, by rfl⟩ : syracuseStep 2211437 = 829289) (by norm_num)
theorem B1031809 : Blo 916578 1031809 := bbase (se 2 (by rfl) ⟨386928, by rfl⟩ : syracuseStep 1031809 = 773857) (by norm_num)
theorem B3096197 : Blo 916578 3096197 := bbase (se 4 (by rfl) ⟨290268, by rfl⟩ : syracuseStep 3096197 = 580537) (by norm_num)
theorem B1031845 : Blo 916578 1031845 := bbase (se 4 (by rfl) ⟨96735, by rfl⟩ : syracuseStep 1031845 = 193471) (by norm_num)
theorem B1162937 : Blo 916578 1162937 := bbase (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) (by norm_num)
theorem B1031881 : Blo 916578 1031881 := bbase (se 2 (by rfl) ⟨386955, by rfl⟩ : syracuseStep 1031881 = 773911) (by norm_num)
theorem B2211533 : Blo 916578 2211533 := bbase (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) (by norm_num)
theorem B1031917 : Blo 916578 1031917 := bbase (se 3 (by rfl) ⟨193484, by rfl⟩ : syracuseStep 1031917 = 386969) (by norm_num)
theorem B1162993 : Blo 916578 1162993 := bbase (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) (by norm_num)
theorem B1031953 : Blo 916578 1031953 := bbase (se 2 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 1031953 = 773965) (by norm_num)
theorem B1031989 : Blo 916578 1031989 := bbase (se 5 (by rfl) ⟨48374, by rfl⟩ : syracuseStep 1031989 = 96749) (by norm_num)
theorem B1163089 : Blo 916578 1163089 := bbase (se 2 (by rfl) ⟨436158, by rfl⟩ : syracuseStep 1163089 = 872317) (by norm_num)
theorem B1032025 : Blo 916578 1032025 := bbase (se 2 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 1032025 = 774019) (by norm_num)
theorem B1032061 : Blo 916578 1032061 := bbase (se 3 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 1032061 = 387023) (by norm_num)
theorem B1032097 : Blo 916578 1032097 := bbase (se 2 (by rfl) ⟨387036, by rfl⟩ : syracuseStep 1032097 = 774073) (by norm_num)
theorem B1032133 : Blo 916578 1032133 := bbase (se 4 (by rfl) ⟨96762, by rfl⟩ : syracuseStep 1032133 = 193525) (by norm_num)
theorem B1032169 : Blo 916578 1032169 := bbase (se 2 (by rfl) ⟨387063, by rfl⟩ : syracuseStep 1032169 = 774127) (by norm_num)
theorem B1163261 : Blo 916578 1163261 := bbase (se 3 (by rfl) ⟨218111, by rfl⟩ : syracuseStep 1163261 = 436223) (by norm_num)
theorem B4407301 : Blo 916578 4407301 := bbase (se 4 (by rfl) ⟨413184, by rfl⟩ : syracuseStep 4407301 = 826369) (by norm_num)
theorem B1032205 : Blo 916578 1032205 := bbase (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) (by norm_num)
theorem B1032241 : Blo 916578 1032241 := bbase (se 2 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 1032241 = 774181) (by norm_num)
theorem B3096629 : Blo 916578 3096629 := bbase (se 5 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 3096629 = 290309) (by norm_num)
theorem B1163317 : Blo 916578 1163317 := bbase (se 5 (by rfl) ⟨54530, by rfl⟩ : syracuseStep 1163317 = 109061) (by norm_num)
theorem B1032277 : Blo 916578 1032277 := bbase (se 8 (by rfl) ⟨6048, by rfl⟩ : syracuseStep 1032277 = 12097) (by norm_num)
theorem B1032313 : Blo 916578 1032313 := bbase (se 2 (by rfl) ⟨387117, by rfl⟩ : syracuseStep 1032313 = 774235) (by norm_num)
theorem B1163413 : Blo 916578 1163413 := bbase (se 6 (by rfl) ⟨27267, by rfl⟩ : syracuseStep 1163413 = 54535) (by norm_num)
theorem B1032349 : Blo 916578 1032349 := bbase (se 3 (by rfl) ⟨193565, by rfl⟩ : syracuseStep 1032349 = 387131) (by norm_num)
theorem B1032385 : Blo 916578 1032385 := bbase (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) (by norm_num)
theorem B1032421 : Blo 916578 1032421 := bbase (se 4 (by rfl) ⟨96789, by rfl⟩ : syracuseStep 1032421 = 193579) (by norm_num)
theorem B1327333 : Blo 916578 1327333 := bbase (se 4 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 1327333 = 248875) (by norm_num)
theorem B1032457 : Blo 916578 1032457 := bbase (se 2 (by rfl) ⟨387171, by rfl⟩ : syracuseStep 1032457 = 774343) (by norm_num)
theorem B1032493 : Blo 916578 1032493 := bbase (se 3 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 1032493 = 387185) (by norm_num)
theorem B1163585 : Blo 916578 1163585 := bbase (se 2 (by rfl) ⟨436344, by rfl⟩ : syracuseStep 1163585 = 872689) (by norm_num)
theorem B1032529 : Blo 916578 1032529 := bbase (se 2 (by rfl) ⟨387198, by rfl⟩ : syracuseStep 1032529 = 774397) (by norm_num)
theorem B3916133 : Blo 916578 3916133 := bbase (se 4 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 3916133 = 734275) (by norm_num)
theorem B1032565 : Blo 916578 1032565 := bbase (se 5 (by rfl) ⟨48401, by rfl⟩ : syracuseStep 1032565 = 96803) (by norm_num)
theorem B1163641 : Blo 916578 1163641 := bbase (se 2 (by rfl) ⟨436365, by rfl⟩ : syracuseStep 1163641 = 872731) (by norm_num)
theorem B1032601 : Blo 916578 1032601 := bbase (se 2 (by rfl) ⟨387225, by rfl⟩ : syracuseStep 1032601 = 774451) (by norm_num)
theorem B1032637 : Blo 916578 1032637 := bbase (se 3 (by rfl) ⟨193619, by rfl⟩ : syracuseStep 1032637 = 387239) (by norm_num)
theorem B1163737 : Blo 916578 1163737 := bbase (se 2 (by rfl) ⟨436401, by rfl⟩ : syracuseStep 1163737 = 872803) (by norm_num)
theorem B1032673 : Blo 916578 1032673 := bbase (se 2 (by rfl) ⟨387252, by rfl⟩ : syracuseStep 1032673 = 774505) (by norm_num)
theorem B3097061 : Blo 916578 3097061 := bbase (se 4 (by rfl) ⟨290349, by rfl⟩ : syracuseStep 3097061 = 580699) (by norm_num)
theorem B1032709 : Blo 916578 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B1032745 : Blo 916578 1032745 := bbase (se 2 (by rfl) ⟨387279, by rfl⟩ : syracuseStep 1032745 = 774559) (by norm_num)
theorem B1032781 : Blo 916578 1032781 := bbase (se 3 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 1032781 = 387293) (by norm_num)
theorem B1032817 : Blo 916578 1032817 := bbase (se 2 (by rfl) ⟨387306, by rfl⟩ : syracuseStep 1032817 = 774613) (by norm_num)
theorem B1163909 : Blo 916578 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B1032853 : Blo 916578 1032853 := bbase (se 6 (by rfl) ⟨24207, by rfl⟩ : syracuseStep 1032853 = 48415) (by norm_num)
theorem B4080293 : Blo 916578 4080293 := bbase (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) (by norm_num)
theorem B6963893 : Blo 916578 6963893 := bbase (se 5 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 6963893 = 652865) (by norm_num)
theorem B1032889 : Blo 916578 1032889 := bbase (se 2 (by rfl) ⟨387333, by rfl⟩ : syracuseStep 1032889 = 774667) (by norm_num)
theorem B1163965 : Blo 916578 1163965 := bbase (se 3 (by rfl) ⟨218243, by rfl⟩ : syracuseStep 1163965 = 436487) (by norm_num)
theorem B1032925 : Blo 916578 1032925 := bbase (se 3 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 1032925 = 387347) (by norm_num)
theorem B1032961 : Blo 916578 1032961 := bbase (se 2 (by rfl) ⟨387360, by rfl⟩ : syracuseStep 1032961 = 774721) (by norm_num)
theorem B1164061 : Blo 916578 1164061 := bbase (se 3 (by rfl) ⟨218261, by rfl⟩ : syracuseStep 1164061 = 436523) (by norm_num)
theorem B1032997 : Blo 916578 1032997 := bbase (se 4 (by rfl) ⟨96843, by rfl⟩ : syracuseStep 1032997 = 193687) (by norm_num)
theorem B1033033 : Blo 916578 1033033 := bbase (se 2 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 1033033 = 774775) (by norm_num)
theorem B1033069 : Blo 916578 1033069 := bbase (se 3 (by rfl) ⟨193700, by rfl⟩ : syracuseStep 1033069 = 387401) (by norm_num)
theorem B1033105 : Blo 916578 1033105 := bbase (se 2 (by rfl) ⟨387414, by rfl⟩ : syracuseStep 1033105 = 774829) (by norm_num)
theorem B3097493 : Blo 916578 3097493 := bbase (se 6 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 3097493 = 145195) (by norm_num)
theorem B1033141 : Blo 916578 1033141 := bbase (se 5 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 1033141 = 96857) (by norm_num)
theorem B1164233 : Blo 916578 1164233 := bbase (se 2 (by rfl) ⟨436587, by rfl⟩ : syracuseStep 1164233 = 873175) (by norm_num)
theorem B1033177 : Blo 916578 1033177 := bbase (se 2 (by rfl) ⟨387441, by rfl⟩ : syracuseStep 1033177 = 774883) (by norm_num)
theorem B1033213 : Blo 916578 1033213 := bbase (se 3 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 1033213 = 387455) (by norm_num)
theorem B1164289 : Blo 916578 1164289 := bbase (se 2 (by rfl) ⟨436608, by rfl⟩ : syracuseStep 1164289 = 873217) (by norm_num)
theorem B1033249 : Blo 916578 1033249 := bbase (se 2 (by rfl) ⟨387468, by rfl⟩ : syracuseStep 1033249 = 774937) (by norm_num)
theorem B1393733 : Blo 916578 1393733 := bbase (se 4 (by rfl) ⟨130662, by rfl⟩ : syracuseStep 1393733 = 261325) (by norm_num)
theorem B1033285 : Blo 916578 1033285 := bbase (se 4 (by rfl) ⟨96870, by rfl⟩ : syracuseStep 1033285 = 193741) (by norm_num)
theorem B1164385 : Blo 916578 1164385 := bbase (se 2 (by rfl) ⟨436644, by rfl⟩ : syracuseStep 1164385 = 873289) (by norm_num)
theorem B1033321 : Blo 916578 1033321 := bbase (se 2 (by rfl) ⟨387495, by rfl⟩ : syracuseStep 1033321 = 774991) (by norm_num)
theorem B1033357 : Blo 916578 1033357 := bbase (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) (by norm_num)
theorem B1033393 : Blo 916578 1033393 := bbase (se 2 (by rfl) ⟨387522, by rfl⟩ : syracuseStep 1033393 = 775045) (by norm_num)
theorem B1393861 : Blo 916578 1393861 := bbase (se 4 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 1393861 = 261349) (by norm_num)
theorem B1033429 : Blo 916578 1033429 := bbase (se 7 (by rfl) ⟨12110, by rfl⟩ : syracuseStep 1033429 = 24221) (by norm_num)
theorem B3491045 : Blo 916578 3491045 := bbase (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) (by norm_num)
theorem B1885421 : Blo 916578 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1033465 : Blo 916578 1033465 := bbase (se 2 (by rfl) ⟨387549, by rfl⟩ : syracuseStep 1033465 = 775099) (by norm_num)
theorem B1164557 : Blo 916578 1164557 := bbase (se 3 (by rfl) ⟨218354, by rfl⟩ : syracuseStep 1164557 = 436709) (by norm_num)
theorem B15680789 : Blo 916578 15680789 := bbase (se 6 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 15680789 = 735037) (by norm_num)
theorem B1033501 : Blo 916578 1033501 := bbase (se 3 (by rfl) ⟨193781, by rfl⟩ : syracuseStep 1033501 = 387563) (by norm_num)
theorem B1033537 : Blo 916578 1033537 := bbase (se 2 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 1033537 = 775153) (by norm_num)
theorem B3097925 : Blo 916578 3097925 := bbase (se 4 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 3097925 = 580861) (by norm_num)
theorem B1164613 : Blo 916578 1164613 := bbase (se 4 (by rfl) ⟨109182, by rfl⟩ : syracuseStep 1164613 = 218365) (by norm_num)
theorem B1033573 : Blo 916578 1033573 := bbase (se 4 (by rfl) ⟨96897, by rfl⟩ : syracuseStep 1033573 = 193795) (by norm_num)
theorem B1033609 : Blo 916578 1033609 := bbase (se 2 (by rfl) ⟨387603, by rfl⟩ : syracuseStep 1033609 = 775207) (by norm_num)
theorem B1164709 : Blo 916578 1164709 := bbase (se 4 (by rfl) ⟨109191, by rfl⟩ : syracuseStep 1164709 = 218383) (by norm_num)
theorem B1033645 : Blo 916578 1033645 := bbase (se 3 (by rfl) ⟨193808, by rfl⟩ : syracuseStep 1033645 = 387617) (by norm_num)
theorem B1033681 : Blo 916578 1033681 := bbase (se 2 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 1033681 = 775261) (by norm_num)
theorem B1033717 : Blo 916578 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B3491333 : Blo 916578 3491333 := bbase (se 4 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 3491333 = 654625) (by norm_num)
theorem B3720725 : Blo 916578 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B1033753 : Blo 916578 1033753 := bbase (se 2 (by rfl) ⟨387657, by rfl⟩ : syracuseStep 1033753 = 775315) (by norm_num)
theorem B1033789 : Blo 916578 1033789 := bbase (se 3 (by rfl) ⟨193835, by rfl⟩ : syracuseStep 1033789 = 387671) (by norm_num)
theorem B1164881 : Blo 916578 1164881 := bbase (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) (by norm_num)
theorem B1033825 : Blo 916578 1033825 := bbase (se 2 (by rfl) ⟨387684, by rfl⟩ : syracuseStep 1033825 = 775369) (by norm_num)
theorem B1033861 : Blo 916578 1033861 := bbase (se 4 (by rfl) ⟨96924, by rfl⟩ : syracuseStep 1033861 = 193849) (by norm_num)
theorem B1164937 : Blo 916578 1164937 := bbase (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) (by norm_num)
theorem B9914005 : Blo 916578 9914005 := bbase (se 6 (by rfl) ⟨232359, by rfl⟩ : syracuseStep 9914005 = 464719) (by norm_num)
theorem B1033897 : Blo 916578 1033897 := bbase (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) (by norm_num)
theorem B1033933 : Blo 916578 1033933 := bbase (se 3 (by rfl) ⟨193862, by rfl⟩ : syracuseStep 1033933 = 387725) (by norm_num)
theorem B1165033 : Blo 916578 1165033 := bbase (se 2 (by rfl) ⟨436887, by rfl⟩ : syracuseStep 1165033 = 873775) (by norm_num)
theorem B1033969 : Blo 916578 1033969 := bbase (se 2 (by rfl) ⟨387738, by rfl⟩ : syracuseStep 1033969 = 775477) (by norm_num)
theorem B3098357 : Blo 916578 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B1034005 : Blo 916578 1034005 := bbase (se 6 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 1034005 = 48469) (by norm_num)
theorem B1034041 : Blo 916578 1034041 := bbase (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) (by norm_num)
theorem B1034077 : Blo 916578 1034077 := bbase (se 3 (by rfl) ⟨193889, by rfl⟩ : syracuseStep 1034077 = 387779) (by norm_num)
theorem B1034113 : Blo 916578 1034113 := bbase (se 2 (by rfl) ⟨387792, by rfl⟩ : syracuseStep 1034113 = 775585) (by norm_num)
theorem B1656733 : Blo 916578 1656733 := bbase (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) (by norm_num)
theorem B1034149 : Blo 916578 1034149 := bbase (se 4 (by rfl) ⟨96951, by rfl⟩ : syracuseStep 1034149 = 193903) (by norm_num)
theorem B1034185 : Blo 916578 1034185 := bbase (se 2 (by rfl) ⟨387819, by rfl⟩ : syracuseStep 1034185 = 775639) (by norm_num)
theorem B1034221 : Blo 916578 1034221 := bbase (se 3 (by rfl) ⟨193916, by rfl⟩ : syracuseStep 1034221 = 387833) (by norm_num)
theorem B1034257 : Blo 916578 1034257 := bbase (se 2 (by rfl) ⟨387846, by rfl⟩ : syracuseStep 1034257 = 775693) (by norm_num)
theorem B4769813 : Blo 916578 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034293 : Blo 916578 1034293 := bbase (se 5 (by rfl) ⟨48482, by rfl⟩ : syracuseStep 1034293 = 96965) (by norm_num)
theorem B3917909 : Blo 916578 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B1034329 : Blo 916578 1034329 := bbase (se 2 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 1034329 = 775747) (by norm_num)
theorem B1034365 : Blo 916578 1034365 := bbase (se 3 (by rfl) ⟨193943, by rfl⟩ : syracuseStep 1034365 = 387887) (by norm_num)
theorem B1034401 : Blo 916578 1034401 := bbase (se 2 (by rfl) ⟨387900, by rfl⟩ : syracuseStep 1034401 = 775801) (by norm_num)
theorem B3098789 : Blo 916578 3098789 := bbase (se 4 (by rfl) ⟨290511, by rfl⟩ : syracuseStep 3098789 = 581023) (by norm_num)
theorem B1034437 : Blo 916578 1034437 := bbase (se 4 (by rfl) ⟨96978, by rfl⟩ : syracuseStep 1034437 = 193957) (by norm_num)
theorem B1034473 : Blo 916578 1034473 := bbase (se 2 (by rfl) ⟨387927, by rfl⟩ : syracuseStep 1034473 = 775855) (by norm_num)
theorem B1034509 : Blo 916578 1034509 := bbase (se 3 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 1034509 = 387941) (by norm_num)
theorem B1034545 : Blo 916578 1034545 := bbase (se 2 (by rfl) ⟨387954, by rfl⟩ : syracuseStep 1034545 = 775909) (by norm_num)
theorem B1395029 : Blo 916578 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B1034581 : Blo 916578 1034581 := bbase (se 10 (by rfl) ⟨1515, by rfl⟩ : syracuseStep 1034581 = 3031) (by norm_num)
theorem B1034617 : Blo 916578 1034617 := bbase (se 2 (by rfl) ⟨387981, by rfl⟩ : syracuseStep 1034617 = 775963) (by norm_num)
theorem B1034653 : Blo 916578 1034653 := bbase (se 3 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 1034653 = 387995) (by norm_num)
theorem B5228981 : Blo 916578 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B1034689 : Blo 916578 1034689 := bbase (se 2 (by rfl) ⟨388008, by rfl⟩ : syracuseStep 1034689 = 776017) (by norm_num)
theorem B5294549 : Blo 916578 5294549 := bbase (se 7 (by rfl) ⟨62045, by rfl⟩ : syracuseStep 5294549 = 124091) (by norm_num)
theorem B1034725 : Blo 916578 1034725 := bbase (se 4 (by rfl) ⟨97005, by rfl⟩ : syracuseStep 1034725 = 194011) (by norm_num)
theorem B6375925 : Blo 916578 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B1034761 : Blo 916578 1034761 := bbase (se 2 (by rfl) ⟨388035, by rfl⟩ : syracuseStep 1034761 = 776071) (by norm_num)
theorem B1034797 : Blo 916578 1034797 := bbase (se 3 (by rfl) ⟨194024, by rfl⟩ : syracuseStep 1034797 = 388049) (by norm_num)
theorem B1034833 : Blo 916578 1034833 := bbase (se 2 (by rfl) ⟨388062, by rfl⟩ : syracuseStep 1034833 = 776125) (by norm_num)
theorem B3099221 : Blo 916578 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B1034869 : Blo 916578 1034869 := bbase (se 5 (by rfl) ⟨48509, by rfl⟩ : syracuseStep 1034869 = 97019) (by norm_num)
theorem B1034905 : Blo 916578 1034905 := bbase (se 2 (by rfl) ⟨388089, by rfl⟩ : syracuseStep 1034905 = 776179) (by norm_num)
theorem B3492517 : Blo 916578 3492517 := bbase (se 4 (by rfl) ⟨327423, by rfl⟩ : syracuseStep 3492517 = 654847) (by norm_num)
theorem B1034941 : Blo 916578 1034941 := bbase (se 3 (by rfl) ⟨194051, by rfl⟩ : syracuseStep 1034941 = 388103) (by norm_num)
theorem B1034977 : Blo 916578 1034977 := bbase (se 2 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 1034977 = 776233) (by norm_num)
theorem B1035013 : Blo 916578 1035013 := bbase (se 4 (by rfl) ⟨97032, by rfl⟩ : syracuseStep 1035013 = 194065) (by norm_num)
theorem B1035049 : Blo 916578 1035049 := bbase (se 2 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 1035049 = 776287) (by norm_num)
theorem B1395533 : Blo 916578 1395533 := bbase (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) (by norm_num)
theorem B1035085 : Blo 916578 1035085 := bbase (se 3 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 1035085 = 388157) (by norm_num)
theorem B1035121 : Blo 916578 1035121 := bbase (se 2 (by rfl) ⟨388170, by rfl⟩ : syracuseStep 1035121 = 776341) (by norm_num)
theorem B1035157 : Blo 916578 1035157 := bbase (se 6 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 1035157 = 48523) (by norm_num)
theorem B1035193 : Blo 916578 1035193 := bbase (se 2 (by rfl) ⟨388197, by rfl⟩ : syracuseStep 1035193 = 776395) (by norm_num)
theorem B3492821 : Blo 916578 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B1657813 : Blo 916578 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B1035229 : Blo 916578 1035229 := bbase (se 3 (by rfl) ⟨194105, by rfl⟩ : syracuseStep 1035229 = 388211) (by norm_num)
theorem B1035265 : Blo 916578 1035265 := bbase (se 2 (by rfl) ⟨388224, by rfl⟩ : syracuseStep 1035265 = 776449) (by norm_num)
theorem B3099653 : Blo 916578 3099653 := bbase (se 4 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 3099653 = 581185) (by norm_num)
theorem B1035301 : Blo 916578 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B1657901 : Blo 916578 1657901 := bbase (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) (by norm_num)
theorem B1035337 : Blo 916578 1035337 := bbase (se 2 (by rfl) ⟨388251, by rfl⟩ : syracuseStep 1035337 = 776503) (by norm_num)
theorem B1657957 : Blo 916578 1657957 := bbase (se 4 (by rfl) ⟨155433, by rfl⟩ : syracuseStep 1657957 = 310867) (by norm_num)
theorem B1035373 : Blo 916578 1035373 := bbase (se 3 (by rfl) ⟨194132, by rfl⟩ : syracuseStep 1035373 = 388265) (by norm_num)
theorem B1035409 : Blo 916578 1035409 := bbase (se 2 (by rfl) ⟨388278, by rfl⟩ : syracuseStep 1035409 = 776557) (by norm_num)
theorem B1035445 : Blo 916578 1035445 := bbase (se 5 (by rfl) ⟨48536, by rfl⟩ : syracuseStep 1035445 = 97073) (by norm_num)
theorem B1035481 : Blo 916578 1035481 := bbase (se 2 (by rfl) ⟨388305, by rfl⟩ : syracuseStep 1035481 = 776611) (by norm_num)
theorem B1035517 : Blo 916578 1035517 := bbase (se 3 (by rfl) ⟨194159, by rfl⟩ : syracuseStep 1035517 = 388319) (by norm_num)
theorem B1035553 : Blo 916578 1035553 := bbase (se 2 (by rfl) ⟨388332, by rfl⟩ : syracuseStep 1035553 = 776665) (by norm_num)
theorem B1035589 : Blo 916578 1035589 := bbase (se 4 (by rfl) ⟨97086, by rfl⟩ : syracuseStep 1035589 = 194173) (by norm_num)
theorem B1035625 : Blo 916578 1035625 := bbase (se 2 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 1035625 = 776719) (by norm_num)
theorem B3100085 : Blo 916578 3100085 := bbase (se 5 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 3100085 = 290633) (by norm_num)
theorem B1396165 : Blo 916578 1396165 := bbase (se 4 (by rfl) ⟨130890, by rfl⟩ : syracuseStep 1396165 = 261781) (by norm_num)
theorem B1396445 : Blo 916578 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B2936549 : Blo 916578 2936549 := bbase (se 4 (by rfl) ⟨275301, by rfl⟩ : syracuseStep 2936549 = 550603) (by norm_num)
theorem B1396493 : Blo 916578 1396493 := bbase (se 3 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 1396493 = 523685) (by norm_num)
theorem B4771685 : Blo 916578 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B3100517 : Blo 916578 3100517 := bbase (se 4 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 3100517 = 581347) (by norm_num)
theorem B1101821 : Blo 916578 1101821 := bbase (se 3 (by rfl) ⟨206591, by rfl⟩ : syracuseStep 1101821 = 413183) (by norm_num)
theorem B3723317 : Blo 916578 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B5886037 : Blo 916578 5886037 := bbase (se 8 (by rfl) ⟨34488, by rfl⟩ : syracuseStep 5886037 = 68977) (by norm_num)
theorem B1101937 : Blo 916578 1101937 := bbase (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) (by norm_num)
theorem B3100949 : Blo 916578 3100949 := bbase (se 6 (by rfl) ⟨72678, by rfl⟩ : syracuseStep 3100949 = 145357) (by norm_num)
theorem B4411685 : Blo 916578 4411685 := bbase (se 4 (by rfl) ⟨413595, by rfl⟩ : syracuseStep 4411685 = 827191) (by norm_num)
theorem B1102133 : Blo 916578 1102133 := bbase (se 5 (by rfl) ⟨51662, by rfl⟩ : syracuseStep 1102133 = 103325) (by norm_num)
theorem B4641461 : Blo 916578 4641461 := bbase (se 5 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 4641461 = 435137) (by norm_num)
theorem B3101381 : Blo 916578 3101381 := bbase (se 4 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 3101381 = 581509) (by norm_num)
theorem B2937637 : Blo 916578 2937637 := bbase (se 4 (by rfl) ⟨275403, by rfl⟩ : syracuseStep 2937637 = 550807) (by norm_num)
theorem B1102681 : Blo 916578 1102681 := bbase (se 2 (by rfl) ⟨413505, by rfl⟩ : syracuseStep 1102681 = 827011) (by norm_num)
theorem B2511749 : Blo 916578 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B1102825 : Blo 916578 1102825 := bbase (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) (by norm_num)
theorem B3494933 : Blo 916578 3494933 := bbase (se 6 (by rfl) ⟨81912, by rfl⟩ : syracuseStep 3494933 = 163825) (by norm_num)
theorem B3101813 : Blo 916578 3101813 := bbase (se 5 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 3101813 = 290795) (by norm_num)
theorem B1889453 : Blo 916578 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B3495221 : Blo 916578 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B3102245 : Blo 916578 3102245 := bbase (se 4 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 3102245 = 581671) (by norm_num)
theorem B2938805 : Blo 916578 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B4642757 : Blo 916578 4642757 := bbase (se 4 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 4642757 = 870517) (by norm_num)
theorem B3102677 : Blo 916578 3102677 := bbase (se 7 (by rfl) ⟨36359, by rfl⟩ : syracuseStep 3102677 = 72719) (by norm_num)
theorem B1103873 : Blo 916578 1103873 := bbase (se 2 (by rfl) ⟨413952, by rfl⟩ : syracuseStep 1103873 = 827905) (by norm_num)
theorem B1398877 : Blo 916578 1398877 := bbase (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) (by norm_num)
theorem B2480309 : Blo 916578 2480309 := bbase (se 5 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 2480309 = 232529) (by norm_num)
theorem B2480341 : Blo 916578 2480341 := bbase (se 7 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 2480341 = 58133) (by norm_num)
theorem B3922181 : Blo 916578 3922181 := bbase (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) (by norm_num)
theorem B1104205 : Blo 916578 1104205 := bbase (se 3 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 1104205 = 414077) (by norm_num)
theorem B2611541 : Blo 916578 2611541 := bbase (se 10 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 2611541 = 7651) (by norm_num)
theorem B3103109 : Blo 916578 3103109 := bbase (se 4 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 3103109 = 581833) (by norm_num)
theorem B1432205 : Blo 916578 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B3103541 : Blo 916578 3103541 := bbase (se 5 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 3103541 = 290957) (by norm_num)
theorem B2612213 : Blo 916578 2612213 := bbase (se 5 (by rfl) ⟨122447, by rfl⟩ : syracuseStep 2612213 = 244895) (by norm_num)
theorem B7855157 : Blo 916578 7855157 := bbase (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) (by norm_num)
theorem B1105093 : Blo 916578 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B4644053 : Blo 916578 4644053 := bbase (se 7 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 4644053 = 108845) (by norm_num)
theorem B3103973 : Blo 916578 3103973 := bbase (se 4 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 3103973 = 581995) (by norm_num)
theorem B2612645 : Blo 916578 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B1990117 : Blo 916578 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B3726965 : Blo 916578 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B1793669 : Blo 916578 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B3104405 : Blo 916578 3104405 := bbase (se 6 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 3104405 = 145519) (by norm_num)
theorem B2940661 : Blo 916578 2940661 := bbase (se 5 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 2940661 = 275687) (by norm_num)
theorem B1957861 : Blo 916578 1957861 := bbase (se 4 (by rfl) ⟨183549, by rfl⟩ : syracuseStep 1957861 = 367099) (by norm_num)
theorem B3923957 : Blo 916578 3923957 := bbase (se 5 (by rfl) ⟨183935, by rfl⟩ : syracuseStep 3923957 = 367871) (by norm_num)
theorem B3104837 : Blo 916578 3104837 := bbase (se 4 (by rfl) ⟨291078, by rfl⟩ : syracuseStep 3104837 = 582157) (by norm_num)
theorem B2613397 : Blo 916578 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B3924197 : Blo 916578 3924197 := bbase (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) (by norm_num)
theorem B6971669 : Blo 916578 6971669 := bbase (se 6 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 6971669 = 326797) (by norm_num)
theorem B1860013 : Blo 916578 1860013 := bbase (se 3 (by rfl) ⟨348752, by rfl⟩ : syracuseStep 1860013 = 697505) (by norm_num)
theorem B1008073 : Blo 916578 1008073 := bbase (se 2 (by rfl) ⟨378027, by rfl⟩ : syracuseStep 1008073 = 756055) (by norm_num)
theorem B1958357 : Blo 916578 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B4645349 : Blo 916578 4645349 := bbase (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) (by norm_num)
theorem B3105269 : Blo 916578 3105269 := bbase (se 5 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 3105269 = 291119) (by norm_num)
theorem B2482741 : Blo 916578 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B3531365 : Blo 916578 3531365 := bbase (se 4 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 3531365 = 662131) (by norm_num)
theorem B4416373 : Blo 916578 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B2483077 : Blo 916578 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B3105701 : Blo 916578 3105701 := bbase (se 4 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 3105701 = 582319) (by norm_num)
theorem B2942021 : Blo 916578 2942021 := bbase (se 4 (by rfl) ⟨275814, by rfl⟩ : syracuseStep 2942021 = 551629) (by norm_num)
theorem B1959245 : Blo 916578 1959245 := bbase (se 3 (by rfl) ⟨367358, by rfl⟩ : syracuseStep 1959245 = 734717) (by norm_num)
theorem B3106133 : Blo 916578 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B1795421 : Blo 916578 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B1959365 : Blo 916578 1959365 := bbase (se 4 (by rfl) ⟨183690, by rfl⟩ : syracuseStep 1959365 = 367381) (by norm_num)
theorem B35743189 : Blo 916578 35743189 := bbase (se 7 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 35743189 = 837731) (by norm_num)
theorem B8382133 : Blo 916578 8382133 := bbase (se 5 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 8382133 = 785825) (by norm_num)
theorem B4712165 : Blo 916578 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B4646645 : Blo 916578 4646645 := bbase (se 5 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 4646645 = 435623) (by norm_num)
theorem B3106565 : Blo 916578 3106565 := bbase (se 4 (by rfl) ⟨291240, by rfl⟩ : syracuseStep 3106565 = 582481) (by norm_num)
theorem B1238797 : Blo 916578 1238797 := bbase (se 3 (by rfl) ⟨232274, by rfl⟩ : syracuseStep 1238797 = 464549) (by norm_num)
theorem B2516789 : Blo 916578 2516789 := bbase (se 5 (by rfl) ⟨117974, by rfl⟩ : syracuseStep 2516789 = 235949) (by norm_num)
theorem B14903189 : Blo 916578 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B2320285 : Blo 916578 2320285 := bbase (se 3 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 2320285 = 870107) (by norm_num)
theorem B7858133 : Blo 916578 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B4188149 : Blo 916578 4188149 := bbase (se 5 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 4188149 = 392639) (by norm_num)
theorem B2320397 : Blo 916578 2320397 := bbase (se 3 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 2320397 = 870149) (by norm_num)
theorem B1959997 : Blo 916578 1959997 := bbase (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) (by norm_num)
theorem B2320589 : Blo 916578 2320589 := bbase (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) (by norm_num)
theorem B1861861 : Blo 916578 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B1468685 : Blo 916578 1468685 := bbase (se 3 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 1468685 = 550757) (by norm_num)
theorem B5237045 : Blo 916578 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B7072085 : Blo 916578 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B3926485 : Blo 916578 3926485 := bbase (se 7 (by rfl) ⟨46013, by rfl⟩ : syracuseStep 3926485 = 92027) (by norm_num)
theorem B2320933 : Blo 916578 2320933 := bbase (se 4 (by rfl) ⟨217587, by rfl⟩ : syracuseStep 2320933 = 435175) (by norm_num)
theorem B1305229 : Blo 916578 1305229 := bbase (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) (by norm_num)
theorem B2321045 : Blo 916578 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B8841973 : Blo 916578 8841973 := bbase (se 5 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 8841973 = 828935) (by norm_num)
theorem B2321237 : Blo 916578 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B1469357 : Blo 916578 1469357 := bbase (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) (by norm_num)
theorem B1960885 : Blo 916578 1960885 := bbase (se 5 (by rfl) ⟨91916, by rfl⟩ : syracuseStep 1960885 = 183833) (by norm_num)
theorem B2616245 : Blo 916578 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B3533765 : Blo 916578 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B1305605 : Blo 916578 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B4647941 : Blo 916578 4647941 := bbase (se 4 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 4647941 = 871489) (by norm_num)
theorem B1961005 : Blo 916578 1961005 := bbase (se 3 (by rfl) ⟨367688, by rfl⟩ : syracuseStep 1961005 = 735377) (by norm_num)
theorem B2354285 : Blo 916578 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B2321581 : Blo 916578 2321581 := bbase (se 3 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 2321581 = 870593) (by norm_num)
theorem B5893397 : Blo 916578 5893397 := bbase (se 6 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 5893397 = 276253) (by norm_num)
theorem B2321693 : Blo 916578 2321693 := bbase (se 3 (by rfl) ⟨435317, by rfl⟩ : syracuseStep 2321693 = 870635) (by norm_num)
theorem B1961261 : Blo 916578 1961261 := bbase (se 3 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 1961261 = 735473) (by norm_num)
theorem B2092405 : Blo 916578 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B1469869 : Blo 916578 1469869 := bbase (se 3 (by rfl) ⟨275600, by rfl⟩ : syracuseStep 1469869 = 551201) (by norm_num)
theorem B5238229 : Blo 916578 5238229 := bbase (se 7 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 5238229 = 122771) (by norm_num)
theorem B2321885 : Blo 916578 2321885 := bbase (se 3 (by rfl) ⟨435353, by rfl⟩ : syracuseStep 2321885 = 870707) (by norm_num)
theorem B2322229 : Blo 916578 2322229 := bbase (se 5 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 2322229 = 217709) (by norm_num)
theorem B1568621 : Blo 916578 1568621 := bbase (se 3 (by rfl) ⟨294116, by rfl⟩ : syracuseStep 1568621 = 588233) (by norm_num)
theorem B1470325 : Blo 916578 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B2977669 : Blo 916578 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1699717 : Blo 916578 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B2322341 : Blo 916578 2322341 := bbase (se 4 (by rfl) ⟨217719, by rfl⟩ : syracuseStep 2322341 = 435439) (by norm_num)
theorem B3927973 : Blo 916578 3927973 := bbase (se 4 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 3927973 = 736495) (by norm_num)
theorem B3927989 : Blo 916578 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B978905 : Blo 916578 978905 := bbase (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) (by norm_num)
theorem B1863677 : Blo 916578 1863677 := bbase (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) (by norm_num)
theorem B2617429 : Blo 916578 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B2322533 : Blo 916578 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B1568893 : Blo 916578 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B1962149 : Blo 916578 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B2617589 : Blo 916578 2617589 := bbase (se 5 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 2617589 = 245399) (by norm_num)
theorem B4649237 : Blo 916578 4649237 := bbase (se 6 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 4649237 = 217933) (by norm_num)
theorem B3305765 : Blo 916578 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B4714805 : Blo 916578 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B1241413 : Blo 916578 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B979349 : Blo 916578 979349 := bbase (se 6 (by rfl) ⟨22953, by rfl⟩ : syracuseStep 979349 = 45907) (by norm_num)
theorem B1307029 : Blo 916578 1307029 := bbase (se 6 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 1307029 = 61267) (by norm_num)
theorem B1962389 : Blo 916578 1962389 := bbase (se 6 (by rfl) ⟨45993, by rfl⟩ : syracuseStep 1962389 = 91987) (by norm_num)
theorem B2945429 : Blo 916578 2945429 := bbase (se 6 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 2945429 = 138067) (by norm_num)
theorem B1765805 : Blo 916578 1765805 := bbase (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) (by norm_num)
theorem B1438133 : Blo 916578 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B2322877 : Blo 916578 2322877 := bbase (se 3 (by rfl) ⟨435539, by rfl⟩ : syracuseStep 2322877 = 871079) (by norm_num)
theorem B979409 : Blo 916578 979409 := bbase (se 2 (by rfl) ⟨367278, by rfl⟩ : syracuseStep 979409 = 734557) (by norm_num)
theorem B2617829 : Blo 916578 2617829 := bbase (se 4 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 2617829 = 490843) (by norm_num)
theorem B1470997 : Blo 916578 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B2322989 : Blo 916578 2322989 := bbase (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) (by norm_num)
theorem B979537 : Blo 916578 979537 := bbase (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) (by norm_num)
theorem B2618021 : Blo 916578 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B1569461 : Blo 916578 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B2355925 : Blo 916578 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B2323181 : Blo 916578 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B1962893 : Blo 916578 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B1962901 : Blo 916578 1962901 := bbase (se 6 (by rfl) ⟨46005, by rfl⟩ : syracuseStep 1962901 = 92011) (by norm_num)
theorem B1569701 : Blo 916578 1569701 := bbase (se 4 (by rfl) ⟨147159, by rfl⟩ : syracuseStep 1569701 = 294319) (by norm_num)
theorem B1471421 : Blo 916578 1471421 := bbase (se 3 (by rfl) ⟨275891, by rfl⟩ : syracuseStep 1471421 = 551783) (by norm_num)
theorem B4420565 : Blo 916578 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B1307621 : Blo 916578 1307621 := bbase (se 4 (by rfl) ⟨122589, by rfl⟩ : syracuseStep 1307621 = 245179) (by norm_num)
theorem B1569797 : Blo 916578 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B979981 : Blo 916578 979981 := bbase (se 3 (by rfl) ⟨183746, by rfl⟩ : syracuseStep 979981 = 367493) (by norm_num)
theorem B1569845 : Blo 916578 1569845 := bbase (se 5 (by rfl) ⟨73586, by rfl⟩ : syracuseStep 1569845 = 147173) (by norm_num)
theorem B1307701 : Blo 916578 1307701 := bbase (se 5 (by rfl) ⟨61298, by rfl⟩ : syracuseStep 1307701 = 122597) (by norm_num)
theorem B2323525 : Blo 916578 2323525 := bbase (se 4 (by rfl) ⟨217830, by rfl⟩ : syracuseStep 2323525 = 435661) (by norm_num)
theorem B8811605 : Blo 916578 8811605 := bbase (se 8 (by rfl) ⟨51630, by rfl⟩ : syracuseStep 8811605 = 103261) (by norm_num)
theorem B2126965 : Blo 916578 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B980101 : Blo 916578 980101 := bbase (se 4 (by rfl) ⟨91884, by rfl⟩ : syracuseStep 980101 = 183769) (by norm_num)
theorem B1307821 : Blo 916578 1307821 := bbase (se 3 (by rfl) ⟨245216, by rfl⟩ : syracuseStep 1307821 = 490433) (by norm_num)
theorem B2323637 : Blo 916578 2323637 := bbase (se 5 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 2323637 = 217841) (by norm_num)
theorem B1242317 : Blo 916578 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B1471709 : Blo 916578 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1307917 : Blo 916578 1307917 := bbase (se 3 (by rfl) ⟨245234, by rfl⟩ : syracuseStep 1307917 = 490469) (by norm_num)
theorem B2323829 : Blo 916578 2323829 := bbase (se 5 (by rfl) ⟨108929, by rfl⟩ : syracuseStep 2323829 = 217859) (by norm_num)
theorem B980353 : Blo 916578 980353 := bbase (se 2 (by rfl) ⟨367632, by rfl⟩ : syracuseStep 980353 = 735265) (by norm_num)
theorem B980357 : Blo 916578 980357 := bbase (se 4 (by rfl) ⟨91908, by rfl⟩ : syracuseStep 980357 = 183817) (by norm_num)
theorem B5240213 : Blo 916578 5240213 := bbase (se 6 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 5240213 = 245635) (by norm_num)
theorem B8844821 : Blo 916578 8844821 := bbase (se 6 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 8844821 = 414601) (by norm_num)
theorem B4650533 : Blo 916578 4650533 := bbase (se 4 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 4650533 = 871975) (by norm_num)
theorem B1767037 : Blo 916578 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B2619013 : Blo 916578 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B2946709 : Blo 916578 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B1177265 : Blo 916578 1177265 := bbase (se 2 (by rfl) ⟨441474, by rfl⟩ : syracuseStep 1177265 = 882949) (by norm_num)
theorem B5732021 : Blo 916578 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B2324173 : Blo 916578 2324173 := bbase (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) (by norm_num)
theorem B1308413 : Blo 916578 1308413 := bbase (se 3 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 1308413 = 490655) (by norm_num)
theorem B2324285 : Blo 916578 2324285 := bbase (se 3 (by rfl) ⟨435803, by rfl⟩ : syracuseStep 2324285 = 871607) (by norm_num)
theorem B1242949 : Blo 916578 1242949 := bbase (se 4 (by rfl) ⟨116526, by rfl⟩ : syracuseStep 1242949 = 233053) (by norm_num)
theorem B980921 : Blo 916578 980921 := bbase (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) (by norm_num)
theorem B2324477 : Blo 916578 2324477 := bbase (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) (by norm_num)
theorem B1472509 : Blo 916578 1472509 := bbase (se 3 (by rfl) ⟨276095, by rfl⟩ : syracuseStep 1472509 = 552191) (by norm_num)
theorem B1964029 : Blo 916578 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2062349 : Blo 916578 2062349 := bbase (se 3 (by rfl) ⟨386690, by rfl⟩ : syracuseStep 2062349 = 773381) (by norm_num)
theorem B2062421 : Blo 916578 2062421 := bbase (se 8 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 2062421 = 24169) (by norm_num)
theorem B19888213 : Blo 916578 19888213 := bbase (se 8 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 19888213 = 233065) (by norm_num)
theorem B981109 : Blo 916578 981109 := bbase (se 5 (by rfl) ⟨45989, by rfl⟩ : syracuseStep 981109 = 91979) (by norm_num)
theorem B3930245 : Blo 916578 3930245 := bbase (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) (by norm_num)
theorem B2062493 : Blo 916578 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B2062565 : Blo 916578 2062565 := bbase (se 4 (by rfl) ⟨193365, by rfl⟩ : syracuseStep 2062565 = 386731) (by norm_num)
theorem B4421909 : Blo 916578 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B1308965 : Blo 916578 1308965 := bbase (se 4 (by rfl) ⟨122715, by rfl⟩ : syracuseStep 1308965 = 245431) (by norm_num)
theorem B2062637 : Blo 916578 2062637 := bbase (se 3 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 2062637 = 773489) (by norm_num)
theorem B2324821 : Blo 916578 2324821 := bbase (se 10 (by rfl) ⟨3405, by rfl⟩ : syracuseStep 2324821 = 6811) (by norm_num)
theorem B2062709 : Blo 916578 2062709 := bbase (se 5 (by rfl) ⟨96689, by rfl⟩ : syracuseStep 2062709 = 193379) (by norm_num)
theorem B1964405 : Blo 916578 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B1571213 : Blo 916578 1571213 := bbase (se 3 (by rfl) ⟨294602, by rfl⟩ : syracuseStep 1571213 = 589205) (by norm_num)
theorem B5896597 : Blo 916578 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B2062781 : Blo 916578 2062781 := bbase (se 3 (by rfl) ⟨386771, by rfl⟩ : syracuseStep 2062781 = 773543) (by norm_num)
theorem B2324933 : Blo 916578 2324933 := bbase (se 4 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 2324933 = 435925) (by norm_num)
theorem B2062853 : Blo 916578 2062853 := bbase (se 4 (by rfl) ⟨193392, by rfl⟩ : syracuseStep 2062853 = 386785) (by norm_num)
theorem B1473061 : Blo 916578 1473061 := bbase (se 4 (by rfl) ⟨138099, by rfl⟩ : syracuseStep 1473061 = 276199) (by norm_num)
theorem B2062925 : Blo 916578 2062925 := bbase (se 3 (by rfl) ⟨386798, by rfl⟩ : syracuseStep 2062925 = 773597) (by norm_num)
theorem B2325125 : Blo 916578 2325125 := bbase (se 4 (by rfl) ⟨217980, by rfl⟩ : syracuseStep 2325125 = 435961) (by norm_num)
theorem B1374869 : Blo 916578 1374869 := bbase (se 6 (by rfl) ⟨32223, by rfl⟩ : syracuseStep 1374869 = 64447) (by norm_num)
theorem B2062997 : Blo 916578 2062997 := bbase (se 6 (by rfl) ⟨48351, by rfl⟩ : syracuseStep 2062997 = 96703) (by norm_num)
theorem B1374893 : Blo 916578 1374893 := bbase (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) (by norm_num)
theorem B1374917 : Blo 916578 1374917 := bbase (se 4 (by rfl) ⟨128898, by rfl⟩ : syracuseStep 1374917 = 257797) (by norm_num)
theorem B2620117 : Blo 916578 2620117 := bbase (se 7 (by rfl) ⟨30704, by rfl⟩ : syracuseStep 2620117 = 61409) (by norm_num)
theorem B1374941 : Blo 916578 1374941 := bbase (se 3 (by rfl) ⟨257801, by rfl⟩ : syracuseStep 1374941 = 515603) (by norm_num)
theorem B2063069 : Blo 916578 2063069 := bbase (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) (by norm_num)
theorem B2357981 : Blo 916578 2357981 := bbase (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) (by norm_num)
theorem B1374965 : Blo 916578 1374965 := bbase (se 5 (by rfl) ⟨64451, by rfl⟩ : syracuseStep 1374965 = 128903) (by norm_num)
theorem B3144437 : Blo 916578 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B1374989 : Blo 916578 1374989 := bbase (se 3 (by rfl) ⟨257810, by rfl⟩ : syracuseStep 1374989 = 515621) (by norm_num)
theorem B1375013 : Blo 916578 1375013 := bbase (se 4 (by rfl) ⟨128907, by rfl⟩ : syracuseStep 1375013 = 257815) (by norm_num)
theorem B2063141 : Blo 916578 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B1473317 : Blo 916578 1473317 := bbase (se 4 (by rfl) ⟨138123, by rfl⟩ : syracuseStep 1473317 = 276247) (by norm_num)
theorem B4651829 : Blo 916578 4651829 := bbase (se 5 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 4651829 = 436109) (by norm_num)
theorem B1375037 : Blo 916578 1375037 := bbase (se 3 (by rfl) ⟨257819, by rfl⟩ : syracuseStep 1375037 = 515639) (by norm_num)
theorem B1375061 : Blo 916578 1375061 := bbase (se 9 (by rfl) ⟨4028, by rfl⟩ : syracuseStep 1375061 = 8057) (by norm_num)
theorem B1375085 : Blo 916578 1375085 := bbase (se 3 (by rfl) ⟨257828, by rfl⟩ : syracuseStep 1375085 = 515657) (by norm_num)
theorem B2063213 : Blo 916578 2063213 := bbase (se 3 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 2063213 = 773705) (by norm_num)
theorem B1047425 : Blo 916578 1047425 := bbase (se 2 (by rfl) ⟨392784, by rfl⟩ : syracuseStep 1047425 = 785569) (by norm_num)
theorem B1375109 : Blo 916578 1375109 := bbase (se 4 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 1375109 = 257833) (by norm_num)
theorem B1375133 : Blo 916578 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B981929 : Blo 916578 981929 := bbase (se 2 (by rfl) ⟨368223, by rfl⟩ : syracuseStep 981929 = 736447) (by norm_num)
theorem B1375157 : Blo 916578 1375157 := bbase (se 5 (by rfl) ⟨64460, by rfl⟩ : syracuseStep 1375157 = 128921) (by norm_num)
theorem B2063285 : Blo 916578 2063285 := bbase (se 5 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 2063285 = 193433) (by norm_num)
theorem B1375181 : Blo 916578 1375181 := bbase (se 3 (by rfl) ⟨257846, by rfl⟩ : syracuseStep 1375181 = 515693) (by norm_num)
theorem B2325469 : Blo 916578 2325469 := bbase (se 3 (by rfl) ⟨436025, by rfl⟩ : syracuseStep 2325469 = 872051) (by norm_num)
theorem B1375205 : Blo 916578 1375205 := bbase (se 4 (by rfl) ⟨128925, by rfl⟩ : syracuseStep 1375205 = 257851) (by norm_num)
theorem B2948069 : Blo 916578 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B1375229 : Blo 916578 1375229 := bbase (se 3 (by rfl) ⟨257855, by rfl⟩ : syracuseStep 1375229 = 515711) (by norm_num)
theorem B2063357 : Blo 916578 2063357 := bbase (se 3 (by rfl) ⟨386879, by rfl⟩ : syracuseStep 2063357 = 773759) (by norm_num)
theorem B1375253 : Blo 916578 1375253 := bbase (se 6 (by rfl) ⟨32232, by rfl⟩ : syracuseStep 1375253 = 64465) (by norm_num)
theorem B1309717 : Blo 916578 1309717 := bbase (se 6 (by rfl) ⟨30696, by rfl⟩ : syracuseStep 1309717 = 61393) (by norm_num)
theorem B1375277 : Blo 916578 1375277 := bbase (se 3 (by rfl) ⟨257864, by rfl⟩ : syracuseStep 1375277 = 515729) (by norm_num)
theorem B1375301 : Blo 916578 1375301 := bbase (se 4 (by rfl) ⟨128934, by rfl⟩ : syracuseStep 1375301 = 257869) (by norm_num)
theorem B2063429 : Blo 916578 2063429 := bbase (se 4 (by rfl) ⟨193446, by rfl⟩ : syracuseStep 2063429 = 386893) (by norm_num)
theorem B2325581 : Blo 916578 2325581 := bbase (se 3 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 2325581 = 872093) (by norm_num)
theorem B1375325 : Blo 916578 1375325 := bbase (se 3 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 1375325 = 515747) (by norm_num)
theorem B2948197 : Blo 916578 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B1375349 : Blo 916578 1375349 := bbase (se 5 (by rfl) ⟨64469, by rfl⟩ : syracuseStep 1375349 = 128939) (by norm_num)
theorem B1375373 : Blo 916578 1375373 := bbase (se 3 (by rfl) ⟨257882, by rfl⟩ : syracuseStep 1375373 = 515765) (by norm_num)
theorem B2063501 : Blo 916578 2063501 := bbase (se 3 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 2063501 = 773813) (by norm_num)
theorem B1375397 : Blo 916578 1375397 := bbase (se 4 (by rfl) ⟨128943, by rfl⟩ : syracuseStep 1375397 = 257887) (by norm_num)
theorem B1375421 : Blo 916578 1375421 := bbase (se 3 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 1375421 = 515783) (by norm_num)
theorem B1375445 : Blo 916578 1375445 := bbase (se 7 (by rfl) ⟨16118, by rfl⟩ : syracuseStep 1375445 = 32237) (by norm_num)
theorem B2063573 : Blo 916578 2063573 := bbase (se 7 (by rfl) ⟨24182, by rfl⟩ : syracuseStep 2063573 = 48365) (by norm_num)
theorem B1375469 : Blo 916578 1375469 := bbase (se 3 (by rfl) ⟨257900, by rfl⟩ : syracuseStep 1375469 = 515801) (by norm_num)
theorem B1375493 : Blo 916578 1375493 := bbase (se 4 (by rfl) ⟨128952, by rfl⟩ : syracuseStep 1375493 = 257905) (by norm_num)
theorem B2325773 : Blo 916578 2325773 := bbase (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) (by norm_num)
theorem B1375517 : Blo 916578 1375517 := bbase (se 3 (by rfl) ⟨257909, by rfl⟩ : syracuseStep 1375517 = 515819) (by norm_num)
theorem B2063645 : Blo 916578 2063645 := bbase (se 3 (by rfl) ⟨386933, by rfl⟩ : syracuseStep 2063645 = 773867) (by norm_num)
theorem B1375541 : Blo 916578 1375541 := bbase (se 5 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 1375541 = 128957) (by norm_num)
theorem B1375565 : Blo 916578 1375565 := bbase (se 3 (by rfl) ⟨257918, by rfl⟩ : syracuseStep 1375565 = 515837) (by norm_num)
theorem B1375589 : Blo 916578 1375589 := bbase (se 4 (by rfl) ⟨128961, by rfl⟩ : syracuseStep 1375589 = 257923) (by norm_num)
theorem B2063717 : Blo 916578 2063717 := bbase (se 4 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 2063717 = 386947) (by norm_num)
theorem B982373 : Blo 916578 982373 := bbase (se 4 (by rfl) ⟨92097, by rfl⟩ : syracuseStep 982373 = 184195) (by norm_num)
theorem B2948453 : Blo 916578 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B1375613 : Blo 916578 1375613 := bbase (se 3 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 1375613 = 515855) (by norm_num)
theorem B1375637 : Blo 916578 1375637 := bbase (se 6 (by rfl) ⟨32241, by rfl⟩ : syracuseStep 1375637 = 64483) (by norm_num)
theorem B1047973 : Blo 916578 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B1375661 : Blo 916578 1375661 := bbase (se 3 (by rfl) ⟨257936, by rfl⟩ : syracuseStep 1375661 = 515873) (by norm_num)
theorem B2063789 : Blo 916578 2063789 := bbase (se 3 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 2063789 = 773921) (by norm_num)
theorem B1375685 : Blo 916578 1375685 := bbase (se 4 (by rfl) ⟨128970, by rfl⟩ : syracuseStep 1375685 = 257941) (by norm_num)
theorem B1375709 : Blo 916578 1375709 := bbase (se 3 (by rfl) ⟨257945, by rfl⟩ : syracuseStep 1375709 = 515891) (by norm_num)
theorem B1474021 : Blo 916578 1474021 := bbase (se 4 (by rfl) ⟨138189, by rfl⟩ : syracuseStep 1474021 = 276379) (by norm_num)
theorem B1375733 : Blo 916578 1375733 := bbase (se 5 (by rfl) ⟨64487, by rfl⟩ : syracuseStep 1375733 = 128975) (by norm_num)
theorem B2063861 : Blo 916578 2063861 := bbase (se 5 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 2063861 = 193487) (by norm_num)
theorem B1375757 : Blo 916578 1375757 := bbase (se 3 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 1375757 = 515909) (by norm_num)
theorem B2391565 : Blo 916578 2391565 := bbase (se 3 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 2391565 = 896837) (by norm_num)
theorem B1375781 : Blo 916578 1375781 := bbase (se 4 (by rfl) ⟨128979, by rfl⟩ : syracuseStep 1375781 = 257959) (by norm_num)
theorem B5242421 : Blo 916578 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B1375805 : Blo 916578 1375805 := bbase (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) (by norm_num)
theorem B2063933 : Blo 916578 2063933 := bbase (se 3 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 2063933 = 773975) (by norm_num)
theorem B1375829 : Blo 916578 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B982621 : Blo 916578 982621 := bbase (se 3 (by rfl) ⟨184241, by rfl⟩ : syracuseStep 982621 = 368483) (by norm_num)
theorem B2326117 : Blo 916578 2326117 := bbase (se 4 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 2326117 = 436147) (by norm_num)
theorem B1375853 : Blo 916578 1375853 := bbase (se 3 (by rfl) ⟨257972, by rfl⟩ : syracuseStep 1375853 = 515945) (by norm_num)
theorem B1375877 : Blo 916578 1375877 := bbase (se 4 (by rfl) ⟨128988, by rfl⟩ : syracuseStep 1375877 = 257977) (by norm_num)
theorem B2064005 : Blo 916578 2064005 := bbase (se 4 (by rfl) ⟨193500, by rfl⟩ : syracuseStep 2064005 = 387001) (by norm_num)
theorem B2981509 : Blo 916578 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B1375901 : Blo 916578 1375901 := bbase (se 3 (by rfl) ⟨257981, by rfl⟩ : syracuseStep 1375901 = 515963) (by norm_num)
theorem B1375925 : Blo 916578 1375925 := bbase (se 5 (by rfl) ⟨64496, by rfl⟩ : syracuseStep 1375925 = 128993) (by norm_num)
theorem B1375949 : Blo 916578 1375949 := bbase (se 3 (by rfl) ⟨257990, by rfl⟩ : syracuseStep 1375949 = 515981) (by norm_num)
theorem B2064077 : Blo 916578 2064077 := bbase (se 3 (by rfl) ⟨387014, by rfl⟩ : syracuseStep 2064077 = 774029) (by norm_num)
theorem B2326229 : Blo 916578 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B1375973 : Blo 916578 1375973 := bbase (se 4 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 1375973 = 257995) (by norm_num)
theorem B1375997 : Blo 916578 1375997 := bbase (se 3 (by rfl) ⟨257999, by rfl⟩ : syracuseStep 1375997 = 515999) (by norm_num)
theorem B2391805 : Blo 916578 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B1376021 : Blo 916578 1376021 := bbase (se 6 (by rfl) ⟨32250, by rfl⟩ : syracuseStep 1376021 = 64501) (by norm_num)
theorem B2064149 : Blo 916578 2064149 := bbase (se 6 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 2064149 = 96757) (by norm_num)
theorem B1376045 : Blo 916578 1376045 := bbase (se 3 (by rfl) ⟨258008, by rfl⟩ : syracuseStep 1376045 = 516017) (by norm_num)
theorem B1310509 : Blo 916578 1310509 := bbase (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) (by norm_num)
theorem B1376069 : Blo 916578 1376069 := bbase (se 4 (by rfl) ⟨129006, by rfl⟩ : syracuseStep 1376069 = 258013) (by norm_num)
theorem B1769285 : Blo 916578 1769285 := bbase (se 4 (by rfl) ⟨165870, by rfl⟩ : syracuseStep 1769285 = 331741) (by norm_num)
theorem B1376093 : Blo 916578 1376093 := bbase (se 3 (by rfl) ⟨258017, by rfl⟩ : syracuseStep 1376093 = 516035) (by norm_num)
theorem B2064221 : Blo 916578 2064221 := bbase (se 3 (by rfl) ⟨387041, by rfl⟩ : syracuseStep 2064221 = 774083) (by norm_num)
theorem B1376117 : Blo 916578 1376117 := bbase (se 5 (by rfl) ⟨64505, by rfl⟩ : syracuseStep 1376117 = 129011) (by norm_num)
theorem B6979445 : Blo 916578 6979445 := bbase (se 5 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 6979445 = 654323) (by norm_num)
theorem B1376141 : Blo 916578 1376141 := bbase (se 3 (by rfl) ⟨258026, by rfl⟩ : syracuseStep 1376141 = 516053) (by norm_num)
theorem B1474445 : Blo 916578 1474445 := bbase (se 3 (by rfl) ⟨276458, by rfl⟩ : syracuseStep 1474445 = 552917) (by norm_num)
theorem B2326421 : Blo 916578 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B1376165 : Blo 916578 1376165 := bbase (se 4 (by rfl) ⟨129015, by rfl⟩ : syracuseStep 1376165 = 258031) (by norm_num)
theorem B2064293 : Blo 916578 2064293 := bbase (se 4 (by rfl) ⟨193527, by rfl⟩ : syracuseStep 2064293 = 387055) (by norm_num)
theorem B1376189 : Blo 916578 1376189 := bbase (se 3 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 1376189 = 516071) (by norm_num)
theorem B1376213 : Blo 916578 1376213 := bbase (se 7 (by rfl) ⟨16127, by rfl⟩ : syracuseStep 1376213 = 32255) (by norm_num)
theorem B1966045 : Blo 916578 1966045 := bbase (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) (by norm_num)
theorem B1376237 : Blo 916578 1376237 := bbase (se 3 (by rfl) ⟨258044, by rfl⟩ : syracuseStep 1376237 = 516089) (by norm_num)
theorem B2064365 : Blo 916578 2064365 := bbase (se 3 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 2064365 = 774137) (by norm_num)
theorem B2424829 : Blo 916578 2424829 := bbase (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) (by norm_num)
theorem B917507 : Blo 916578 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B2064401 : Blo 916578 2064401 := bstep (se 2 (by rfl) ⟨774150, by rfl⟩ : syracuseStep 2064401 = 1548301) B1548301
theorem B1376273 : Blo 916578 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B917523 : Blo 916578 917523 := bstep (se 1 (by rfl) ⟨688142, by rfl⟩ : syracuseStep 917523 = 1376285) B1376285
theorem B1310737 : Blo 916578 1310737 := bstep (se 2 (by rfl) ⟨491526, by rfl⟩ : syracuseStep 1310737 = 983053) B983053
theorem B2064419 : Blo 916578 2064419 := bstep (se 1 (by rfl) ⟨1548314, by rfl⟩ : syracuseStep 2064419 = 3096629) B3096629
theorem B1376291 : Blo 916578 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B917539 : Blo 916578 917539 := bstep (se 1 (by rfl) ⟨688154, by rfl⟩ : syracuseStep 917539 = 1376309) B1376309
theorem B917555 : Blo 916578 917555 := bstep (se 1 (by rfl) ⟨688166, by rfl⟩ : syracuseStep 917555 = 1376333) B1376333
theorem B1376321 : Blo 916578 1376321 := bstep (se 2 (by rfl) ⟨516120, by rfl⟩ : syracuseStep 1376321 = 1032241) B1032241
theorem B917571 : Blo 916578 917571 := bstep (se 1 (by rfl) ⟨688178, by rfl⟩ : syracuseStep 917571 = 1376357) B1376357
theorem B1376339 : Blo 916578 1376339 := bstep (se 1 (by rfl) ⟨1032254, by rfl⟩ : syracuseStep 1376339 = 2064509) B2064509
theorem B917587 : Blo 916578 917587 := bstep (se 1 (by rfl) ⟨688190, by rfl⟩ : syracuseStep 917587 = 1376381) B1376381
theorem B917603 : Blo 916578 917603 := bstep (se 1 (by rfl) ⟨688202, by rfl⟩ : syracuseStep 917603 = 1376405) B1376405
theorem B1376369 : Blo 916578 1376369 := bstep (se 2 (by rfl) ⟨516138, by rfl⟩ : syracuseStep 1376369 = 1032277) B1032277
theorem B917619 : Blo 916578 917619 := bstep (se 1 (by rfl) ⟨688214, by rfl⟩ : syracuseStep 917619 = 1376429) B1376429
theorem B1376387 : Blo 916578 1376387 := bstep (se 1 (by rfl) ⟨1032290, by rfl⟩ : syracuseStep 1376387 = 2064581) B2064581
theorem B917635 : Blo 916578 917635 := bstep (se 1 (by rfl) ⟨688226, by rfl⟩ : syracuseStep 917635 = 1376453) B1376453
theorem B917651 : Blo 916578 917651 := bstep (se 1 (by rfl) ⟨688238, by rfl⟩ : syracuseStep 917651 = 1376477) B1376477
theorem B1376417 : Blo 916578 1376417 := bstep (se 2 (by rfl) ⟨516156, by rfl⟩ : syracuseStep 1376417 = 1032313) B1032313
theorem B917667 : Blo 916578 917667 := bstep (se 1 (by rfl) ⟨688250, by rfl⟩ : syracuseStep 917667 = 1376501) B1376501
theorem B1376435 : Blo 916578 1376435 := bstep (se 1 (by rfl) ⟨1032326, by rfl⟩ : syracuseStep 1376435 = 2064653) B2064653
theorem B917683 : Blo 916578 917683 := bstep (se 1 (by rfl) ⟨688262, by rfl⟩ : syracuseStep 917683 = 1376525) B1376525
theorem B917699 : Blo 916578 917699 := bstep (se 1 (by rfl) ⟨688274, by rfl⟩ : syracuseStep 917699 = 1376549) B1376549
theorem B1376465 : Blo 916578 1376465 := bstep (se 2 (by rfl) ⟨516174, by rfl⟩ : syracuseStep 1376465 = 1032349) B1032349
theorem B917715 : Blo 916578 917715 := bstep (se 1 (by rfl) ⟨688286, by rfl⟩ : syracuseStep 917715 = 1376573) B1376573
theorem B1376483 : Blo 916578 1376483 := bstep (se 1 (by rfl) ⟨1032362, by rfl⟩ : syracuseStep 1376483 = 2064725) B2064725
theorem B917731 : Blo 916578 917731 := bstep (se 1 (by rfl) ⟨688298, by rfl⟩ : syracuseStep 917731 = 1376597) B1376597
theorem B917747 : Blo 916578 917747 := bstep (se 1 (by rfl) ⟨688310, by rfl⟩ : syracuseStep 917747 = 1376621) B1376621
theorem B1376513 : Blo 916578 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B917763 : Blo 916578 917763 := bstep (se 1 (by rfl) ⟨688322, by rfl⟩ : syracuseStep 917763 = 1376645) B1376645
theorem B1376531 : Blo 916578 1376531 := bstep (se 1 (by rfl) ⟨1032398, by rfl⟩ : syracuseStep 1376531 = 2064797) B2064797
theorem B917779 : Blo 916578 917779 := bstep (se 1 (by rfl) ⟨688334, by rfl⟩ : syracuseStep 917779 = 1376669) B1376669
theorem B917795 : Blo 916578 917795 := bstep (se 1 (by rfl) ⟨688346, by rfl⟩ : syracuseStep 917795 = 1376693) B1376693
theorem B2064689 : Blo 916578 2064689 := bstep (se 2 (by rfl) ⟨774258, by rfl⟩ : syracuseStep 2064689 = 1548517) B1548517
theorem B1376561 : Blo 916578 1376561 := bstep (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) B1032421
theorem B917811 : Blo 916578 917811 := bstep (se 1 (by rfl) ⟨688358, by rfl⟩ : syracuseStep 917811 = 1376717) B1376717
theorem B1769777 : Blo 916578 1769777 := bstep (se 2 (by rfl) ⟨663666, by rfl⟩ : syracuseStep 1769777 = 1327333) B1327333
theorem B1179955 : Blo 916578 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B2064707 : Blo 916578 2064707 := bstep (se 1 (by rfl) ⟨1548530, by rfl⟩ : syracuseStep 2064707 = 3097061) B3097061
theorem B1376579 : Blo 916578 1376579 := bstep (se 1 (by rfl) ⟨1032434, by rfl⟩ : syracuseStep 1376579 = 2064869) B2064869
theorem B917827 : Blo 916578 917827 := bstep (se 1 (by rfl) ⟨688370, by rfl⟩ : syracuseStep 917827 = 1376741) B1376741
theorem B3146051 : Blo 916578 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B917843 : Blo 916578 917843 := bstep (se 1 (by rfl) ⟨688382, by rfl⟩ : syracuseStep 917843 = 1376765) B1376765
theorem B1376609 : Blo 916578 1376609 := bstep (se 2 (by rfl) ⟨516228, by rfl⟩ : syracuseStep 1376609 = 1032457) B1032457
theorem B917859 : Blo 916578 917859 := bstep (se 1 (by rfl) ⟨688394, by rfl⟩ : syracuseStep 917859 = 1376789) B1376789
theorem B1376627 : Blo 916578 1376627 := bstep (se 1 (by rfl) ⟨1032470, by rfl⟩ : syracuseStep 1376627 = 2064941) B2064941
theorem B917875 : Blo 916578 917875 := bstep (se 1 (by rfl) ⟨688406, by rfl⟩ : syracuseStep 917875 = 1376813) B1376813
theorem B917891 : Blo 916578 917891 := bstep (se 1 (by rfl) ⟨688418, by rfl⟩ : syracuseStep 917891 = 1376837) B1376837
theorem B1376657 : Blo 916578 1376657 := bstep (se 2 (by rfl) ⟨516246, by rfl⟩ : syracuseStep 1376657 = 1032493) B1032493
theorem B917907 : Blo 916578 917907 := bstep (se 1 (by rfl) ⟨688430, by rfl⟩ : syracuseStep 917907 = 1376861) B1376861
theorem B1376675 : Blo 916578 1376675 := bstep (se 1 (by rfl) ⟨1032506, by rfl⟩ : syracuseStep 1376675 = 2065013) B2065013
theorem B917923 : Blo 916578 917923 := bstep (se 1 (by rfl) ⟨688442, by rfl⟩ : syracuseStep 917923 = 1376885) B1376885
theorem B917939 : Blo 916578 917939 := bstep (se 1 (by rfl) ⟨688454, by rfl⟩ : syracuseStep 917939 = 1376909) B1376909
theorem B1376705 : Blo 916578 1376705 := bstep (se 2 (by rfl) ⟨516264, by rfl⟩ : syracuseStep 1376705 = 1032529) B1032529
theorem B2720195 : Blo 916578 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B917955 : Blo 916578 917955 := bstep (se 1 (by rfl) ⟨688466, by rfl⟩ : syracuseStep 917955 = 1376933) B1376933
theorem B1376723 : Blo 916578 1376723 := bstep (se 1 (by rfl) ⟨1032542, by rfl⟩ : syracuseStep 1376723 = 2065085) B2065085
theorem B917971 : Blo 916578 917971 := bstep (se 1 (by rfl) ⟨688478, by rfl⟩ : syracuseStep 917971 = 1376957) B1376957
theorem B917987 : Blo 916578 917987 := bstep (se 1 (by rfl) ⟨688490, by rfl⟩ : syracuseStep 917987 = 1376981) B1376981
theorem B1376753 : Blo 916578 1376753 := bstep (se 2 (by rfl) ⟨516282, by rfl⟩ : syracuseStep 1376753 = 1032565) B1032565
theorem B918003 : Blo 916578 918003 := bstep (se 1 (by rfl) ⟨688502, by rfl⟩ : syracuseStep 918003 = 1377005) B1377005
theorem B1376771 : Blo 916578 1376771 := bstep (se 1 (by rfl) ⟨1032578, by rfl⟩ : syracuseStep 1376771 = 2065157) B2065157
theorem B918019 : Blo 916578 918019 := bstep (se 1 (by rfl) ⟨688514, by rfl⟩ : syracuseStep 918019 = 1377029) B1377029
theorem B918035 : Blo 916578 918035 := bstep (se 1 (by rfl) ⟨688526, by rfl⟩ : syracuseStep 918035 = 1377053) B1377053
theorem B1376801 : Blo 916578 1376801 := bstep (se 2 (by rfl) ⟨516300, by rfl⟩ : syracuseStep 1376801 = 1032601) B1032601
theorem B918051 : Blo 916578 918051 := bstep (se 1 (by rfl) ⟨688538, by rfl⟩ : syracuseStep 918051 = 1377077) B1377077
theorem B2327089 : Blo 916578 2327089 := bstep (se 2 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 2327089 = 1745317) B1745317
theorem B1376819 : Blo 916578 1376819 := bstep (se 1 (by rfl) ⟨1032614, by rfl⟩ : syracuseStep 1376819 = 2065229) B2065229
theorem B918067 : Blo 916578 918067 := bstep (se 1 (by rfl) ⟨688550, by rfl⟩ : syracuseStep 918067 = 1377101) B1377101
theorem B918083 : Blo 916578 918083 := bstep (se 1 (by rfl) ⟨688562, by rfl⟩ : syracuseStep 918083 = 1377125) B1377125
theorem B2064977 : Blo 916578 2064977 := bstep (se 2 (by rfl) ⟨774366, by rfl⟩ : syracuseStep 2064977 = 1548733) B1548733
theorem B1376849 : Blo 916578 1376849 := bstep (se 2 (by rfl) ⟨516318, by rfl⟩ : syracuseStep 1376849 = 1032637) B1032637
theorem B918099 : Blo 916578 918099 := bstep (se 1 (by rfl) ⟨688574, by rfl⟩ : syracuseStep 918099 = 1377149) B1377149
theorem B1344097 : Blo 916578 1344097 := bstep (se 2 (by rfl) ⟨504036, by rfl⟩ : syracuseStep 1344097 = 1008073) B1008073
theorem B2064995 : Blo 916578 2064995 := bstep (se 1 (by rfl) ⟨1548746, by rfl⟩ : syracuseStep 2064995 = 3097493) B3097493
theorem B1376867 : Blo 916578 1376867 := bstep (se 1 (by rfl) ⟨1032650, by rfl⟩ : syracuseStep 1376867 = 2065301) B2065301
theorem B918115 : Blo 916578 918115 := bstep (se 1 (by rfl) ⟨688586, by rfl⟩ : syracuseStep 918115 = 1377173) B1377173
theorem B918131 : Blo 916578 918131 := bstep (se 1 (by rfl) ⟨688598, by rfl⟩ : syracuseStep 918131 = 1377197) B1377197
theorem B1376897 : Blo 916578 1376897 := bstep (se 2 (by rfl) ⟨516336, by rfl⟩ : syracuseStep 1376897 = 1032673) B1032673
theorem B918147 : Blo 916578 918147 := bstep (se 1 (by rfl) ⟨688610, by rfl⟩ : syracuseStep 918147 = 1377221) B1377221
theorem B1376915 : Blo 916578 1376915 := bstep (se 1 (by rfl) ⟨1032686, by rfl⟩ : syracuseStep 1376915 = 2065373) B2065373
theorem B918163 : Blo 916578 918163 := bstep (se 1 (by rfl) ⟨688622, by rfl⟩ : syracuseStep 918163 = 1377245) B1377245
theorem B918179 : Blo 916578 918179 := bstep (se 1 (by rfl) ⟨688634, by rfl⟩ : syracuseStep 918179 = 1377269) B1377269
theorem B1376945 : Blo 916578 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B918195 : Blo 916578 918195 := bstep (se 1 (by rfl) ⟨688646, by rfl⟩ : syracuseStep 918195 = 1377293) B1377293
theorem B1376963 : Blo 916578 1376963 := bstep (se 1 (by rfl) ⟨1032722, by rfl⟩ : syracuseStep 1376963 = 2065445) B2065445
theorem B918211 : Blo 916578 918211 := bstep (se 1 (by rfl) ⟨688658, by rfl⟩ : syracuseStep 918211 = 1377317) B1377317
theorem B4653773 : Blo 916578 4653773 := bstep (se 3 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 4653773 = 1745165) B1745165
theorem B918227 : Blo 916578 918227 := bstep (se 1 (by rfl) ⟨688670, by rfl⟩ : syracuseStep 918227 = 1377341) B1377341
theorem B1376993 : Blo 916578 1376993 := bstep (se 2 (by rfl) ⟨516372, by rfl⟩ : syracuseStep 1376993 = 1032745) B1032745
theorem B918243 : Blo 916578 918243 := bstep (se 1 (by rfl) ⟨688682, by rfl⟩ : syracuseStep 918243 = 1377365) B1377365
theorem B3310321 : Blo 916578 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B1377011 : Blo 916578 1377011 := bstep (se 1 (by rfl) ⟨1032758, by rfl⟩ : syracuseStep 1377011 = 2065517) B2065517
theorem B918259 : Blo 916578 918259 := bstep (se 1 (by rfl) ⟨688694, by rfl⟩ : syracuseStep 918259 = 1377389) B1377389
theorem B918275 : Blo 916578 918275 := bstep (se 1 (by rfl) ⟨688706, by rfl⟩ : syracuseStep 918275 = 1377413) B1377413
theorem B1377041 : Blo 916578 1377041 := bstep (se 2 (by rfl) ⟨516390, by rfl⟩ : syracuseStep 1377041 = 1032781) B1032781
theorem B918291 : Blo 916578 918291 := bstep (se 1 (by rfl) ⟨688718, by rfl⟩ : syracuseStep 918291 = 1377437) B1377437
theorem B1377059 : Blo 916578 1377059 := bstep (se 1 (by rfl) ⟨1032794, by rfl⟩ : syracuseStep 1377059 = 2065589) B2065589
theorem B918307 : Blo 916578 918307 := bstep (se 1 (by rfl) ⟨688730, by rfl⟩ : syracuseStep 918307 = 1377461) B1377461
theorem B918323 : Blo 916578 918323 := bstep (se 1 (by rfl) ⟨688742, by rfl⟩ : syracuseStep 918323 = 1377485) B1377485
theorem B1377089 : Blo 916578 1377089 := bstep (se 2 (by rfl) ⟨516408, by rfl⟩ : syracuseStep 1377089 = 1032817) B1032817
theorem B918339 : Blo 916578 918339 := bstep (se 1 (by rfl) ⟨688754, by rfl⟩ : syracuseStep 918339 = 1377509) B1377509
theorem B2327363 : Blo 916578 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B1377107 : Blo 916578 1377107 := bstep (se 1 (by rfl) ⟨1032830, by rfl⟩ : syracuseStep 1377107 = 2065661) B2065661
theorem B918355 : Blo 916578 918355 := bstep (se 1 (by rfl) ⟨688766, by rfl⟩ : syracuseStep 918355 = 1377533) B1377533
theorem B10453859 : Blo 916578 10453859 := bstep (se 1 (by rfl) ⟨7840394, by rfl⟩ : syracuseStep 10453859 = 15680789) B15680789
theorem B918371 : Blo 916578 918371 := bstep (se 1 (by rfl) ⟨688778, by rfl⟩ : syracuseStep 918371 = 1377557) B1377557
theorem B2065265 : Blo 916578 2065265 := bstep (se 2 (by rfl) ⟨774474, by rfl⟩ : syracuseStep 2065265 = 1548949) B1548949
theorem B1377137 : Blo 916578 1377137 := bstep (se 2 (by rfl) ⟨516426, by rfl⟩ : syracuseStep 1377137 = 1032853) B1032853
theorem B918387 : Blo 916578 918387 := bstep (se 1 (by rfl) ⟨688790, by rfl⟩ : syracuseStep 918387 = 1377581) B1377581
theorem B2065283 : Blo 916578 2065283 := bstep (se 1 (by rfl) ⟨1548962, by rfl⟩ : syracuseStep 2065283 = 3097925) B3097925
theorem B1377155 : Blo 916578 1377155 := bstep (se 1 (by rfl) ⟨1032866, by rfl⟩ : syracuseStep 1377155 = 2065733) B2065733
theorem B918403 : Blo 916578 918403 := bstep (se 1 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 918403 = 1377605) B1377605
theorem B918419 : Blo 916578 918419 := bstep (se 1 (by rfl) ⟨688814, by rfl⟩ : syracuseStep 918419 = 1377629) B1377629
theorem B1377185 : Blo 916578 1377185 := bstep (se 2 (by rfl) ⟨516444, by rfl⟩ : syracuseStep 1377185 = 1032889) B1032889
theorem B918435 : Blo 916578 918435 := bstep (se 1 (by rfl) ⟨688826, by rfl⟩ : syracuseStep 918435 = 1377653) B1377653
theorem B1377203 : Blo 916578 1377203 := bstep (se 1 (by rfl) ⟨1032902, by rfl⟩ : syracuseStep 1377203 = 2065805) B2065805
theorem B918451 : Blo 916578 918451 := bstep (se 1 (by rfl) ⟨688838, by rfl⟩ : syracuseStep 918451 = 1377677) B1377677
theorem B918467 : Blo 916578 918467 := bstep (se 1 (by rfl) ⟨688850, by rfl⟩ : syracuseStep 918467 = 1377701) B1377701
theorem B1377233 : Blo 916578 1377233 := bstep (se 2 (by rfl) ⟨516462, by rfl⟩ : syracuseStep 1377233 = 1032925) B1032925
theorem B918483 : Blo 916578 918483 := bstep (se 1 (by rfl) ⟨688862, by rfl⟩ : syracuseStep 918483 = 1377725) B1377725
theorem B1377251 : Blo 916578 1377251 := bstep (se 1 (by rfl) ⟨1032938, by rfl⟩ : syracuseStep 1377251 = 2065877) B2065877
theorem B918499 : Blo 916578 918499 := bstep (se 1 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 918499 = 1377749) B1377749
theorem B918515 : Blo 916578 918515 := bstep (se 1 (by rfl) ⟨688886, by rfl⟩ : syracuseStep 918515 = 1377773) B1377773
theorem B1377281 : Blo 916578 1377281 := bstep (se 2 (by rfl) ⟨516480, by rfl⟩ : syracuseStep 1377281 = 1032961) B1032961
theorem B918531 : Blo 916578 918531 := bstep (se 1 (by rfl) ⟨688898, by rfl⟩ : syracuseStep 918531 = 1377797) B1377797
theorem B2327555 : Blo 916578 2327555 := bstep (se 1 (by rfl) ⟨1745666, by rfl⟩ : syracuseStep 2327555 = 3491333) B3491333
theorem B1377299 : Blo 916578 1377299 := bstep (se 1 (by rfl) ⟨1032974, by rfl⟩ : syracuseStep 1377299 = 2065949) B2065949
theorem B918547 : Blo 916578 918547 := bstep (se 1 (by rfl) ⟨688910, by rfl⟩ : syracuseStep 918547 = 1377821) B1377821
theorem B918563 : Blo 916578 918563 := bstep (se 1 (by rfl) ⟨688922, by rfl⟩ : syracuseStep 918563 = 1377845) B1377845
theorem B1377329 : Blo 916578 1377329 := bstep (se 2 (by rfl) ⟨516498, by rfl⟩ : syracuseStep 1377329 = 1032997) B1032997
theorem B918579 : Blo 916578 918579 := bstep (se 1 (by rfl) ⟨688934, by rfl⟩ : syracuseStep 918579 = 1377869) B1377869
theorem B1377347 : Blo 916578 1377347 := bstep (se 1 (by rfl) ⟨1033010, by rfl⟩ : syracuseStep 1377347 = 2066021) B2066021
theorem B918595 : Blo 916578 918595 := bstep (se 1 (by rfl) ⟨688946, by rfl⟩ : syracuseStep 918595 = 1377893) B1377893
theorem B918611 : Blo 916578 918611 := bstep (se 1 (by rfl) ⟨688958, by rfl⟩ : syracuseStep 918611 = 1377917) B1377917
theorem B1377377 : Blo 916578 1377377 := bstep (se 2 (by rfl) ⟨516516, by rfl⟩ : syracuseStep 1377377 = 1033033) B1033033
theorem B918627 : Blo 916578 918627 := bstep (se 1 (by rfl) ⟨688970, by rfl⟩ : syracuseStep 918627 = 1377941) B1377941
theorem B1377395 : Blo 916578 1377395 := bstep (se 1 (by rfl) ⟨1033046, by rfl⟩ : syracuseStep 1377395 = 2066093) B2066093
theorem B918643 : Blo 916578 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B918659 : Blo 916578 918659 := bstep (se 1 (by rfl) ⟨688994, by rfl⟩ : syracuseStep 918659 = 1377989) B1377989
theorem B2065553 : Blo 916578 2065553 := bstep (se 2 (by rfl) ⟨774582, by rfl⟩ : syracuseStep 2065553 = 1549165) B1549165
theorem B1377425 : Blo 916578 1377425 := bstep (se 2 (by rfl) ⟨516534, by rfl⟩ : syracuseStep 1377425 = 1033069) B1033069
theorem B918675 : Blo 916578 918675 := bstep (se 1 (by rfl) ⟨689006, by rfl⟩ : syracuseStep 918675 = 1378013) B1378013
theorem B2065571 : Blo 916578 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B1377443 : Blo 916578 1377443 := bstep (se 1 (by rfl) ⟨1033082, by rfl⟩ : syracuseStep 1377443 = 2066165) B2066165
theorem B918691 : Blo 916578 918691 := bstep (se 1 (by rfl) ⟨689018, by rfl⟩ : syracuseStep 918691 = 1378037) B1378037
theorem B3310769 : Blo 916578 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B918707 : Blo 916578 918707 := bstep (se 1 (by rfl) ⟨689030, by rfl⟩ : syracuseStep 918707 = 1378061) B1378061
theorem B1377473 : Blo 916578 1377473 := bstep (se 2 (by rfl) ⟨516552, by rfl⟩ : syracuseStep 1377473 = 1033105) B1033105
theorem B918723 : Blo 916578 918723 := bstep (se 1 (by rfl) ⟨689042, by rfl⟩ : syracuseStep 918723 = 1378085) B1378085
theorem B1377491 : Blo 916578 1377491 := bstep (se 1 (by rfl) ⟨1033118, by rfl⟩ : syracuseStep 1377491 = 2066237) B2066237
theorem B918739 : Blo 916578 918739 := bstep (se 1 (by rfl) ⟨689054, by rfl⟩ : syracuseStep 918739 = 1378109) B1378109
theorem B918755 : Blo 916578 918755 := bstep (se 1 (by rfl) ⟨689066, by rfl⟩ : syracuseStep 918755 = 1378133) B1378133
theorem B1377521 : Blo 916578 1377521 := bstep (se 2 (by rfl) ⟨516570, by rfl⟩ : syracuseStep 1377521 = 1033141) B1033141
theorem B918771 : Blo 916578 918771 := bstep (se 1 (by rfl) ⟨689078, by rfl⟩ : syracuseStep 918771 = 1378157) B1378157
theorem B1377539 : Blo 916578 1377539 := bstep (se 1 (by rfl) ⟨1033154, by rfl⟩ : syracuseStep 1377539 = 2066309) B2066309
theorem B918787 : Blo 916578 918787 := bstep (se 1 (by rfl) ⟨689090, by rfl⟩ : syracuseStep 918787 = 1378181) B1378181
theorem B918803 : Blo 916578 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B1377569 : Blo 916578 1377569 := bstep (se 2 (by rfl) ⟨516588, by rfl⟩ : syracuseStep 1377569 = 1033177) B1033177
theorem B918819 : Blo 916578 918819 := bstep (se 1 (by rfl) ⟨689114, by rfl⟩ : syracuseStep 918819 = 1378229) B1378229
theorem B1377587 : Blo 916578 1377587 := bstep (se 1 (by rfl) ⟨1033190, by rfl⟩ : syracuseStep 1377587 = 2066381) B2066381
theorem B918835 : Blo 916578 918835 := bstep (se 1 (by rfl) ⟨689126, by rfl⟩ : syracuseStep 918835 = 1378253) B1378253
theorem B918851 : Blo 916578 918851 := bstep (se 1 (by rfl) ⟨689138, by rfl⟩ : syracuseStep 918851 = 1378277) B1378277
theorem B1377617 : Blo 916578 1377617 := bstep (se 2 (by rfl) ⟨516606, by rfl⟩ : syracuseStep 1377617 = 1033213) B1033213
theorem B1574225 : Blo 916578 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B918867 : Blo 916578 918867 := bstep (se 1 (by rfl) ⟨689150, by rfl⟩ : syracuseStep 918867 = 1378301) B1378301
theorem B1377635 : Blo 916578 1377635 := bstep (se 1 (by rfl) ⟨1033226, by rfl⟩ : syracuseStep 1377635 = 2066453) B2066453
theorem B918883 : Blo 916578 918883 := bstep (se 1 (by rfl) ⟨689162, by rfl⟩ : syracuseStep 918883 = 1378325) B1378325
theorem B918899 : Blo 916578 918899 := bstep (se 1 (by rfl) ⟨689174, by rfl⟩ : syracuseStep 918899 = 1378349) B1378349
theorem B1377665 : Blo 916578 1377665 := bstep (se 2 (by rfl) ⟨516624, by rfl⟩ : syracuseStep 1377665 = 1033249) B1033249
theorem B918915 : Blo 916578 918915 := bstep (se 1 (by rfl) ⟨689186, by rfl⟩ : syracuseStep 918915 = 1378373) B1378373
theorem B1377683 : Blo 916578 1377683 := bstep (se 1 (by rfl) ⟨1033262, by rfl⟩ : syracuseStep 1377683 = 2066525) B2066525
theorem B918931 : Blo 916578 918931 := bstep (se 1 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 918931 = 1378397) B1378397
theorem B918947 : Blo 916578 918947 := bstep (se 1 (by rfl) ⟨689210, by rfl⟩ : syracuseStep 918947 = 1378421) B1378421
theorem B2065841 : Blo 916578 2065841 := bstep (se 2 (by rfl) ⟨774690, by rfl⟩ : syracuseStep 2065841 = 1549381) B1549381
theorem B1377713 : Blo 916578 1377713 := bstep (se 2 (by rfl) ⟨516642, by rfl⟩ : syracuseStep 1377713 = 1033285) B1033285
theorem B918963 : Blo 916578 918963 := bstep (se 1 (by rfl) ⟨689222, by rfl⟩ : syracuseStep 918963 = 1378445) B1378445
theorem B2065859 : Blo 916578 2065859 := bstep (se 1 (by rfl) ⟨1549394, by rfl⟩ : syracuseStep 2065859 = 3098789) B3098789
theorem B1377731 : Blo 916578 1377731 := bstep (se 1 (by rfl) ⟨1033298, by rfl⟩ : syracuseStep 1377731 = 2066597) B2066597
theorem B918979 : Blo 916578 918979 := bstep (se 1 (by rfl) ⟨689234, by rfl⟩ : syracuseStep 918979 = 1378469) B1378469
theorem B918995 : Blo 916578 918995 := bstep (se 1 (by rfl) ⟨689246, by rfl⟩ : syracuseStep 918995 = 1378493) B1378493
theorem B1377761 : Blo 916578 1377761 := bstep (se 2 (by rfl) ⟨516660, by rfl⟩ : syracuseStep 1377761 = 1033321) B1033321
theorem B919011 : Blo 916578 919011 := bstep (se 1 (by rfl) ⟨689258, by rfl⟩ : syracuseStep 919011 = 1378517) B1378517
theorem B3147245 : Blo 916578 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B1377779 : Blo 916578 1377779 := bstep (se 1 (by rfl) ⟨1033334, by rfl⟩ : syracuseStep 1377779 = 2066669) B2066669
theorem B919027 : Blo 916578 919027 := bstep (se 1 (by rfl) ⟨689270, by rfl⟩ : syracuseStep 919027 = 1378541) B1378541
theorem B919043 : Blo 916578 919043 := bstep (se 1 (by rfl) ⟨689282, by rfl⟩ : syracuseStep 919043 = 1378565) B1378565
theorem B1377809 : Blo 916578 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B919059 : Blo 916578 919059 := bstep (se 1 (by rfl) ⟨689294, by rfl⟩ : syracuseStep 919059 = 1378589) B1378589
theorem B1377827 : Blo 916578 1377827 := bstep (se 1 (by rfl) ⟨1033370, by rfl⟩ : syracuseStep 1377827 = 2066741) B2066741
theorem B919075 : Blo 916578 919075 := bstep (se 1 (by rfl) ⟨689306, by rfl⟩ : syracuseStep 919075 = 1378613) B1378613
theorem B919091 : Blo 916578 919091 := bstep (se 1 (by rfl) ⟨689318, by rfl⟩ : syracuseStep 919091 = 1378637) B1378637
theorem B1377857 : Blo 916578 1377857 := bstep (se 2 (by rfl) ⟨516696, by rfl⟩ : syracuseStep 1377857 = 1033393) B1033393
theorem B919107 : Blo 916578 919107 := bstep (se 1 (by rfl) ⟨689330, by rfl⟩ : syracuseStep 919107 = 1378661) B1378661
theorem B8291909 : Blo 916578 8291909 := bstep (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) B1554733
theorem B1377875 : Blo 916578 1377875 := bstep (se 1 (by rfl) ⟨1033406, by rfl⟩ : syracuseStep 1377875 = 2066813) B2066813
theorem B919123 : Blo 916578 919123 := bstep (se 1 (by rfl) ⟨689342, by rfl⟩ : syracuseStep 919123 = 1378685) B1378685
theorem B919139 : Blo 916578 919139 := bstep (se 1 (by rfl) ⟨689354, by rfl⟩ : syracuseStep 919139 = 1378709) B1378709
theorem B1377905 : Blo 916578 1377905 := bstep (se 2 (by rfl) ⟨516714, by rfl⟩ : syracuseStep 1377905 = 1033429) B1033429
theorem B919155 : Blo 916578 919155 := bstep (se 1 (by rfl) ⟨689366, by rfl⟩ : syracuseStep 919155 = 1378733) B1378733
theorem B1377923 : Blo 916578 1377923 := bstep (se 1 (by rfl) ⟨1033442, by rfl⟩ : syracuseStep 1377923 = 2066885) B2066885
theorem B919171 : Blo 916578 919171 := bstep (se 1 (by rfl) ⟨689378, by rfl⟩ : syracuseStep 919171 = 1378757) B1378757
theorem B919187 : Blo 916578 919187 := bstep (se 1 (by rfl) ⟨689390, by rfl⟩ : syracuseStep 919187 = 1378781) B1378781
theorem B1377953 : Blo 916578 1377953 := bstep (se 2 (by rfl) ⟨516732, by rfl⟩ : syracuseStep 1377953 = 1033465) B1033465
theorem B919203 : Blo 916578 919203 := bstep (se 1 (by rfl) ⟨689402, by rfl⟩ : syracuseStep 919203 = 1378805) B1378805
theorem B1377971 : Blo 916578 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B919219 : Blo 916578 919219 := bstep (se 1 (by rfl) ⟨689414, by rfl⟩ : syracuseStep 919219 = 1378829) B1378829
theorem B919235 : Blo 916578 919235 := bstep (se 1 (by rfl) ⟨689426, by rfl⟩ : syracuseStep 919235 = 1378853) B1378853
theorem B6620869 : Blo 916578 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B2066129 : Blo 916578 2066129 := bstep (se 2 (by rfl) ⟨774798, by rfl⟩ : syracuseStep 2066129 = 1549597) B1549597
theorem B1378001 : Blo 916578 1378001 := bstep (se 2 (by rfl) ⟨516750, by rfl⟩ : syracuseStep 1378001 = 1033501) B1033501
theorem B919251 : Blo 916578 919251 := bstep (se 1 (by rfl) ⟨689438, by rfl⟩ : syracuseStep 919251 = 1378877) B1378877
theorem B2066147 : Blo 916578 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B1378019 : Blo 916578 1378019 := bstep (se 1 (by rfl) ⟨1033514, by rfl⟩ : syracuseStep 1378019 = 2067029) B2067029
theorem B919267 : Blo 916578 919267 := bstep (se 1 (by rfl) ⟨689450, by rfl⟩ : syracuseStep 919267 = 1378901) B1378901
theorem B919283 : Blo 916578 919283 := bstep (se 1 (by rfl) ⟨689462, by rfl⟩ : syracuseStep 919283 = 1378925) B1378925
theorem B1378049 : Blo 916578 1378049 := bstep (se 2 (by rfl) ⟨516768, by rfl⟩ : syracuseStep 1378049 = 1033537) B1033537
theorem B919299 : Blo 916578 919299 := bstep (se 1 (by rfl) ⟨689474, by rfl⟩ : syracuseStep 919299 = 1378949) B1378949
theorem B6981389 : Blo 916578 6981389 := bstep (se 3 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 6981389 = 2618021) B2618021
theorem B1378067 : Blo 916578 1378067 := bstep (se 1 (by rfl) ⟨1033550, by rfl⟩ : syracuseStep 1378067 = 2067101) B2067101
theorem B919315 : Blo 916578 919315 := bstep (se 1 (by rfl) ⟨689486, by rfl⟩ : syracuseStep 919315 = 1378973) B1378973
theorem B919331 : Blo 916578 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B1378097 : Blo 916578 1378097 := bstep (se 2 (by rfl) ⟨516786, by rfl⟩ : syracuseStep 1378097 = 1033573) B1033573
theorem B919347 : Blo 916578 919347 := bstep (se 1 (by rfl) ⟨689510, by rfl⟩ : syracuseStep 919347 = 1379021) B1379021
theorem B1378115 : Blo 916578 1378115 := bstep (se 1 (by rfl) ⟨1033586, by rfl⟩ : syracuseStep 1378115 = 2067173) B2067173
theorem B919363 : Blo 916578 919363 := bstep (se 1 (by rfl) ⟨689522, by rfl⟩ : syracuseStep 919363 = 1379045) B1379045
theorem B919379 : Blo 916578 919379 := bstep (se 1 (by rfl) ⟨689534, by rfl⟩ : syracuseStep 919379 = 1379069) B1379069
theorem B1378145 : Blo 916578 1378145 := bstep (se 2 (by rfl) ⟨516804, by rfl⟩ : syracuseStep 1378145 = 1033609) B1033609
theorem B919395 : Blo 916578 919395 := bstep (se 1 (by rfl) ⟨689546, by rfl⟩ : syracuseStep 919395 = 1379093) B1379093
theorem B1378163 : Blo 916578 1378163 := bstep (se 1 (by rfl) ⟨1033622, by rfl⟩ : syracuseStep 1378163 = 2067245) B2067245
theorem B919411 : Blo 916578 919411 := bstep (se 1 (by rfl) ⟨689558, by rfl⟩ : syracuseStep 919411 = 1379117) B1379117
theorem B919427 : Blo 916578 919427 := bstep (se 1 (by rfl) ⟨689570, by rfl⟩ : syracuseStep 919427 = 1379141) B1379141
theorem B1378193 : Blo 916578 1378193 := bstep (se 2 (by rfl) ⟨516822, by rfl⟩ : syracuseStep 1378193 = 1033645) B1033645
theorem B919443 : Blo 916578 919443 := bstep (se 1 (by rfl) ⟨689582, by rfl⟩ : syracuseStep 919443 = 1379165) B1379165
theorem B1378211 : Blo 916578 1378211 := bstep (se 1 (by rfl) ⟨1033658, by rfl⟩ : syracuseStep 1378211 = 2067317) B2067317
theorem B919459 : Blo 916578 919459 := bstep (se 1 (by rfl) ⟨689594, by rfl⟩ : syracuseStep 919459 = 1379189) B1379189
theorem B2328497 : Blo 916578 2328497 := bstep (se 2 (by rfl) ⟨873186, by rfl⟩ : syracuseStep 2328497 = 1746373) B1746373
theorem B919475 : Blo 916578 919475 := bstep (se 1 (by rfl) ⟨689606, by rfl⟩ : syracuseStep 919475 = 1379213) B1379213
theorem B1378241 : Blo 916578 1378241 := bstep (se 2 (by rfl) ⟨516840, by rfl⟩ : syracuseStep 1378241 = 1033681) B1033681
theorem B919491 : Blo 916578 919491 := bstep (se 1 (by rfl) ⟨689618, by rfl⟩ : syracuseStep 919491 = 1379237) B1379237
theorem B1378259 : Blo 916578 1378259 := bstep (se 1 (by rfl) ⟨1033694, by rfl⟩ : syracuseStep 1378259 = 2067389) B2067389
theorem B919507 : Blo 916578 919507 := bstep (se 1 (by rfl) ⟨689630, by rfl⟩ : syracuseStep 919507 = 1379261) B1379261
theorem B919523 : Blo 916578 919523 := bstep (se 1 (by rfl) ⟨689642, by rfl⟩ : syracuseStep 919523 = 1379285) B1379285
theorem B2328547 : Blo 916578 2328547 := bstep (se 1 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 2328547 = 3492821) B3492821
theorem B2066417 : Blo 916578 2066417 := bstep (se 2 (by rfl) ⟨774906, by rfl⟩ : syracuseStep 2066417 = 1549813) B1549813
theorem B1378289 : Blo 916578 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B919539 : Blo 916578 919539 := bstep (se 1 (by rfl) ⟨689654, by rfl⟩ : syracuseStep 919539 = 1379309) B1379309
theorem B2066435 : Blo 916578 2066435 := bstep (se 1 (by rfl) ⟨1549826, by rfl⟩ : syracuseStep 2066435 = 3099653) B3099653
theorem B1378307 : Blo 916578 1378307 := bstep (se 1 (by rfl) ⟨1033730, by rfl⟩ : syracuseStep 1378307 = 2067461) B2067461
theorem B919555 : Blo 916578 919555 := bstep (se 1 (by rfl) ⟨689666, by rfl⟩ : syracuseStep 919555 = 1379333) B1379333
theorem B919571 : Blo 916578 919571 := bstep (se 1 (by rfl) ⟨689678, by rfl⟩ : syracuseStep 919571 = 1379357) B1379357
theorem B1378337 : Blo 916578 1378337 := bstep (se 2 (by rfl) ⟨516876, by rfl⟩ : syracuseStep 1378337 = 1033753) B1033753
theorem B919587 : Blo 916578 919587 := bstep (se 1 (by rfl) ⟨689690, by rfl⟩ : syracuseStep 919587 = 1379381) B1379381
theorem B1378355 : Blo 916578 1378355 := bstep (se 1 (by rfl) ⟨1033766, by rfl⟩ : syracuseStep 1378355 = 2067533) B2067533
theorem B919603 : Blo 916578 919603 := bstep (se 1 (by rfl) ⟨689702, by rfl⟩ : syracuseStep 919603 = 1379405) B1379405
theorem B919619 : Blo 916578 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B1378385 : Blo 916578 1378385 := bstep (se 2 (by rfl) ⟨516894, by rfl⟩ : syracuseStep 1378385 = 1033789) B1033789
theorem B919635 : Blo 916578 919635 := bstep (se 1 (by rfl) ⟨689726, by rfl⟩ : syracuseStep 919635 = 1379453) B1379453
theorem B1378403 : Blo 916578 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B919651 : Blo 916578 919651 := bstep (se 1 (by rfl) ⟨689738, by rfl⟩ : syracuseStep 919651 = 1379477) B1379477
theorem B919667 : Blo 916578 919667 := bstep (se 1 (by rfl) ⟨689750, by rfl⟩ : syracuseStep 919667 = 1379501) B1379501
theorem B2328689 : Blo 916578 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B1378433 : Blo 916578 1378433 := bstep (se 2 (by rfl) ⟨516912, by rfl⟩ : syracuseStep 1378433 = 1033825) B1033825
theorem B919683 : Blo 916578 919683 := bstep (se 1 (by rfl) ⟨689762, by rfl⟩ : syracuseStep 919683 = 1379525) B1379525
theorem B1378451 : Blo 916578 1378451 := bstep (se 1 (by rfl) ⟨1033838, by rfl⟩ : syracuseStep 1378451 = 2067677) B2067677
theorem B919699 : Blo 916578 919699 := bstep (se 1 (by rfl) ⟨689774, by rfl⟩ : syracuseStep 919699 = 1379549) B1379549
theorem B919715 : Blo 916578 919715 := bstep (se 1 (by rfl) ⟨689786, by rfl⟩ : syracuseStep 919715 = 1379573) B1379573
theorem B1378481 : Blo 916578 1378481 := bstep (se 2 (by rfl) ⟨516930, by rfl⟩ : syracuseStep 1378481 = 1033861) B1033861
theorem B919731 : Blo 916578 919731 := bstep (se 1 (by rfl) ⟨689798, by rfl⟩ : syracuseStep 919731 = 1379597) B1379597
theorem B1378499 : Blo 916578 1378499 := bstep (se 1 (by rfl) ⟨1033874, by rfl⟩ : syracuseStep 1378499 = 2067749) B2067749
theorem B919747 : Blo 916578 919747 := bstep (se 1 (by rfl) ⟨689810, by rfl⟩ : syracuseStep 919747 = 1379621) B1379621
theorem B919763 : Blo 916578 919763 := bstep (se 1 (by rfl) ⟨689822, by rfl⟩ : syracuseStep 919763 = 1379645) B1379645
theorem B1378529 : Blo 916578 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B919779 : Blo 916578 919779 := bstep (se 1 (by rfl) ⟨689834, by rfl⟩ : syracuseStep 919779 = 1379669) B1379669
theorem B1378547 : Blo 916578 1378547 := bstep (se 1 (by rfl) ⟨1033910, by rfl⟩ : syracuseStep 1378547 = 2067821) B2067821
theorem B919795 : Blo 916578 919795 := bstep (se 1 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 919795 = 1379693) B1379693
theorem B919811 : Blo 916578 919811 := bstep (se 1 (by rfl) ⟨689858, by rfl⟩ : syracuseStep 919811 = 1379717) B1379717
theorem B2066705 : Blo 916578 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B1378577 : Blo 916578 1378577 := bstep (se 2 (by rfl) ⟨516966, by rfl⟩ : syracuseStep 1378577 = 1033933) B1033933
theorem B919827 : Blo 916578 919827 := bstep (se 1 (by rfl) ⟨689870, by rfl⟩ : syracuseStep 919827 = 1379741) B1379741
theorem B2066723 : Blo 916578 2066723 := bstep (se 1 (by rfl) ⟨1550042, by rfl⟩ : syracuseStep 2066723 = 3100085) B3100085
theorem B1378595 : Blo 916578 1378595 := bstep (se 1 (by rfl) ⟨1033946, by rfl⟩ : syracuseStep 1378595 = 2067893) B2067893
theorem B919843 : Blo 916578 919843 := bstep (se 1 (by rfl) ⟨689882, by rfl⟩ : syracuseStep 919843 = 1379765) B1379765
theorem B919859 : Blo 916578 919859 := bstep (se 1 (by rfl) ⟨689894, by rfl⟩ : syracuseStep 919859 = 1379789) B1379789
theorem B1378625 : Blo 916578 1378625 := bstep (se 2 (by rfl) ⟨516984, by rfl⟩ : syracuseStep 1378625 = 1033969) B1033969
theorem B919875 : Blo 916578 919875 := bstep (se 1 (by rfl) ⟨689906, by rfl⟩ : syracuseStep 919875 = 1379813) B1379813
theorem B1378643 : Blo 916578 1378643 := bstep (se 1 (by rfl) ⟨1033982, by rfl⟩ : syracuseStep 1378643 = 2067965) B2067965
theorem B919891 : Blo 916578 919891 := bstep (se 1 (by rfl) ⟨689918, by rfl⟩ : syracuseStep 919891 = 1379837) B1379837
theorem B919907 : Blo 916578 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B1378673 : Blo 916578 1378673 := bstep (se 2 (by rfl) ⟨517002, by rfl⟩ : syracuseStep 1378673 = 1034005) B1034005
theorem B919923 : Blo 916578 919923 := bstep (se 1 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 919923 = 1379885) B1379885
theorem B1116547 : Blo 916578 1116547 := bstep (se 1 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 1116547 = 1674821) B1674821
theorem B1378691 : Blo 916578 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B919939 : Blo 916578 919939 := bstep (se 1 (by rfl) ⟨689954, by rfl⟩ : syracuseStep 919939 = 1379909) B1379909
theorem B919955 : Blo 916578 919955 := bstep (se 1 (by rfl) ⟨689966, by rfl⟩ : syracuseStep 919955 = 1379933) B1379933
theorem B1378721 : Blo 916578 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B919971 : Blo 916578 919971 := bstep (se 1 (by rfl) ⟨689978, by rfl⟩ : syracuseStep 919971 = 1379957) B1379957
theorem B1378739 : Blo 916578 1378739 := bstep (se 1 (by rfl) ⟨1034054, by rfl⟩ : syracuseStep 1378739 = 2068109) B2068109
theorem B919987 : Blo 916578 919987 := bstep (se 1 (by rfl) ⟨689990, by rfl⟩ : syracuseStep 919987 = 1379981) B1379981
theorem B920003 : Blo 916578 920003 := bstep (se 1 (by rfl) ⟨690002, by rfl⟩ : syracuseStep 920003 = 1380005) B1380005
theorem B1378769 : Blo 916578 1378769 := bstep (se 2 (by rfl) ⟨517038, by rfl⟩ : syracuseStep 1378769 = 1034077) B1034077
theorem B920019 : Blo 916578 920019 := bstep (se 1 (by rfl) ⟨690014, by rfl⟩ : syracuseStep 920019 = 1380029) B1380029
theorem B1378787 : Blo 916578 1378787 := bstep (se 1 (by rfl) ⟨1034090, by rfl⟩ : syracuseStep 1378787 = 2068181) B2068181
theorem B920035 : Blo 916578 920035 := bstep (se 1 (by rfl) ⟨690026, by rfl⟩ : syracuseStep 920035 = 1380053) B1380053
theorem B920051 : Blo 916578 920051 := bstep (se 1 (by rfl) ⟨690038, by rfl⟩ : syracuseStep 920051 = 1380077) B1380077
theorem B1378817 : Blo 916578 1378817 := bstep (se 2 (by rfl) ⟨517056, by rfl⟩ : syracuseStep 1378817 = 1034113) B1034113
theorem B920067 : Blo 916578 920067 := bstep (se 1 (by rfl) ⟨690050, by rfl⟩ : syracuseStep 920067 = 1380101) B1380101
theorem B1378835 : Blo 916578 1378835 := bstep (se 1 (by rfl) ⟨1034126, by rfl⟩ : syracuseStep 1378835 = 2068253) B2068253
theorem B920083 : Blo 916578 920083 := bstep (se 1 (by rfl) ⟨690062, by rfl⟩ : syracuseStep 920083 = 1380125) B1380125
theorem B920099 : Blo 916578 920099 := bstep (se 1 (by rfl) ⟨690074, by rfl⟩ : syracuseStep 920099 = 1380149) B1380149
theorem B2066993 : Blo 916578 2066993 := bstep (se 2 (by rfl) ⟨775122, by rfl⟩ : syracuseStep 2066993 = 1550245) B1550245
theorem B1378865 : Blo 916578 1378865 := bstep (se 2 (by rfl) ⟨517074, by rfl⟩ : syracuseStep 1378865 = 1034149) B1034149
theorem B920115 : Blo 916578 920115 := bstep (se 1 (by rfl) ⟨690086, by rfl⟩ : syracuseStep 920115 = 1380173) B1380173
theorem B3181123 : Blo 916578 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B2067011 : Blo 916578 2067011 := bstep (se 1 (by rfl) ⟨1550258, by rfl⟩ : syracuseStep 2067011 = 3100517) B3100517
theorem B1378883 : Blo 916578 1378883 := bstep (se 1 (by rfl) ⟨1034162, by rfl⟩ : syracuseStep 1378883 = 2068325) B2068325
theorem B920131 : Blo 916578 920131 := bstep (se 1 (by rfl) ⟨690098, by rfl⟩ : syracuseStep 920131 = 1380197) B1380197
theorem B920147 : Blo 916578 920147 := bstep (se 1 (by rfl) ⟨690110, by rfl⟩ : syracuseStep 920147 = 1380221) B1380221
theorem B1378913 : Blo 916578 1378913 := bstep (se 2 (by rfl) ⟨517092, by rfl⟩ : syracuseStep 1378913 = 1034185) B1034185
theorem B920163 : Blo 916578 920163 := bstep (se 1 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 920163 = 1380245) B1380245
theorem B1378931 : Blo 916578 1378931 := bstep (se 1 (by rfl) ⟨1034198, by rfl⟩ : syracuseStep 1378931 = 2068397) B2068397
theorem B920179 : Blo 916578 920179 := bstep (se 1 (by rfl) ⟨690134, by rfl⟩ : syracuseStep 920179 = 1380269) B1380269
theorem B920195 : Blo 916578 920195 := bstep (se 1 (by rfl) ⟨690146, by rfl⟩ : syracuseStep 920195 = 1380293) B1380293
theorem B1378961 : Blo 916578 1378961 := bstep (se 2 (by rfl) ⟨517110, by rfl⟩ : syracuseStep 1378961 = 1034221) B1034221
theorem B920211 : Blo 916578 920211 := bstep (se 1 (by rfl) ⟨690158, by rfl⟩ : syracuseStep 920211 = 1380317) B1380317
theorem B1378979 : Blo 916578 1378979 := bstep (se 1 (by rfl) ⟨1034234, by rfl⟩ : syracuseStep 1378979 = 2068469) B2068469
theorem B920227 : Blo 916578 920227 := bstep (se 1 (by rfl) ⟨690170, by rfl⟩ : syracuseStep 920227 = 1380341) B1380341
theorem B920243 : Blo 916578 920243 := bstep (se 1 (by rfl) ⟨690182, by rfl⟩ : syracuseStep 920243 = 1380365) B1380365
theorem B1379009 : Blo 916578 1379009 := bstep (se 2 (by rfl) ⟨517128, by rfl⟩ : syracuseStep 1379009 = 1034257) B1034257
theorem B920259 : Blo 916578 920259 := bstep (se 1 (by rfl) ⟨690194, by rfl⟩ : syracuseStep 920259 = 1380389) B1380389
theorem B1379027 : Blo 916578 1379027 := bstep (se 1 (by rfl) ⟨1034270, by rfl⟩ : syracuseStep 1379027 = 2068541) B2068541
theorem B920275 : Blo 916578 920275 := bstep (se 1 (by rfl) ⟨690206, by rfl⟩ : syracuseStep 920275 = 1380413) B1380413
theorem B920291 : Blo 916578 920291 := bstep (se 1 (by rfl) ⟨690218, by rfl⟩ : syracuseStep 920291 = 1380437) B1380437
theorem B1379057 : Blo 916578 1379057 := bstep (se 2 (by rfl) ⟨517146, by rfl⟩ : syracuseStep 1379057 = 1034293) B1034293
theorem B920307 : Blo 916578 920307 := bstep (se 1 (by rfl) ⟨690230, by rfl⟩ : syracuseStep 920307 = 1380461) B1380461
theorem B1379075 : Blo 916578 1379075 := bstep (se 1 (by rfl) ⟨1034306, by rfl⟩ : syracuseStep 1379075 = 2068613) B2068613
theorem B920323 : Blo 916578 920323 := bstep (se 1 (by rfl) ⟨690242, by rfl⟩ : syracuseStep 920323 = 1380485) B1380485
theorem B920339 : Blo 916578 920339 := bstep (se 1 (by rfl) ⟨690254, by rfl⟩ : syracuseStep 920339 = 1380509) B1380509
theorem B1379105 : Blo 916578 1379105 := bstep (se 2 (by rfl) ⟨517164, by rfl⟩ : syracuseStep 1379105 = 1034329) B1034329
theorem B920355 : Blo 916578 920355 := bstep (se 1 (by rfl) ⟨690266, by rfl⟩ : syracuseStep 920355 = 1380533) B1380533
theorem B2657069 : Blo 916578 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B1379123 : Blo 916578 1379123 := bstep (se 1 (by rfl) ⟨1034342, by rfl⟩ : syracuseStep 1379123 = 2068685) B2068685
theorem B920371 : Blo 916578 920371 := bstep (se 1 (by rfl) ⟨690278, by rfl⟩ : syracuseStep 920371 = 1380557) B1380557
theorem B920387 : Blo 916578 920387 := bstep (se 1 (by rfl) ⟨690290, by rfl⟩ : syracuseStep 920387 = 1380581) B1380581
theorem B2067281 : Blo 916578 2067281 := bstep (se 2 (by rfl) ⟨775230, by rfl⟩ : syracuseStep 2067281 = 1550461) B1550461
theorem B1379153 : Blo 916578 1379153 := bstep (se 2 (by rfl) ⟨517182, by rfl⟩ : syracuseStep 1379153 = 1034365) B1034365
theorem B920403 : Blo 916578 920403 := bstep (se 1 (by rfl) ⟨690302, by rfl⟩ : syracuseStep 920403 = 1380605) B1380605
theorem B2067299 : Blo 916578 2067299 := bstep (se 1 (by rfl) ⟨1550474, by rfl⟩ : syracuseStep 2067299 = 3100949) B3100949
theorem B1379171 : Blo 916578 1379171 := bstep (se 1 (by rfl) ⟨1034378, by rfl⟩ : syracuseStep 1379171 = 2068757) B2068757
theorem B920419 : Blo 916578 920419 := bstep (se 1 (by rfl) ⟨690314, by rfl⟩ : syracuseStep 920419 = 1380629) B1380629
theorem B920435 : Blo 916578 920435 := bstep (se 1 (by rfl) ⟨690326, by rfl⟩ : syracuseStep 920435 = 1380653) B1380653
theorem B1379201 : Blo 916578 1379201 := bstep (se 2 (by rfl) ⟨517200, by rfl⟩ : syracuseStep 1379201 = 1034401) B1034401
theorem B920451 : Blo 916578 920451 := bstep (se 1 (by rfl) ⟨690338, by rfl⟩ : syracuseStep 920451 = 1380677) B1380677
theorem B1379219 : Blo 916578 1379219 := bstep (se 1 (by rfl) ⟨1034414, by rfl⟩ : syracuseStep 1379219 = 2068829) B2068829
theorem B920467 : Blo 916578 920467 := bstep (se 1 (by rfl) ⟨690350, by rfl⟩ : syracuseStep 920467 = 1380701) B1380701
theorem B920483 : Blo 916578 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B1379249 : Blo 916578 1379249 := bstep (se 2 (by rfl) ⟨517218, by rfl⟩ : syracuseStep 1379249 = 1034437) B1034437
theorem B920499 : Blo 916578 920499 := bstep (se 1 (by rfl) ⟨690374, by rfl⟩ : syracuseStep 920499 = 1380749) B1380749
theorem B1379267 : Blo 916578 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B920515 : Blo 916578 920515 := bstep (se 1 (by rfl) ⟨690386, by rfl⟩ : syracuseStep 920515 = 1380773) B1380773
theorem B920531 : Blo 916578 920531 := bstep (se 1 (by rfl) ⟨690398, by rfl⟩ : syracuseStep 920531 = 1380797) B1380797
theorem B1379297 : Blo 916578 1379297 := bstep (se 2 (by rfl) ⟨517236, by rfl⟩ : syracuseStep 1379297 = 1034473) B1034473
theorem B920547 : Blo 916578 920547 := bstep (se 1 (by rfl) ⟨690410, by rfl⟩ : syracuseStep 920547 = 1380821) B1380821
theorem B1379315 : Blo 916578 1379315 := bstep (se 1 (by rfl) ⟨1034486, by rfl⟩ : syracuseStep 1379315 = 2068973) B2068973
theorem B920563 : Blo 916578 920563 := bstep (se 1 (by rfl) ⟨690422, by rfl⟩ : syracuseStep 920563 = 1380845) B1380845
theorem B1379345 : Blo 916578 1379345 := bstep (se 2 (by rfl) ⟨517254, by rfl⟩ : syracuseStep 1379345 = 1034509) B1034509
theorem B1379363 : Blo 916578 1379363 := bstep (se 1 (by rfl) ⟨1034522, by rfl⟩ : syracuseStep 1379363 = 2069045) B2069045
theorem B1379393 : Blo 916578 1379393 := bstep (se 2 (by rfl) ⟨517272, by rfl⟩ : syracuseStep 1379393 = 1034545) B1034545
theorem B2329681 : Blo 916578 2329681 := bstep (se 2 (by rfl) ⟨873630, by rfl⟩ : syracuseStep 2329681 = 1747261) B1747261
theorem B1379411 : Blo 916578 1379411 := bstep (se 1 (by rfl) ⟨1034558, by rfl⟩ : syracuseStep 1379411 = 2069117) B2069117
theorem B2067569 : Blo 916578 2067569 := bstep (se 2 (by rfl) ⟨775338, by rfl⟩ : syracuseStep 2067569 = 1550677) B1550677
theorem B1379441 : Blo 916578 1379441 := bstep (se 2 (by rfl) ⟨517290, by rfl⟩ : syracuseStep 1379441 = 1034581) B1034581
theorem B2067587 : Blo 916578 2067587 := bstep (se 1 (by rfl) ⟨1550690, by rfl⟩ : syracuseStep 2067587 = 3101381) B3101381
theorem B1379459 : Blo 916578 1379459 := bstep (se 1 (by rfl) ⟨1034594, by rfl⟩ : syracuseStep 1379459 = 2069189) B2069189
theorem B1379489 : Blo 916578 1379489 := bstep (se 2 (by rfl) ⟨517308, by rfl⟩ : syracuseStep 1379489 = 1034617) B1034617
theorem B1379507 : Blo 916578 1379507 := bstep (se 1 (by rfl) ⟨1034630, by rfl⟩ : syracuseStep 1379507 = 2069261) B2069261
theorem B3312845 : Blo 916578 3312845 := bstep (se 3 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 3312845 = 1242317) B1242317
theorem B1379537 : Blo 916578 1379537 := bstep (se 2 (by rfl) ⟨517326, by rfl⟩ : syracuseStep 1379537 = 1034653) B1034653
theorem B1379555 : Blo 916578 1379555 := bstep (se 1 (by rfl) ⟨1034666, by rfl⟩ : syracuseStep 1379555 = 2069333) B2069333
theorem B1379585 : Blo 916578 1379585 := bstep (se 2 (by rfl) ⟨517344, by rfl⟩ : syracuseStep 1379585 = 1034689) B1034689
theorem B1674499 : Blo 916578 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B1379603 : Blo 916578 1379603 := bstep (se 1 (by rfl) ⟨1034702, by rfl⟩ : syracuseStep 1379603 = 2069405) B2069405
theorem B1379633 : Blo 916578 1379633 := bstep (se 2 (by rfl) ⟨517362, by rfl⟩ : syracuseStep 1379633 = 1034725) B1034725
theorem B1379651 : Blo 916578 1379651 := bstep (se 1 (by rfl) ⟨1034738, by rfl⟩ : syracuseStep 1379651 = 2069477) B2069477
theorem B1379681 : Blo 916578 1379681 := bstep (se 2 (by rfl) ⟨517380, by rfl⟩ : syracuseStep 1379681 = 1034761) B1034761
theorem B2329955 : Blo 916578 2329955 := bstep (se 1 (by rfl) ⟨1747466, by rfl⟩ : syracuseStep 2329955 = 3494933) B3494933
theorem B11767153 : Blo 916578 11767153 := bstep (se 2 (by rfl) ⟨4412682, by rfl⟩ : syracuseStep 11767153 = 8825365) B8825365
theorem B1379699 : Blo 916578 1379699 := bstep (se 1 (by rfl) ⟨1034774, by rfl⟩ : syracuseStep 1379699 = 2069549) B2069549
theorem B2067857 : Blo 916578 2067857 := bstep (se 2 (by rfl) ⟨775446, by rfl⟩ : syracuseStep 2067857 = 1550893) B1550893
theorem B1379729 : Blo 916578 1379729 := bstep (se 2 (by rfl) ⟨517398, by rfl⟩ : syracuseStep 1379729 = 1034797) B1034797
theorem B2067875 : Blo 916578 2067875 := bstep (se 1 (by rfl) ⟨1550906, by rfl⟩ : syracuseStep 2067875 = 3101813) B3101813
theorem B1379747 : Blo 916578 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B1379777 : Blo 916578 1379777 := bstep (se 2 (by rfl) ⟨517416, by rfl⟩ : syracuseStep 1379777 = 1034833) B1034833
theorem B1379795 : Blo 916578 1379795 := bstep (se 1 (by rfl) ⟨1034846, by rfl⟩ : syracuseStep 1379795 = 2069693) B2069693
theorem B1379825 : Blo 916578 1379825 := bstep (se 2 (by rfl) ⟨517434, by rfl⟩ : syracuseStep 1379825 = 1034869) B1034869
theorem B1379843 : Blo 916578 1379843 := bstep (se 1 (by rfl) ⟨1034882, by rfl⟩ : syracuseStep 1379843 = 2069765) B2069765
theorem B1740305 : Blo 916578 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B1379873 : Blo 916578 1379873 := bstep (se 2 (by rfl) ⟨517452, by rfl⟩ : syracuseStep 1379873 = 1034905) B1034905
theorem B2330147 : Blo 916578 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B4656689 : Blo 916578 4656689 := bstep (se 2 (by rfl) ⟨1746258, by rfl⟩ : syracuseStep 4656689 = 3492517) B3492517
theorem B1379891 : Blo 916578 1379891 := bstep (se 1 (by rfl) ⟨1034918, by rfl⟩ : syracuseStep 1379891 = 2069837) B2069837
theorem B1379921 : Blo 916578 1379921 := bstep (se 2 (by rfl) ⟨517470, by rfl⟩ : syracuseStep 1379921 = 1034941) B1034941
theorem B1379939 : Blo 916578 1379939 := bstep (se 1 (by rfl) ⟨1034954, by rfl⟩ : syracuseStep 1379939 = 2069909) B2069909
theorem B1379969 : Blo 916578 1379969 := bstep (se 2 (by rfl) ⟨517488, by rfl⟩ : syracuseStep 1379969 = 1034977) B1034977
theorem B1379987 : Blo 916578 1379987 := bstep (se 1 (by rfl) ⟨1034990, by rfl⟩ : syracuseStep 1379987 = 2069981) B2069981
theorem B2068145 : Blo 916578 2068145 := bstep (se 2 (by rfl) ⟨775554, by rfl⟩ : syracuseStep 2068145 = 1551109) B1551109
theorem B1380017 : Blo 916578 1380017 := bstep (se 2 (by rfl) ⟨517506, by rfl⟩ : syracuseStep 1380017 = 1035013) B1035013
theorem B2068163 : Blo 916578 2068163 := bstep (se 1 (by rfl) ⟨1551122, by rfl⟩ : syracuseStep 2068163 = 3102245) B3102245
theorem B1380035 : Blo 916578 1380035 := bstep (se 1 (by rfl) ⟨1035026, by rfl⟩ : syracuseStep 1380035 = 2070053) B2070053
theorem B1380065 : Blo 916578 1380065 := bstep (se 2 (by rfl) ⟨517524, by rfl⟩ : syracuseStep 1380065 = 1035049) B1035049
theorem B1380083 : Blo 916578 1380083 := bstep (se 1 (by rfl) ⟨1035062, by rfl⟩ : syracuseStep 1380083 = 2070125) B2070125
theorem B1380113 : Blo 916578 1380113 := bstep (se 2 (by rfl) ⟨517542, by rfl⟩ : syracuseStep 1380113 = 1035085) B1035085
theorem B1380131 : Blo 916578 1380131 := bstep (se 1 (by rfl) ⟨1035098, by rfl⟩ : syracuseStep 1380131 = 2070197) B2070197
theorem B1380161 : Blo 916578 1380161 := bstep (se 2 (by rfl) ⟨517560, by rfl⟩ : syracuseStep 1380161 = 1035121) B1035121
theorem B1380179 : Blo 916578 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B1380209 : Blo 916578 1380209 := bstep (se 2 (by rfl) ⟨517578, by rfl⟩ : syracuseStep 1380209 = 1035157) B1035157
theorem B1380227 : Blo 916578 1380227 := bstep (se 1 (by rfl) ⟨1035170, by rfl⟩ : syracuseStep 1380227 = 2070341) B2070341
theorem B1380257 : Blo 916578 1380257 := bstep (se 2 (by rfl) ⟨517596, by rfl⟩ : syracuseStep 1380257 = 1035193) B1035193
theorem B1380275 : Blo 916578 1380275 := bstep (se 1 (by rfl) ⟨1035206, by rfl⟩ : syracuseStep 1380275 = 2070413) B2070413
theorem B2068433 : Blo 916578 2068433 := bstep (se 2 (by rfl) ⟨775662, by rfl⟩ : syracuseStep 2068433 = 1551325) B1551325
theorem B1380305 : Blo 916578 1380305 := bstep (se 2 (by rfl) ⟨517614, by rfl⟩ : syracuseStep 1380305 = 1035229) B1035229
theorem B2068451 : Blo 916578 2068451 := bstep (se 1 (by rfl) ⟨1551338, by rfl⟩ : syracuseStep 2068451 = 3102677) B3102677
theorem B1380323 : Blo 916578 1380323 := bstep (se 1 (by rfl) ⟨1035242, by rfl⟩ : syracuseStep 1380323 = 2070485) B2070485
theorem B1380353 : Blo 916578 1380353 := bstep (se 2 (by rfl) ⟨517632, by rfl⟩ : syracuseStep 1380353 = 1035265) B1035265
theorem B1380371 : Blo 916578 1380371 := bstep (se 1 (by rfl) ⟨1035278, by rfl⟩ : syracuseStep 1380371 = 2070557) B2070557
theorem B1380401 : Blo 916578 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B1380419 : Blo 916578 1380419 := bstep (se 1 (by rfl) ⟨1035314, by rfl⟩ : syracuseStep 1380419 = 2070629) B2070629
theorem B1380449 : Blo 916578 1380449 := bstep (se 2 (by rfl) ⟨517668, by rfl⟩ : syracuseStep 1380449 = 1035337) B1035337
theorem B1380467 : Blo 916578 1380467 := bstep (se 1 (by rfl) ⟨1035350, by rfl⟩ : syracuseStep 1380467 = 2070701) B2070701
theorem B1380497 : Blo 916578 1380497 := bstep (se 2 (by rfl) ⟨517686, by rfl⟩ : syracuseStep 1380497 = 1035373) B1035373
theorem B1380515 : Blo 916578 1380515 := bstep (se 1 (by rfl) ⟨1035386, by rfl⟩ : syracuseStep 1380515 = 2070773) B2070773
theorem B1380545 : Blo 916578 1380545 := bstep (se 2 (by rfl) ⟨517704, by rfl⟩ : syracuseStep 1380545 = 1035409) B1035409
theorem B1380563 : Blo 916578 1380563 := bstep (se 1 (by rfl) ⟨1035422, by rfl⟩ : syracuseStep 1380563 = 2070845) B2070845
theorem B1741027 : Blo 916578 1741027 := bstep (se 1 (by rfl) ⟨1305770, by rfl⟩ : syracuseStep 1741027 = 2611541) B2611541
theorem B2068721 : Blo 916578 2068721 := bstep (se 2 (by rfl) ⟨775770, by rfl⟩ : syracuseStep 2068721 = 1551541) B1551541
theorem B1380593 : Blo 916578 1380593 := bstep (se 2 (by rfl) ⟨517722, by rfl⟩ : syracuseStep 1380593 = 1035445) B1035445
theorem B2068739 : Blo 916578 2068739 := bstep (se 1 (by rfl) ⟨1551554, by rfl⟩ : syracuseStep 2068739 = 3103109) B3103109
theorem B1380611 : Blo 916578 1380611 := bstep (se 1 (by rfl) ⟨1035458, by rfl⟩ : syracuseStep 1380611 = 2070917) B2070917
theorem B1380641 : Blo 916578 1380641 := bstep (se 2 (by rfl) ⟨517740, by rfl⟩ : syracuseStep 1380641 = 1035481) B1035481
theorem B1380659 : Blo 916578 1380659 := bstep (se 1 (by rfl) ⟨1035494, by rfl⟩ : syracuseStep 1380659 = 2070989) B2070989
theorem B1380689 : Blo 916578 1380689 := bstep (se 2 (by rfl) ⟨517758, by rfl⟩ : syracuseStep 1380689 = 1035517) B1035517
theorem B1380707 : Blo 916578 1380707 := bstep (se 1 (by rfl) ⟨1035530, by rfl⟩ : syracuseStep 1380707 = 2071061) B2071061
theorem B1380737 : Blo 916578 1380737 := bstep (se 2 (by rfl) ⟨517776, by rfl⟩ : syracuseStep 1380737 = 1035553) B1035553
theorem B1380755 : Blo 916578 1380755 := bstep (se 1 (by rfl) ⟨1035566, by rfl⟩ : syracuseStep 1380755 = 2071133) B2071133
theorem B1380785 : Blo 916578 1380785 := bstep (se 2 (by rfl) ⟨517794, by rfl⟩ : syracuseStep 1380785 = 1035589) B1035589
theorem B1380803 : Blo 916578 1380803 := bstep (se 1 (by rfl) ⟨1035602, by rfl⟩ : syracuseStep 1380803 = 2071205) B2071205
theorem B1380833 : Blo 916578 1380833 := bstep (se 2 (by rfl) ⟨517812, by rfl⟩ : syracuseStep 1380833 = 1035625) B1035625
theorem B2789873 : Blo 916578 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B1380851 : Blo 916578 1380851 := bstep (se 1 (by rfl) ⟨1035638, by rfl⟩ : syracuseStep 1380851 = 2071277) B2071277
theorem B2069009 : Blo 916578 2069009 := bstep (se 2 (by rfl) ⟨775878, by rfl⟩ : syracuseStep 2069009 = 1551757) B1551757
theorem B2069027 : Blo 916578 2069027 := bstep (se 1 (by rfl) ⟨1551770, by rfl⟩ : syracuseStep 2069027 = 3103541) B3103541
theorem B15340085 : Blo 916578 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B6984305 : Blo 916578 6984305 := bstep (se 2 (by rfl) ⟨2619114, by rfl⟩ : syracuseStep 6984305 = 5238229) B5238229
theorem B7180913 : Blo 916578 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B1741475 : Blo 916578 1741475 := bstep (se 1 (by rfl) ⟨1306106, by rfl⟩ : syracuseStep 1741475 = 2612213) B2612213
theorem B2069297 : Blo 916578 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B2069315 : Blo 916578 2069315 := bstep (se 1 (by rfl) ⟨1551986, by rfl⟩ : syracuseStep 2069315 = 3103973) B3103973
theorem B1741763 : Blo 916578 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B4658147 : Blo 916578 4658147 := bstep (se 1 (by rfl) ⟨3493610, by rfl⟩ : syracuseStep 4658147 = 6987221) B6987221
theorem B2069585 : Blo 916578 2069585 := bstep (se 2 (by rfl) ⟨776094, by rfl⟩ : syracuseStep 2069585 = 1552189) B1552189
theorem B2069603 : Blo 916578 2069603 := bstep (se 1 (by rfl) ⟨1552202, by rfl⟩ : syracuseStep 2069603 = 3104405) B3104405
theorem B3970225 : Blo 916578 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B2266289 : Blo 916578 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B2069873 : Blo 916578 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B2069891 : Blo 916578 2069891 := bstep (se 1 (by rfl) ⟨1552418, by rfl⟩ : syracuseStep 2069891 = 3104837) B3104837
theorem B12719501 : Blo 916578 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B2070161 : Blo 916578 2070161 := bstep (se 2 (by rfl) ⟨776310, by rfl⟩ : syracuseStep 2070161 = 1552621) B1552621
theorem B2070179 : Blo 916578 2070179 := bstep (se 1 (by rfl) ⟨1552634, by rfl⟩ : syracuseStep 2070179 = 3105269) B3105269
theorem B4658957 : Blo 916578 4658957 := bstep (se 3 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 4658957 = 1747109) B1747109
theorem B1742705 : Blo 916578 1742705 := bstep (se 2 (by rfl) ⟨653514, by rfl⟩ : syracuseStep 1742705 = 1307029) B1307029
theorem B17667953 : Blo 916578 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B2070449 : Blo 916578 2070449 := bstep (se 2 (by rfl) ⟨776418, by rfl⟩ : syracuseStep 2070449 = 1552837) B1552837
theorem B2070467 : Blo 916578 2070467 := bstep (se 1 (by rfl) ⟨1552850, by rfl⟩ : syracuseStep 2070467 = 3105701) B3105701
theorem B10623089 : Blo 916578 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B2070737 : Blo 916578 2070737 := bstep (se 2 (by rfl) ⟨776526, by rfl⟩ : syracuseStep 2070737 = 1553053) B1553053
theorem B2070755 : Blo 916578 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B8821061 : Blo 916578 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B16783757 : Blo 916578 16783757 := bstep (se 3 (by rfl) ⟨3146954, by rfl⟩ : syracuseStep 16783757 = 6293909) B6293909
theorem B2071025 : Blo 916578 2071025 := bstep (se 2 (by rfl) ⟨776634, by rfl⟩ : syracuseStep 2071025 = 1553269) B1553269
theorem B2071043 : Blo 916578 2071043 := bstep (se 1 (by rfl) ⟨1553282, by rfl⟩ : syracuseStep 2071043 = 3106565) B3106565
theorem B1546769 : Blo 916578 1546769 := bstep (se 2 (by rfl) ⟨580038, by rfl⟩ : syracuseStep 1546769 = 1160077) B1160077
theorem B1677859 : Blo 916578 1677859 := bstep (se 1 (by rfl) ⟨1258394, by rfl⟩ : syracuseStep 1677859 = 2516789) B2516789
theorem B9935459 : Blo 916578 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B1546897 : Blo 916578 1546897 := bstep (se 2 (by rfl) ⟨580086, by rfl⟩ : syracuseStep 1546897 = 1160173) B1160173
theorem B2792099 : Blo 916578 2792099 := bstep (se 1 (by rfl) ⟨2094074, by rfl⟩ : syracuseStep 2792099 = 4188149) B4188149
theorem B1546931 : Blo 916578 1546931 := bstep (se 1 (by rfl) ⟨1160198, by rfl⟩ : syracuseStep 1546931 = 2320397) B2320397
theorem B1743601 : Blo 916578 1743601 := bstep (se 2 (by rfl) ⟨653850, by rfl⟩ : syracuseStep 1743601 = 1307701) B1307701
theorem B1547059 : Blo 916578 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B15276853 : Blo 916578 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B1743761 : Blo 916578 1743761 := bstep (se 2 (by rfl) ⟨653910, by rfl⟩ : syracuseStep 1743761 = 1307821) B1307821
theorem B1547201 : Blo 916578 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B1547329 : Blo 916578 1547329 := bstep (se 2 (by rfl) ⟨580248, by rfl⟩ : syracuseStep 1547329 = 1160497) B1160497
theorem B1547363 : Blo 916578 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B1547491 : Blo 916578 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B1744163 : Blo 916578 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B1547633 : Blo 916578 1547633 := bstep (se 2 (by rfl) ⟨580362, by rfl⟩ : syracuseStep 1547633 = 1160725) B1160725
theorem B1547761 : Blo 916578 1547761 := bstep (se 2 (by rfl) ⟨580410, by rfl⟩ : syracuseStep 1547761 = 1160821) B1160821
theorem B1547795 : Blo 916578 1547795 := bstep (se 1 (by rfl) ⟨1160846, by rfl⟩ : syracuseStep 1547795 = 2321693) B2321693
theorem B7839301 : Blo 916578 7839301 := bstep (se 4 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 7839301 = 1469869) B1469869
theorem B1547923 : Blo 916578 1547923 := bstep (se 1 (by rfl) ⟨1160942, by rfl⟩ : syracuseStep 1547923 = 2321885) B2321885
theorem B2793133 : Blo 916578 2793133 := bstep (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) B1047425
theorem B1548065 : Blo 916578 1548065 := bstep (se 2 (by rfl) ⟨580524, by rfl⟩ : syracuseStep 1548065 = 1161049) B1161049
theorem B5447459 : Blo 916578 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B1548193 : Blo 916578 1548193 := bstep (se 2 (by rfl) ⟨580572, by rfl⟩ : syracuseStep 1548193 = 1161145) B1161145
theorem B1548227 : Blo 916578 1548227 := bstep (se 1 (by rfl) ⟨1161170, by rfl⟩ : syracuseStep 1548227 = 2322341) B2322341
theorem B3481613 : Blo 916578 3481613 := bstep (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) B1305605
theorem B1548355 : Blo 916578 1548355 := bstep (se 1 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 1548355 = 2322533) B2322533
theorem B26517617 : Blo 916578 26517617 := bstep (se 2 (by rfl) ⟨9944106, by rfl⟩ : syracuseStep 26517617 = 19888213) B19888213
theorem B1745059 : Blo 916578 1745059 := bstep (se 1 (by rfl) ⟨1308794, by rfl⟩ : syracuseStep 1745059 = 2617589) B2617589
theorem B2203843 : Blo 916578 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B1548497 : Blo 916578 1548497 := bstep (se 2 (by rfl) ⟨580686, by rfl⟩ : syracuseStep 1548497 = 1161373) B1161373
theorem B1745219 : Blo 916578 1745219 := bstep (se 1 (by rfl) ⟨1308914, by rfl⟩ : syracuseStep 1745219 = 2617829) B2617829
theorem B1548625 : Blo 916578 1548625 := bstep (se 2 (by rfl) ⟨580734, by rfl⟩ : syracuseStep 1548625 = 1161469) B1161469
theorem B1548659 : Blo 916578 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B1548787 : Blo 916578 1548787 := bstep (se 1 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 1548787 = 2323181) B2323181
theorem B11772485 : Blo 916578 11772485 := bstep (se 4 (by rfl) ⟨1103670, by rfl⟩ : syracuseStep 11772485 = 2207341) B2207341
theorem B1548929 : Blo 916578 1548929 := bstep (se 2 (by rfl) ⟨580848, by rfl⟩ : syracuseStep 1548929 = 1161697) B1161697
theorem B15901381 : Blo 916578 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B5874403 : Blo 916578 5874403 := bstep (se 1 (by rfl) ⟨4405802, by rfl⟩ : syracuseStep 5874403 = 8811605) B8811605
theorem B1549057 : Blo 916578 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B1549091 : Blo 916578 1549091 := bstep (se 1 (by rfl) ⟨1161818, by rfl⟩ : syracuseStep 1549091 = 2323637) B2323637
theorem B1549219 : Blo 916578 1549219 := bstep (se 1 (by rfl) ⟨1161914, by rfl⟩ : syracuseStep 1549219 = 2323829) B2323829
theorem B44704709 : Blo 916578 44704709 := bstep (se 4 (by rfl) ⟨4191066, by rfl⟩ : syracuseStep 44704709 = 8382133) B8382133
theorem B1549361 : Blo 916578 1549361 := bstep (se 2 (by rfl) ⟨581010, by rfl⟩ : syracuseStep 1549361 = 1162021) B1162021
theorem B1549489 : Blo 916578 1549489 := bstep (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) B1162117
theorem B1549523 : Blo 916578 1549523 := bstep (se 1 (by rfl) ⟨1162142, by rfl⟩ : syracuseStep 1549523 = 2324285) B2324285
theorem B1549651 : Blo 916578 1549651 := bstep (se 1 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 1549651 = 2324477) B2324477
theorem B1746289 : Blo 916578 1746289 := bstep (se 2 (by rfl) ⟨654858, by rfl⟩ : syracuseStep 1746289 = 1309717) B1309717
theorem B2205073 : Blo 916578 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B1549793 : Blo 916578 1549793 := bstep (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) B1162345
theorem B1549921 : Blo 916578 1549921 := bstep (se 2 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 1549921 = 1162441) B1162441
theorem B1549955 : Blo 916578 1549955 := bstep (se 1 (by rfl) ⟨1162466, by rfl⟩ : syracuseStep 1549955 = 2324933) B2324933
theorem B1550083 : Blo 916578 1550083 := bstep (se 1 (by rfl) ⟨1162562, by rfl⟩ : syracuseStep 1550083 = 2325125) B2325125
theorem B1550225 : Blo 916578 1550225 := bstep (se 2 (by rfl) ⟨581334, by rfl⟩ : syracuseStep 1550225 = 1162669) B1162669
theorem B1550353 : Blo 916578 1550353 := bstep (se 2 (by rfl) ⟨581382, by rfl⟩ : syracuseStep 1550353 = 1162765) B1162765
theorem B3188753 : Blo 916578 3188753 := bstep (se 2 (by rfl) ⟨1195782, by rfl⟩ : syracuseStep 3188753 = 2391565) B2391565
theorem B1550387 : Blo 916578 1550387 := bstep (se 1 (by rfl) ⟨1162790, by rfl⟩ : syracuseStep 1550387 = 2325581) B2325581
theorem B1550515 : Blo 916578 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B1550657 : Blo 916578 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B3189073 : Blo 916578 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B1747345 : Blo 916578 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1550785 : Blo 916578 1550785 := bstep (se 2 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 1550785 = 1163089) B1163089
theorem B1550819 : Blo 916578 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1550947 : Blo 916578 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B5876401 : Blo 916578 5876401 := bstep (se 2 (by rfl) ⟨2203650, by rfl⟩ : syracuseStep 5876401 = 4407301) B4407301
theorem B1551089 : Blo 916578 1551089 := bstep (se 2 (by rfl) ⟨581658, by rfl⟩ : syracuseStep 1551089 = 1163317) B1163317
theorem B3484529 : Blo 916578 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B1551217 : Blo 916578 1551217 := bstep (se 2 (by rfl) ⟨581706, by rfl⟩ : syracuseStep 1551217 = 1163413) B1163413
theorem B1551251 : Blo 916578 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1551379 : Blo 916578 1551379 := bstep (se 1 (by rfl) ⟨1163534, by rfl⟩ : syracuseStep 1551379 = 2327069) B2327069
theorem B2796611 : Blo 916578 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1551521 : Blo 916578 1551521 := bstep (se 2 (by rfl) ⟨581820, by rfl⟩ : syracuseStep 1551521 = 1163641) B1163641
theorem B1551649 : Blo 916578 1551649 := bstep (se 2 (by rfl) ⟨581868, by rfl⟩ : syracuseStep 1551649 = 1163737) B1163737
theorem B1551683 : Blo 916578 1551683 := bstep (se 1 (by rfl) ⟨1163762, by rfl⟩ : syracuseStep 1551683 = 2327525) B2327525
theorem B929155 : Blo 916578 929155 := bstep (se 1 (by rfl) ⟨696866, by rfl⟩ : syracuseStep 929155 = 1393733) B1393733
theorem B1551811 : Blo 916578 1551811 := bstep (se 1 (by rfl) ⟨1163858, by rfl⟩ : syracuseStep 1551811 = 2327717) B2327717
theorem B1551953 : Blo 916578 1551953 := bstep (se 2 (by rfl) ⟨581982, by rfl⟩ : syracuseStep 1551953 = 1163965) B1163965
theorem B1552081 : Blo 916578 1552081 := bstep (se 2 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 1552081 = 1164061) B1164061
theorem B1552115 : Blo 916578 1552115 := bstep (se 1 (by rfl) ⟨1164086, by rfl⟩ : syracuseStep 1552115 = 2328173) B2328173
theorem B1552243 : Blo 916578 1552243 := bstep (se 1 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 1552243 = 2328365) B2328365
theorem B1322993 : Blo 916578 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B1552385 : Blo 916578 1552385 := bstep (se 2 (by rfl) ⟨582144, by rfl⟩ : syracuseStep 1552385 = 1164289) B1164289
theorem B4960291 : Blo 916578 4960291 := bstep (se 1 (by rfl) ⟨3720218, by rfl⟩ : syracuseStep 4960291 = 7440437) B7440437
theorem B1552513 : Blo 916578 1552513 := bstep (se 2 (by rfl) ⟨582192, by rfl⟩ : syracuseStep 1552513 = 1164385) B1164385
theorem B1552547 : Blo 916578 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B3485987 : Blo 916578 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B1552675 : Blo 916578 1552675 := bstep (se 1 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 1552675 = 2329013) B2329013
theorem B2208131 : Blo 916578 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B1552817 : Blo 916578 1552817 := bstep (se 2 (by rfl) ⟨582306, by rfl⟩ : syracuseStep 1552817 = 1164613) B1164613
theorem B1552945 : Blo 916578 1552945 := bstep (se 2 (by rfl) ⟨582354, by rfl⟩ : syracuseStep 1552945 = 1164709) B1164709
theorem B930355 : Blo 916578 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B1552979 : Blo 916578 1552979 := bstep (se 1 (by rfl) ⟨1164734, by rfl⟩ : syracuseStep 1552979 = 2329469) B2329469
theorem B47657585 : Blo 916578 47657585 := bstep (se 2 (by rfl) ⟨17871594, by rfl⟩ : syracuseStep 47657585 = 35743189) B35743189
theorem B1553107 : Blo 916578 1553107 := bstep (se 1 (by rfl) ⟨1164830, by rfl⟩ : syracuseStep 1553107 = 2329661) B2329661
theorem B1553249 : Blo 916578 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B2798435 : Blo 916578 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B13218673 : Blo 916578 13218673 := bstep (se 2 (by rfl) ⟨4957002, by rfl⟩ : syracuseStep 13218673 = 9914005) B9914005
theorem B1553377 : Blo 916578 1553377 := bstep (se 2 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 1553377 = 1165033) B1165033
theorem B1553411 : Blo 916578 1553411 := bstep (se 1 (by rfl) ⟨1165058, by rfl⟩ : syracuseStep 1553411 = 2330117) B2330117
theorem B930995 : Blo 916578 930995 := bstep (se 1 (by rfl) ⟨698246, by rfl⟩ : syracuseStep 930995 = 1396493) B1396493
theorem B3093713 : Blo 916578 3093713 := bstep (se 2 (by rfl) ⟨1160142, by rfl⟩ : syracuseStep 3093713 = 2320285) B2320285
theorem B2208977 : Blo 916578 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B16954595 : Blo 916578 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B3486989 : Blo 916578 3486989 := bstep (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) B1307621
theorem B1160563 : Blo 916578 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B2209187 : Blo 916578 2209187 := bstep (se 1 (by rfl) ⟨1656890, by rfl⟩ : syracuseStep 2209187 = 3313781) B3313781
theorem B1160659 : Blo 916578 1160659 := bstep (se 1 (by rfl) ⟨870494, by rfl⟩ : syracuseStep 1160659 = 1740989) B1740989
theorem B3094253 : Blo 916578 3094253 := bstep (se 3 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 3094253 = 1160345) B1160345
theorem B3094307 : Blo 916578 3094307 := bstep (se 1 (by rfl) ⟨2320730, by rfl⟩ : syracuseStep 3094307 = 4641461) B4641461
theorem B1161155 : Blo 916578 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B5027789 : Blo 916578 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B8501233 : Blo 916578 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B3094577 : Blo 916578 3094577 := bstep (se 2 (by rfl) ⟨1160466, by rfl⟩ : syracuseStep 3094577 = 2320933) B2320933
theorem B3095117 : Blo 916578 3095117 := bstep (se 3 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 3095117 = 1160669) B1160669
theorem B2210417 : Blo 916578 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B3095171 : Blo 916578 3095171 := bstep (se 1 (by rfl) ⟨2321378, by rfl⟩ : syracuseStep 3095171 = 4642757) B4642757
theorem B1161859 : Blo 916578 1161859 := bstep (se 1 (by rfl) ⟨871394, by rfl⟩ : syracuseStep 1161859 = 1742789) B1742789
theorem B1161955 : Blo 916578 1161955 := bstep (se 1 (by rfl) ⟨871466, by rfl⟩ : syracuseStep 1161955 = 1742933) B1742933
theorem B1653539 : Blo 916578 1653539 := bstep (se 1 (by rfl) ⟨1240154, by rfl⟩ : syracuseStep 1653539 = 2480309) B2480309
theorem B2210609 : Blo 916578 2210609 := bstep (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) B1657957
theorem B3095441 : Blo 916578 3095441 := bstep (se 2 (by rfl) ⟨1160790, by rfl⟩ : syracuseStep 3095441 = 2321581) B2321581
theorem B1031251 : Blo 916578 1031251 := bstep (se 1 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 1031251 = 1546877) B1546877
theorem B1162451 : Blo 916578 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1031395 : Blo 916578 1031395 := bstep (se 1 (by rfl) ⟨773546, by rfl⟩ : syracuseStep 1031395 = 1547093) B1547093
theorem B1490179 : Blo 916578 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B3489101 : Blo 916578 3489101 := bstep (se 3 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 3489101 = 1308413) B1308413
theorem B1031539 : Blo 916578 1031539 := bstep (se 1 (by rfl) ⟨773654, by rfl⟩ : syracuseStep 1031539 = 1547309) B1547309
theorem B4406669 : Blo 916578 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B3095981 : Blo 916578 3095981 := bstep (se 3 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 3095981 = 1160993) B1160993
theorem B3096035 : Blo 916578 3096035 := bstep (se 1 (by rfl) ⟨2322026, by rfl⟩ : syracuseStep 3096035 = 4644053) B4644053
theorem B1031683 : Blo 916578 1031683 := bstep (se 1 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 1031683 = 1547525) B1547525
theorem B1031827 : Blo 916578 1031827 := bstep (se 1 (by rfl) ⟨773870, by rfl⟩ : syracuseStep 1031827 = 1547741) B1547741
theorem B3096305 : Blo 916578 3096305 := bstep (se 2 (by rfl) ⟨1161114, by rfl⟩ : syracuseStep 3096305 = 2322229) B2322229
theorem B1031971 : Blo 916578 1031971 := bstep (se 1 (by rfl) ⟨773978, by rfl⟩ : syracuseStep 1031971 = 1547957) B1547957
theorem B5881733 : Blo 916578 5881733 := bstep (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) B1102825
theorem B1163155 : Blo 916578 1163155 := bstep (se 1 (by rfl) ⟨872366, by rfl⟩ : syracuseStep 1163155 = 1744733) B1744733
theorem B1032115 : Blo 916578 1032115 := bstep (se 1 (by rfl) ⟨774086, by rfl⟩ : syracuseStep 1032115 = 1548173) B1548173
theorem B1163251 : Blo 916578 1163251 := bstep (se 1 (by rfl) ⟨872438, by rfl⟩ : syracuseStep 1163251 = 1744877) B1744877
theorem B1032259 : Blo 916578 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B5226565 : Blo 916578 5226565 := bstep (se 4 (by rfl) ⟨489990, by rfl⟩ : syracuseStep 5226565 = 979981) B979981
theorem B7848049 : Blo 916578 7848049 := bstep (se 2 (by rfl) ⟨2943018, by rfl⟩ : syracuseStep 7848049 = 5886037) B5886037
theorem B3489905 : Blo 916578 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B1032403 : Blo 916578 1032403 := bstep (se 1 (by rfl) ⟨774302, by rfl⟩ : syracuseStep 1032403 = 1548605) B1548605
theorem B3096845 : Blo 916578 3096845 := bstep (se 3 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 3096845 = 1161317) B1161317
theorem B3096899 : Blo 916578 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B11911493 : Blo 916578 11911493 := bstep (se 4 (by rfl) ⟨1116702, by rfl⟩ : syracuseStep 11911493 = 2233405) B2233405
theorem B1032547 : Blo 916578 1032547 := bstep (se 1 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 1032547 = 1548821) B1548821
theorem B1163747 : Blo 916578 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B1032691 : Blo 916578 1032691 := bstep (se 1 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 1032691 = 1549037) B1549037
theorem B84754997 : Blo 916578 84754997 := bstep (se 5 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 84754997 = 7945781) B7945781
theorem B3097169 : Blo 916578 3097169 := bstep (se 2 (by rfl) ⟨1161438, by rfl⟩ : syracuseStep 3097169 = 2322877) B2322877
theorem B1032835 : Blo 916578 1032835 := bstep (se 1 (by rfl) ⟨774626, by rfl⟩ : syracuseStep 1032835 = 1549253) B1549253
theorem B3490573 : Blo 916578 3490573 := bstep (se 3 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 3490573 = 1308965) B1308965
theorem B1032979 : Blo 916578 1032979 := bstep (se 1 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 1032979 = 1549469) B1549469
theorem B3720077 : Blo 916578 3720077 := bstep (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) B1395029
theorem B1196947 : Blo 916578 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1033123 : Blo 916578 1033123 := bstep (se 1 (by rfl) ⟨774842, by rfl⟩ : syracuseStep 1033123 = 1549685) B1549685
theorem B1328113 : Blo 916578 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B3916849 : Blo 916578 3916849 := bstep (se 2 (by rfl) ⟨1468818, by rfl⟩ : syracuseStep 3916849 = 2937637) B2937637
theorem B1033267 : Blo 916578 1033267 := bstep (se 1 (by rfl) ⟨774950, by rfl⟩ : syracuseStep 1033267 = 1549901) B1549901
theorem B3097709 : Blo 916578 3097709 := bstep (se 3 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 3097709 = 1161641) B1161641
theorem B3097763 : Blo 916578 3097763 := bstep (se 1 (by rfl) ⟨2323322, by rfl⟩ : syracuseStep 3097763 = 4646645) B4646645
theorem B1164451 : Blo 916578 1164451 := bstep (se 1 (by rfl) ⟨873338, by rfl⟩ : syracuseStep 1164451 = 1746677) B1746677
theorem B1230001 : Blo 916578 1230001 := bstep (se 2 (by rfl) ⟨461250, by rfl⟩ : syracuseStep 1230001 = 922501) B922501
theorem B1033411 : Blo 916578 1033411 := bstep (se 1 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 1033411 = 1550117) B1550117
theorem B1164547 : Blo 916578 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B1033555 : Blo 916578 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B3098033 : Blo 916578 3098033 := bstep (se 2 (by rfl) ⟨1161762, by rfl⟩ : syracuseStep 3098033 = 2323525) B2323525
theorem B1033699 : Blo 916578 1033699 := bstep (se 1 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 1033699 = 1550549) B1550549
theorem B2835953 : Blo 916578 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B3491363 : Blo 916578 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B1033843 : Blo 916578 1033843 := bstep (se 1 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 1033843 = 1550765) B1550765
theorem B1165043 : Blo 916578 1165043 := bstep (se 1 (by rfl) ⟨873782, by rfl⟩ : syracuseStep 1165043 = 1747565) B1747565
theorem B1033987 : Blo 916578 1033987 := bstep (se 1 (by rfl) ⟨775490, by rfl⟩ : syracuseStep 1033987 = 1550981) B1550981
theorem B1034131 : Blo 916578 1034131 := bstep (se 1 (by rfl) ⟨775598, by rfl⟩ : syracuseStep 1034131 = 1551197) B1551197
theorem B3098573 : Blo 916578 3098573 := bstep (se 3 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 3098573 = 1161965) B1161965
theorem B3098627 : Blo 916578 3098627 := bstep (se 1 (by rfl) ⟨2323970, by rfl⟩ : syracuseStep 3098627 = 4647941) B4647941
theorem B5228549 : Blo 916578 5228549 := bstep (se 4 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 5228549 = 980353) B980353
theorem B1034275 : Blo 916578 1034275 := bstep (se 1 (by rfl) ⟨775706, by rfl⟩ : syracuseStep 1034275 = 1551413) B1551413
theorem B3492017 : Blo 916578 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B1034419 : Blo 916578 1034419 := bstep (se 1 (by rfl) ⟨775814, by rfl⟩ : syracuseStep 1034419 = 1551629) B1551629
theorem B3098897 : Blo 916578 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B1034563 : Blo 916578 1034563 := bstep (se 1 (by rfl) ⟨775922, by rfl⟩ : syracuseStep 1034563 = 1551845) B1551845
theorem B1657265 : Blo 916578 1657265 := bstep (se 2 (by rfl) ⟨621474, by rfl⟩ : syracuseStep 1657265 = 1242949) B1242949
theorem B1034707 : Blo 916578 1034707 := bstep (se 1 (by rfl) ⟨776030, by rfl⟩ : syracuseStep 1034707 = 1552061) B1552061
theorem B9423373 : Blo 916578 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B1034851 : Blo 916578 1034851 := bstep (se 1 (by rfl) ⟨776138, by rfl⟩ : syracuseStep 1034851 = 1552277) B1552277
theorem B1034995 : Blo 916578 1034995 := bstep (se 1 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 1034995 = 1552493) B1552493
theorem B3099437 : Blo 916578 3099437 := bstep (se 3 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 3099437 = 1162289) B1162289
theorem B3099491 : Blo 916578 3099491 := bstep (se 1 (by rfl) ⟨2324618, by rfl⟩ : syracuseStep 3099491 = 4649237) B4649237
theorem B1035139 : Blo 916578 1035139 := bstep (se 1 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 1035139 = 1552709) B1552709
theorem B6278093 : Blo 916578 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B1035283 : Blo 916578 1035283 := bstep (se 1 (by rfl) ⟨776462, by rfl⟩ : syracuseStep 1035283 = 1552925) B1552925
theorem B3099761 : Blo 916578 3099761 := bstep (se 2 (by rfl) ⟨1162410, by rfl⟩ : syracuseStep 3099761 = 2324821) B2324821
theorem B1035427 : Blo 916578 1035427 := bstep (se 1 (by rfl) ⟨776570, by rfl⟩ : syracuseStep 1035427 = 1553141) B1553141
theorem B1035571 : Blo 916578 1035571 := bstep (se 1 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 1035571 = 1553357) B1553357
theorem B15715781 : Blo 916578 15715781 := bstep (se 4 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 15715781 = 2946709) B2946709
theorem B3493475 : Blo 916578 3493475 := bstep (se 1 (by rfl) ⟨2620106, by rfl⟩ : syracuseStep 3493475 = 5240213) B5240213
theorem B3493489 : Blo 916578 3493489 := bstep (se 2 (by rfl) ⟨1310058, by rfl⟩ : syracuseStep 3493489 = 2620117) B2620117
theorem B3100301 : Blo 916578 3100301 := bstep (se 3 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 3100301 = 1162613) B1162613
theorem B3100355 : Blo 916578 3100355 := bstep (se 1 (by rfl) ⟨2325266, by rfl⟩ : syracuseStep 3100355 = 4650533) B4650533
theorem B3821347 : Blo 916578 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B3100625 : Blo 916578 3100625 := bstep (se 2 (by rfl) ⟨1162734, by rfl⟩ : syracuseStep 3100625 = 2325469) B2325469
theorem B6606917 : Blo 916578 6606917 := bstep (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) B1238797
theorem B2937073 : Blo 916578 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B4641137 : Blo 916578 4641137 := bstep (se 2 (by rfl) ⟨1740426, by rfl⟩ : syracuseStep 4641137 = 3480853) B3480853
theorem B3101165 : Blo 916578 3101165 := bstep (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) B1162937
theorem B3101219 : Blo 916578 3101219 := bstep (se 1 (by rfl) ⟨2325914, by rfl⟩ : syracuseStep 3101219 = 4651829) B4651829
theorem B1397297 : Blo 916578 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B3723853 : Blo 916578 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B3101489 : Blo 916578 3101489 := bstep (se 2 (by rfl) ⟨1163058, by rfl⟩ : syracuseStep 3101489 = 2326117) B2326117
theorem B3920881 : Blo 916578 3920881 := bstep (se 2 (by rfl) ⟨1470330, by rfl⟩ : syracuseStep 3920881 = 2940661) B2940661
theorem B1102835 : Blo 916578 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B3494947 : Blo 916578 3494947 := bstep (se 1 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 3494947 = 5242421) B5242421
theorem B2610413 : Blo 916578 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B2610481 : Blo 916578 2610481 := bstep (se 2 (by rfl) ⟨978930, by rfl⟩ : syracuseStep 2610481 = 1957861) B1957861
theorem B7853381 : Blo 916578 7853381 := bstep (se 4 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 7853381 = 1472509) B1472509
theorem B2938189 : Blo 916578 2938189 := bstep (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) B1101821
theorem B3102029 : Blo 916578 3102029 := bstep (se 3 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 3102029 = 1163261) B1163261
theorem B3233105 : Blo 916578 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B1529203 : Blo 916578 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B3102083 : Blo 916578 3102083 := bstep (se 1 (by rfl) ⟨2326562, by rfl⟩ : syracuseStep 3102083 = 4653125) B4653125
theorem B2610755 : Blo 916578 2610755 := bstep (se 1 (by rfl) ⟨1958066, by rfl⟩ : syracuseStep 2610755 = 3916133) B3916133
theorem B1398403 : Blo 916578 1398403 := bstep (se 1 (by rfl) ⟨1048802, by rfl⟩ : syracuseStep 1398403 = 2097605) B2097605
theorem B3102353 : Blo 916578 3102353 := bstep (se 2 (by rfl) ⟨1163382, by rfl⟩ : syracuseStep 3102353 = 2326765) B2326765
theorem B5232397 : Blo 916578 5232397 := bstep (se 3 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 5232397 = 1962149) B1962149
theorem B4642595 : Blo 916578 4642595 := bstep (se 1 (by rfl) ⟨3481946, by rfl⟩ : syracuseStep 4642595 = 6963893) B6963893
theorem B7460677 : Blo 916578 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B2480017 : Blo 916578 2480017 := bstep (se 2 (by rfl) ⟨930006, by rfl⟩ : syracuseStep 2480017 = 1860013) B1860013
theorem B2939021 : Blo 916578 2939021 := bstep (se 3 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 2939021 = 1102133) B1102133
theorem B12572813 : Blo 916578 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B3102893 : Blo 916578 3102893 := bstep (se 3 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 3102893 = 1163585) B1163585
theorem B3102947 : Blo 916578 3102947 := bstep (se 1 (by rfl) ⟨2327210, by rfl⟩ : syracuseStep 3102947 = 4654421) B4654421
theorem B2480483 : Blo 916578 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B2611597 : Blo 916578 2611597 := bstep (se 3 (by rfl) ⟨489674, by rfl⟩ : syracuseStep 2611597 = 979349) B979349
theorem B4708813 : Blo 916578 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B3103217 : Blo 916578 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B2611757 : Blo 916578 2611757 := bstep (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) B979409
theorem B4643405 : Blo 916578 4643405 := bstep (se 3 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 4643405 = 1741277) B1741277
theorem B2611939 : Blo 916578 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B6970211 : Blo 916578 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B1858481 : Blo 916578 1858481 := bstep (se 2 (by rfl) ⟨696930, by rfl⟩ : syracuseStep 1858481 = 1393861) B1393861
theorem B3529699 : Blo 916578 3529699 := bstep (se 1 (by rfl) ⟨2647274, by rfl⟩ : syracuseStep 3529699 = 5294549) B5294549
theorem B3103757 : Blo 916578 3103757 := bstep (se 3 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 3103757 = 1163909) B1163909
theorem B3103811 : Blo 916578 3103811 := bstep (se 1 (by rfl) ⟨2327858, by rfl⟩ : syracuseStep 3103811 = 4655717) B4655717
theorem B3104081 : Blo 916578 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B1105267 : Blo 916578 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B5234381 : Blo 916578 5234381 := bstep (se 3 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 5234381 = 1962893) B1962893
theorem B2416433 : Blo 916578 2416433 := bstep (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) B1812325
theorem B1957699 : Blo 916578 1957699 := bstep (se 1 (by rfl) ⟨1468274, by rfl⟩ : syracuseStep 1957699 = 2936549) B2936549
theorem B3104621 : Blo 916578 3104621 := bstep (se 3 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 3104621 = 1164233) B1164233
theorem B3104675 : Blo 916578 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B2482211 : Blo 916578 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B11952197 : Blo 916578 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2613329 : Blo 916578 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B3104945 : Blo 916578 3104945 := bstep (se 2 (by rfl) ⟨1164354, by rfl⟩ : syracuseStep 3104945 = 2328709) B2328709
theorem B2941123 : Blo 916578 2941123 := bstep (se 1 (by rfl) ⟨2205842, by rfl⟩ : syracuseStep 2941123 = 4411685) B4411685
theorem B2646307 : Blo 916578 2646307 := bstep (se 1 (by rfl) ⟨1984730, by rfl⟩ : syracuseStep 2646307 = 3969461) B3969461
theorem B2482481 : Blo 916578 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B2941265 : Blo 916578 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B5038541 : Blo 916578 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B3924557 : Blo 916578 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B5235313 : Blo 916578 5235313 := bstep (se 2 (by rfl) ⟨1963242, by rfl⟩ : syracuseStep 5235313 = 3926485) B3926485
theorem B3105485 : Blo 916578 3105485 := bstep (se 3 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 3105485 = 1164557) B1164557
theorem B3105539 : Blo 916578 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B5104397 : Blo 916578 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B11789297 : Blo 916578 11789297 := bstep (se 2 (by rfl) ⟨4420986, by rfl⟩ : syracuseStep 11789297 = 8841973) B8841973
theorem B2614285 : Blo 916578 2614285 := bstep (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) B980357
theorem B3105809 : Blo 916578 3105809 := bstep (se 2 (by rfl) ⟨1164678, by rfl⟩ : syracuseStep 3105809 = 2329357) B2329357
theorem B10478645 : Blo 916578 10478645 := bstep (se 5 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 10478645 = 982373) B982373
theorem B2614513 : Blo 916578 2614513 := bstep (se 2 (by rfl) ⟨980442, by rfl⟩ : syracuseStep 2614513 = 1960885) B1960885
theorem B1959203 : Blo 916578 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B2614673 : Blo 916578 2614673 := bstep (se 2 (by rfl) ⟨980502, by rfl⟩ : syracuseStep 2614673 = 1961005) B1961005
theorem B4646321 : Blo 916578 4646321 := bstep (se 2 (by rfl) ⟨1742370, by rfl⟩ : syracuseStep 4646321 = 3484741) B3484741
theorem B2483693 : Blo 916578 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B2614787 : Blo 916578 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B3106349 : Blo 916578 3106349 := bstep (se 3 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 3106349 = 1164881) B1164881
theorem B3106403 : Blo 916578 3106403 := bstep (se 1 (by rfl) ⟨2329802, by rfl⟩ : syracuseStep 3106403 = 4659605) B4659605
theorem B3139373 : Blo 916578 3139373 := bstep (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) B1177265
theorem B3106673 : Blo 916578 3106673 := bstep (se 2 (by rfl) ⟨1165002, by rfl⟩ : syracuseStep 3106673 = 2330005) B2330005
theorem B1861553 : Blo 916578 1861553 := bstep (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) B1396165
theorem B23553989 : Blo 916578 23553989 := bstep (se 4 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 23553989 = 4416373) B4416373
theorem B5236771 : Blo 916578 5236771 := bstep (se 1 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 5236771 = 7855157) B7855157
theorem B5597261 : Blo 916578 5597261 := bstep (se 3 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 5597261 = 2098973) B2098973
theorem B944339 : Blo 916578 944339 := bstep (se 1 (by rfl) ⟨708254, by rfl⟩ : syracuseStep 944339 = 1416509) B1416509
theorem B2320721 : Blo 916578 2320721 := bstep (se 2 (by rfl) ⟨870270, by rfl⟩ : syracuseStep 2320721 = 1740541) B1740541
theorem B2320771 : Blo 916578 2320771 := bstep (se 1 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 2320771 = 3481157) B3481157
theorem B2484643 : Blo 916578 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B2615789 : Blo 916578 2615789 := bstep (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) B980921
theorem B1960433 : Blo 916578 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B7432717 : Blo 916578 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B2320913 : Blo 916578 2320913 := bstep (se 2 (by rfl) ⟨870342, by rfl⟩ : syracuseStep 2320913 = 1740685) B1740685
theorem B5237297 : Blo 916578 5237297 := bstep (se 2 (by rfl) ⟨1963986, by rfl⟩ : syracuseStep 5237297 = 3927973) B3927973
theorem B1469011 : Blo 916578 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B2615971 : Blo 916578 2615971 := bstep (se 1 (by rfl) ⟨1961978, by rfl⟩ : syracuseStep 2615971 = 3923957) B3923957
theorem B2943661 : Blo 916578 2943661 := bstep (se 3 (by rfl) ⟨551936, by rfl⟩ : syracuseStep 2943661 = 1103873) B1103873
theorem B1469249 : Blo 916578 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B2616131 : Blo 916578 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B2091857 : Blo 916578 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B4647779 : Blo 916578 4647779 := bstep (se 1 (by rfl) ⟨3485834, by rfl⟩ : syracuseStep 4647779 = 6971669) B6971669
theorem B1305571 : Blo 916578 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B1469459 : Blo 916578 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B2354243 : Blo 916578 2354243 := bstep (se 1 (by rfl) ⟨1765682, by rfl⟩ : syracuseStep 2354243 = 3531365) B3531365
theorem B1862851 : Blo 916578 1862851 := bstep (se 1 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 1862851 = 2794277) B2794277
theorem B35810531 : Blo 916578 35810531 := bstep (se 1 (by rfl) ⟨26857898, by rfl⟩ : syracuseStep 35810531 = 53715797) B53715797
theorem B1961329 : Blo 916578 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B1961347 : Blo 916578 1961347 := bstep (se 1 (by rfl) ⟨1471010, by rfl⟩ : syracuseStep 1961347 = 2942021) B2942021
theorem B11791757 : Blo 916578 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B1306049 : Blo 916578 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B2321905 : Blo 916578 2321905 := bstep (se 2 (by rfl) ⟨870714, by rfl⟩ : syracuseStep 2321905 = 1741429) B1741429
theorem B1306163 : Blo 916578 1306163 := bstep (se 1 (by rfl) ⟨979622, by rfl⟩ : syracuseStep 1306163 = 1959245) B1959245
theorem B2977357 : Blo 916578 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B2649677 : Blo 916578 2649677 := bstep (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) B993629
theorem B3141233 : Blo 916578 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B1306243 : Blo 916578 1306243 := bstep (se 1 (by rfl) ⟨979682, by rfl⟩ : syracuseStep 1306243 = 1959365) B1959365
theorem B4648589 : Blo 916578 4648589 := bstep (se 3 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 4648589 = 1743221) B1743221
theorem B1240721 : Blo 916578 1240721 := bstep (se 2 (by rfl) ⟨465270, by rfl⟩ : syracuseStep 1240721 = 930541) B930541
theorem B5893829 : Blo 916578 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B2322179 : Blo 916578 2322179 := bstep (se 1 (by rfl) ⟨1741634, by rfl⟩ : syracuseStep 2322179 = 3483269) B3483269
theorem B1470241 : Blo 916578 1470241 := bstep (se 2 (by rfl) ⟨551340, by rfl⟩ : syracuseStep 1470241 = 1102681) B1102681
theorem B3141443 : Blo 916578 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B2617201 : Blo 916578 2617201 := bstep (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) B1962901
theorem B2322371 : Blo 916578 2322371 := bstep (se 1 (by rfl) ⟨1741778, by rfl⟩ : syracuseStep 2322371 = 3483557) B3483557
theorem B5238755 : Blo 916578 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B19132469 : Blo 916578 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B6975557 : Blo 916578 6975557 := bstep (se 4 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 6975557 = 1307917) B1307917
theorem B1306801 : Blo 916578 1306801 := bstep (se 2 (by rfl) ⟨490050, by rfl⟩ : syracuseStep 1306801 = 980101) B980101
theorem B979123 : Blo 916578 979123 := bstep (se 1 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 979123 = 1468685) B1468685
theorem B4714723 : Blo 916578 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B16740917 : Blo 916578 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B1471043 : Blo 916578 1471043 := bstep (se 1 (by rfl) ⟨1103282, by rfl⟩ : syracuseStep 1471043 = 2206565) B2206565
theorem B979571 : Blo 916578 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B2356049 : Blo 916578 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B3928931 : Blo 916578 3928931 := bstep (se 1 (by rfl) ⟨2946698, by rfl⟩ : syracuseStep 3928931 = 5893397) B5893397
theorem B2323313 : Blo 916578 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B1307507 : Blo 916578 1307507 := bstep (se 1 (by rfl) ⟨980630, by rfl⟩ : syracuseStep 1307507 = 1961261) B1961261
theorem B2323363 : Blo 916578 2323363 := bstep (se 1 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 2323363 = 3485045) B3485045
theorem B2323505 : Blo 916578 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1471555 : Blo 916578 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B2618477 : Blo 916578 2618477 := bstep (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) B981929
theorem B7861445 : Blo 916578 7861445 := bstep (se 4 (by rfl) ⟨737010, by rfl⟩ : syracuseStep 7861445 = 1474021) B1474021
theorem B1045747 : Blo 916578 1045747 := bstep (se 1 (by rfl) ⟨784310, by rfl⟩ : syracuseStep 1045747 = 1568621) B1568621
theorem B2618659 : Blo 916578 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B2618705 : Blo 916578 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B1242451 : Blo 916578 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B1242577 : Blo 916578 1242577 := bstep (se 2 (by rfl) ⟨465966, by rfl⟩ : syracuseStep 1242577 = 931933) B931933
theorem B1308145 : Blo 916578 1308145 := bstep (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) B981109
theorem B1308259 : Blo 916578 1308259 := bstep (se 1 (by rfl) ⟨981194, by rfl⟩ : syracuseStep 1308259 = 1962389) B1962389
theorem B1472099 : Blo 916578 1472099 := bstep (se 1 (by rfl) ⟨1104074, by rfl⟩ : syracuseStep 1472099 = 2208149) B2208149
theorem B1963619 : Blo 916578 1963619 := bstep (se 1 (by rfl) ⟨1472714, by rfl⟩ : syracuseStep 1963619 = 2945429) B2945429
theorem B3307121 : Blo 916578 3307121 := bstep (se 2 (by rfl) ⟨1240170, by rfl⟩ : syracuseStep 3307121 = 2480341) B2480341
theorem B1472273 : Blo 916578 1472273 := bstep (se 2 (by rfl) ⟨552102, by rfl⟩ : syracuseStep 1472273 = 1104205) B1104205
theorem B5240645 : Blo 916578 5240645 := bstep (se 4 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 5240645 = 982621) B982621
theorem B7862129 : Blo 916578 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B1046467 : Blo 916578 1046467 := bstep (se 1 (by rfl) ⟨784850, by rfl⟩ : syracuseStep 1046467 = 1569701) B1569701
theorem B980947 : Blo 916578 980947 := bstep (se 1 (by rfl) ⟨735710, by rfl⟩ : syracuseStep 980947 = 1471421) B1471421
theorem B2947043 : Blo 916578 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B1046531 : Blo 916578 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B2324497 : Blo 916578 2324497 := bstep (se 2 (by rfl) ⟨871686, by rfl⟩ : syracuseStep 2324497 = 1743373) B1743373
theorem B1046563 : Blo 916578 1046563 := bstep (se 1 (by rfl) ⟨784922, by rfl⟩ : syracuseStep 1046563 = 1569845) B1569845
theorem B2062385 : Blo 916578 2062385 := bstep (se 2 (by rfl) ⟨773394, by rfl⟩ : syracuseStep 2062385 = 1546789) B1546789
theorem B1964081 : Blo 916578 1964081 := bstep (se 2 (by rfl) ⟨736530, by rfl⟩ : syracuseStep 1964081 = 1473061) B1473061
theorem B2062403 : Blo 916578 2062403 := bstep (se 1 (by rfl) ⟨1546802, by rfl⟩ : syracuseStep 2062403 = 3093605) B3093605
theorem B2324771 : Blo 916578 2324771 := bstep (se 1 (by rfl) ⟨1743578, by rfl⟩ : syracuseStep 2324771 = 3487157) B3487157
theorem B2062673 : Blo 916578 2062673 := bstep (se 2 (by rfl) ⟨773502, by rfl⟩ : syracuseStep 2062673 = 1547005) B1547005
theorem B1767761 : Blo 916578 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B2062691 : Blo 916578 2062691 := bstep (se 1 (by rfl) ⟨1547018, by rfl⟩ : syracuseStep 2062691 = 3094037) B3094037
theorem B5896547 : Blo 916578 5896547 := bstep (se 1 (by rfl) ⟨4422410, by rfl⟩ : syracuseStep 5896547 = 8844821) B8844821
theorem B2324963 : Blo 916578 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B4651505 : Blo 916578 4651505 := bstep (se 2 (by rfl) ⟨1744314, by rfl⟩ : syracuseStep 4651505 = 3488629) B3488629
theorem B2062961 : Blo 916578 2062961 := bstep (se 2 (by rfl) ⟨773610, by rfl⟩ : syracuseStep 2062961 = 1547221) B1547221
theorem B2062979 : Blo 916578 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B1374881 : Blo 916578 1374881 := bstep (se 2 (by rfl) ⟨515580, by rfl⟩ : syracuseStep 1374881 = 1031161) B1031161
theorem B1374899 : Blo 916578 1374899 := bstep (se 1 (by rfl) ⟨1031174, by rfl⟩ : syracuseStep 1374899 = 2062349) B2062349
theorem B1374929 : Blo 916578 1374929 := bstep (se 2 (by rfl) ⟨515598, by rfl⟩ : syracuseStep 1374929 = 1031197) B1031197
theorem B1374947 : Blo 916578 1374947 := bstep (se 1 (by rfl) ⟨1031210, by rfl⟩ : syracuseStep 1374947 = 2062421) B2062421
theorem B1374977 : Blo 916578 1374977 := bstep (se 2 (by rfl) ⟨515616, by rfl⟩ : syracuseStep 1374977 = 1031233) B1031233
theorem B2620163 : Blo 916578 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B1374995 : Blo 916578 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B1375025 : Blo 916578 1375025 := bstep (se 2 (by rfl) ⟨515634, by rfl⟩ : syracuseStep 1375025 = 1031269) B1031269
theorem B2947889 : Blo 916578 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B3930929 : Blo 916578 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B1375043 : Blo 916578 1375043 := bstep (se 1 (by rfl) ⟨1031282, by rfl⟩ : syracuseStep 1375043 = 2062565) B2062565
theorem B1375073 : Blo 916578 1375073 := bstep (se 2 (by rfl) ⟨515652, by rfl⟩ : syracuseStep 1375073 = 1031305) B1031305
theorem B1375091 : Blo 916578 1375091 := bstep (se 1 (by rfl) ⟨1031318, by rfl⟩ : syracuseStep 1375091 = 2062637) B2062637
theorem B1375121 : Blo 916578 1375121 := bstep (se 2 (by rfl) ⟨515670, by rfl⟩ : syracuseStep 1375121 = 1031341) B1031341
theorem B2063249 : Blo 916578 2063249 := bstep (se 2 (by rfl) ⟨773718, by rfl⟩ : syracuseStep 2063249 = 1547437) B1547437
theorem B1375139 : Blo 916578 1375139 := bstep (se 1 (by rfl) ⟨1031354, by rfl⟩ : syracuseStep 1375139 = 2062709) B2062709
theorem B2063267 : Blo 916578 2063267 := bstep (se 1 (by rfl) ⟨1547450, by rfl⟩ : syracuseStep 2063267 = 3094901) B3094901
theorem B1309603 : Blo 916578 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1047475 : Blo 916578 1047475 := bstep (se 1 (by rfl) ⟨785606, by rfl⟩ : syracuseStep 1047475 = 1571213) B1571213
theorem B1375169 : Blo 916578 1375169 := bstep (se 2 (by rfl) ⟨515688, by rfl⟩ : syracuseStep 1375169 = 1031377) B1031377
theorem B1375187 : Blo 916578 1375187 := bstep (se 1 (by rfl) ⟨1031390, by rfl⟩ : syracuseStep 1375187 = 2062781) B2062781
theorem B1375217 : Blo 916578 1375217 := bstep (se 2 (by rfl) ⟨515706, by rfl⟩ : syracuseStep 1375217 = 1031413) B1031413
theorem B1375235 : Blo 916578 1375235 := bstep (se 1 (by rfl) ⟨1031426, by rfl⟩ : syracuseStep 1375235 = 2062853) B2062853
theorem B1375265 : Blo 916578 1375265 := bstep (se 2 (by rfl) ⟨515724, by rfl⟩ : syracuseStep 1375265 = 1031449) B1031449
theorem B1375283 : Blo 916578 1375283 := bstep (se 1 (by rfl) ⟨1031462, by rfl⟩ : syracuseStep 1375283 = 2062925) B2062925
theorem B1375313 : Blo 916578 1375313 := bstep (se 2 (by rfl) ⟨515742, by rfl⟩ : syracuseStep 1375313 = 1031485) B1031485
theorem B916579 : Blo 916578 916579 := bstep (se 1 (by rfl) ⟨687434, by rfl⟩ : syracuseStep 916579 = 1374869) B1374869
theorem B1375331 : Blo 916578 1375331 := bstep (se 1 (by rfl) ⟨1031498, by rfl⟩ : syracuseStep 1375331 = 2062997) B2062997
theorem B916595 : Blo 916578 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B1375361 : Blo 916578 1375361 := bstep (se 2 (by rfl) ⟨515760, by rfl⟩ : syracuseStep 1375361 = 1031521) B1031521
theorem B916611 : Blo 916578 916611 := bstep (se 1 (by rfl) ⟨687458, by rfl⟩ : syracuseStep 916611 = 1374917) B1374917
theorem B916627 : Blo 916578 916627 := bstep (se 1 (by rfl) ⟨687470, by rfl⟩ : syracuseStep 916627 = 1374941) B1374941
theorem B1375379 : Blo 916578 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B1571987 : Blo 916578 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B916643 : Blo 916578 916643 := bstep (se 1 (by rfl) ⟨687482, by rfl⟩ : syracuseStep 916643 = 1374965) B1374965
theorem B2096291 : Blo 916578 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B1375409 : Blo 916578 1375409 := bstep (se 2 (by rfl) ⟨515778, by rfl⟩ : syracuseStep 1375409 = 1031557) B1031557
theorem B2063537 : Blo 916578 2063537 := bstep (se 2 (by rfl) ⟨773826, by rfl⟩ : syracuseStep 2063537 = 1547653) B1547653
theorem B916659 : Blo 916578 916659 := bstep (se 1 (by rfl) ⟨687494, by rfl⟩ : syracuseStep 916659 = 1374989) B1374989
theorem B4422833 : Blo 916578 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B916675 : Blo 916578 916675 := bstep (se 1 (by rfl) ⟨687506, by rfl⟩ : syracuseStep 916675 = 1375013) B1375013
theorem B1375427 : Blo 916578 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B2063555 : Blo 916578 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B982211 : Blo 916578 982211 := bstep (se 1 (by rfl) ⟨736658, by rfl⟩ : syracuseStep 982211 = 1473317) B1473317
theorem B916691 : Blo 916578 916691 := bstep (se 1 (by rfl) ⟨687518, by rfl⟩ : syracuseStep 916691 = 1375037) B1375037
theorem B1375457 : Blo 916578 1375457 := bstep (se 2 (by rfl) ⟨515796, by rfl⟩ : syracuseStep 1375457 = 1031593) B1031593
theorem B916707 : Blo 916578 916707 := bstep (se 1 (by rfl) ⟨687530, by rfl⟩ : syracuseStep 916707 = 1375061) B1375061
theorem B14908643 : Blo 916578 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B916723 : Blo 916578 916723 := bstep (se 1 (by rfl) ⟨687542, by rfl⟩ : syracuseStep 916723 = 1375085) B1375085
theorem B1375475 : Blo 916578 1375475 := bstep (se 1 (by rfl) ⟨1031606, by rfl⟩ : syracuseStep 1375475 = 2063213) B2063213
theorem B916739 : Blo 916578 916739 := bstep (se 1 (by rfl) ⟨687554, by rfl⟩ : syracuseStep 916739 = 1375109) B1375109
theorem B1375505 : Blo 916578 1375505 := bstep (se 2 (by rfl) ⟨515814, by rfl⟩ : syracuseStep 1375505 = 1031629) B1031629
theorem B916755 : Blo 916578 916755 := bstep (se 1 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 916755 = 1375133) B1375133
theorem B916771 : Blo 916578 916771 := bstep (se 1 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 916771 = 1375157) B1375157
theorem B1375523 : Blo 916578 1375523 := bstep (se 1 (by rfl) ⟨1031642, by rfl⟩ : syracuseStep 1375523 = 2063285) B2063285
theorem B2653489 : Blo 916578 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B916787 : Blo 916578 916787 := bstep (se 1 (by rfl) ⟨687590, by rfl⟩ : syracuseStep 916787 = 1375181) B1375181
theorem B1375553 : Blo 916578 1375553 := bstep (se 2 (by rfl) ⟨515832, by rfl⟩ : syracuseStep 1375553 = 1031665) B1031665
theorem B916803 : Blo 916578 916803 := bstep (se 1 (by rfl) ⟨687602, by rfl⟩ : syracuseStep 916803 = 1375205) B1375205
theorem B1965379 : Blo 916578 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B916819 : Blo 916578 916819 := bstep (se 1 (by rfl) ⟨687614, by rfl⟩ : syracuseStep 916819 = 1375229) B1375229
theorem B1375571 : Blo 916578 1375571 := bstep (se 1 (by rfl) ⟨1031678, by rfl⟩ : syracuseStep 1375571 = 2063357) B2063357
theorem B916835 : Blo 916578 916835 := bstep (se 1 (by rfl) ⟨687626, by rfl⟩ : syracuseStep 916835 = 1375253) B1375253
theorem B1375601 : Blo 916578 1375601 := bstep (se 2 (by rfl) ⟨515850, by rfl⟩ : syracuseStep 1375601 = 1031701) B1031701
theorem B4423025 : Blo 916578 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B916851 : Blo 916578 916851 := bstep (se 1 (by rfl) ⟨687638, by rfl⟩ : syracuseStep 916851 = 1375277) B1375277
theorem B916867 : Blo 916578 916867 := bstep (se 1 (by rfl) ⟨687650, by rfl⟩ : syracuseStep 916867 = 1375301) B1375301
theorem B1375619 : Blo 916578 1375619 := bstep (se 1 (by rfl) ⟨1031714, by rfl⟩ : syracuseStep 1375619 = 2063429) B2063429
theorem B2325905 : Blo 916578 2325905 := bstep (se 2 (by rfl) ⟨872214, by rfl⟩ : syracuseStep 2325905 = 1744429) B1744429
theorem B916883 : Blo 916578 916883 := bstep (se 1 (by rfl) ⟨687662, by rfl⟩ : syracuseStep 916883 = 1375325) B1375325
theorem B1375649 : Blo 916578 1375649 := bstep (se 2 (by rfl) ⟨515868, by rfl⟩ : syracuseStep 1375649 = 1031737) B1031737
theorem B916899 : Blo 916578 916899 := bstep (se 1 (by rfl) ⟨687674, by rfl⟩ : syracuseStep 916899 = 1375349) B1375349
theorem B916915 : Blo 916578 916915 := bstep (se 1 (by rfl) ⟨687686, by rfl⟩ : syracuseStep 916915 = 1375373) B1375373
theorem B1375667 : Blo 916578 1375667 := bstep (se 1 (by rfl) ⟨1031750, by rfl⟩ : syracuseStep 1375667 = 2063501) B2063501
theorem B916931 : Blo 916578 916931 := bstep (se 1 (by rfl) ⟨687698, by rfl⟩ : syracuseStep 916931 = 1375397) B1375397
theorem B2325955 : Blo 916578 2325955 := bstep (se 1 (by rfl) ⟨1744466, by rfl⟩ : syracuseStep 2325955 = 3488933) B3488933
theorem B1375697 : Blo 916578 1375697 := bstep (se 2 (by rfl) ⟨515886, by rfl⟩ : syracuseStep 1375697 = 1031773) B1031773
theorem B2063825 : Blo 916578 2063825 := bstep (se 2 (by rfl) ⟨773934, by rfl⟩ : syracuseStep 2063825 = 1547869) B1547869
theorem B916947 : Blo 916578 916947 := bstep (se 1 (by rfl) ⟨687710, by rfl⟩ : syracuseStep 916947 = 1375421) B1375421
theorem B916963 : Blo 916578 916963 := bstep (se 1 (by rfl) ⟨687722, by rfl⟩ : syracuseStep 916963 = 1375445) B1375445
theorem B1375715 : Blo 916578 1375715 := bstep (se 1 (by rfl) ⟨1031786, by rfl⟩ : syracuseStep 1375715 = 2063573) B2063573
theorem B2063843 : Blo 916578 2063843 := bstep (se 1 (by rfl) ⟨1547882, by rfl⟩ : syracuseStep 2063843 = 3095765) B3095765
theorem B916979 : Blo 916578 916979 := bstep (se 1 (by rfl) ⟨687734, by rfl⟩ : syracuseStep 916979 = 1375469) B1375469
theorem B1375745 : Blo 916578 1375745 := bstep (se 2 (by rfl) ⟨515904, by rfl⟩ : syracuseStep 1375745 = 1031809) B1031809
theorem B916995 : Blo 916578 916995 := bstep (se 1 (by rfl) ⟨687746, by rfl⟩ : syracuseStep 916995 = 1375493) B1375493
theorem B917011 : Blo 916578 917011 := bstep (se 1 (by rfl) ⟨687758, by rfl⟩ : syracuseStep 917011 = 1375517) B1375517
theorem B1375763 : Blo 916578 1375763 := bstep (se 1 (by rfl) ⟨1031822, by rfl⟩ : syracuseStep 1375763 = 2063645) B2063645
theorem B917027 : Blo 916578 917027 := bstep (se 1 (by rfl) ⟨687770, by rfl⟩ : syracuseStep 917027 = 1375541) B1375541
theorem B1375793 : Blo 916578 1375793 := bstep (se 2 (by rfl) ⟨515922, by rfl⟩ : syracuseStep 1375793 = 1031845) B1031845
theorem B917043 : Blo 916578 917043 := bstep (se 1 (by rfl) ⟨687782, by rfl⟩ : syracuseStep 917043 = 1375565) B1375565
theorem B917059 : Blo 916578 917059 := bstep (se 1 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 917059 = 1375589) B1375589
theorem B1375811 : Blo 916578 1375811 := bstep (se 1 (by rfl) ⟨1031858, by rfl⟩ : syracuseStep 1375811 = 2063717) B2063717
theorem B1965635 : Blo 916578 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B2326097 : Blo 916578 2326097 := bstep (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) B1744573
theorem B917075 : Blo 916578 917075 := bstep (se 1 (by rfl) ⟨687806, by rfl⟩ : syracuseStep 917075 = 1375613) B1375613
theorem B1375841 : Blo 916578 1375841 := bstep (se 2 (by rfl) ⟨515940, by rfl⟩ : syracuseStep 1375841 = 1031881) B1031881
theorem B917091 : Blo 916578 917091 := bstep (se 1 (by rfl) ⟨687818, by rfl⟩ : syracuseStep 917091 = 1375637) B1375637
theorem B917107 : Blo 916578 917107 := bstep (se 1 (by rfl) ⟨687830, by rfl⟩ : syracuseStep 917107 = 1375661) B1375661
theorem B1375859 : Blo 916578 1375859 := bstep (se 1 (by rfl) ⟨1031894, by rfl⟩ : syracuseStep 1375859 = 2063789) B2063789
theorem B917123 : Blo 916578 917123 := bstep (se 1 (by rfl) ⟨687842, by rfl⟩ : syracuseStep 917123 = 1375685) B1375685
theorem B1375889 : Blo 916578 1375889 := bstep (se 2 (by rfl) ⟨515958, by rfl⟩ : syracuseStep 1375889 = 1031917) B1031917
theorem B917139 : Blo 916578 917139 := bstep (se 1 (by rfl) ⟨687854, by rfl⟩ : syracuseStep 917139 = 1375709) B1375709
theorem B917155 : Blo 916578 917155 := bstep (se 1 (by rfl) ⟨687866, by rfl⟩ : syracuseStep 917155 = 1375733) B1375733
theorem B1375907 : Blo 916578 1375907 := bstep (se 1 (by rfl) ⟨1031930, by rfl⟩ : syracuseStep 1375907 = 2063861) B2063861
theorem B917171 : Blo 916578 917171 := bstep (se 1 (by rfl) ⟨687878, by rfl⟩ : syracuseStep 917171 = 1375757) B1375757
theorem B1375937 : Blo 916578 1375937 := bstep (se 2 (by rfl) ⟨515976, by rfl⟩ : syracuseStep 1375937 = 1031953) B1031953
theorem B917187 : Blo 916578 917187 := bstep (se 1 (by rfl) ⟨687890, by rfl⟩ : syracuseStep 917187 = 1375781) B1375781
theorem B917203 : Blo 916578 917203 := bstep (se 1 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 917203 = 1375805) B1375805
theorem B1375955 : Blo 916578 1375955 := bstep (se 1 (by rfl) ⟨1031966, by rfl⟩ : syracuseStep 1375955 = 2063933) B2063933
theorem B917219 : Blo 916578 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1375985 : Blo 916578 1375985 := bstep (se 2 (by rfl) ⟨515994, by rfl⟩ : syracuseStep 1375985 = 1031989) B1031989
theorem B2064113 : Blo 916578 2064113 := bstep (se 2 (by rfl) ⟨774042, by rfl⟩ : syracuseStep 2064113 = 1548085) B1548085
theorem B917235 : Blo 916578 917235 := bstep (se 1 (by rfl) ⟨687926, by rfl⟩ : syracuseStep 917235 = 1375853) B1375853
theorem B1474291 : Blo 916578 1474291 := bstep (se 1 (by rfl) ⟨1105718, by rfl⟩ : syracuseStep 1474291 = 2211437) B2211437
theorem B917251 : Blo 916578 917251 := bstep (se 1 (by rfl) ⟨687938, by rfl⟩ : syracuseStep 917251 = 1375877) B1375877
theorem B1376003 : Blo 916578 1376003 := bstep (se 1 (by rfl) ⟨1032002, by rfl⟩ : syracuseStep 1376003 = 2064005) B2064005
theorem B2064131 : Blo 916578 2064131 := bstep (se 1 (by rfl) ⟨1548098, by rfl⟩ : syracuseStep 2064131 = 3096197) B3096197
theorem B917267 : Blo 916578 917267 := bstep (se 1 (by rfl) ⟨687950, by rfl⟩ : syracuseStep 917267 = 1375901) B1375901
theorem B1376033 : Blo 916578 1376033 := bstep (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) B1032025
theorem B917283 : Blo 916578 917283 := bstep (se 1 (by rfl) ⟨687962, by rfl⟩ : syracuseStep 917283 = 1375925) B1375925
theorem B917299 : Blo 916578 917299 := bstep (se 1 (by rfl) ⟨687974, by rfl⟩ : syracuseStep 917299 = 1375949) B1375949
theorem B1376051 : Blo 916578 1376051 := bstep (se 1 (by rfl) ⟨1032038, by rfl⟩ : syracuseStep 1376051 = 2064077) B2064077
theorem B1474355 : Blo 916578 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B917315 : Blo 916578 917315 := bstep (se 1 (by rfl) ⟨687986, by rfl⟩ : syracuseStep 917315 = 1375973) B1375973
theorem B1376081 : Blo 916578 1376081 := bstep (se 2 (by rfl) ⟨516030, by rfl⟩ : syracuseStep 1376081 = 1032061) B1032061
theorem B917331 : Blo 916578 917331 := bstep (se 1 (by rfl) ⟨687998, by rfl⟩ : syracuseStep 917331 = 1375997) B1375997
theorem B917347 : Blo 916578 917347 := bstep (se 1 (by rfl) ⟨688010, by rfl⟩ : syracuseStep 917347 = 1376021) B1376021
theorem B1376099 : Blo 916578 1376099 := bstep (se 1 (by rfl) ⟨1032074, by rfl⟩ : syracuseStep 1376099 = 2064149) B2064149
theorem B917363 : Blo 916578 917363 := bstep (se 1 (by rfl) ⟨688022, by rfl⟩ : syracuseStep 917363 = 1376045) B1376045
theorem B1376129 : Blo 916578 1376129 := bstep (se 2 (by rfl) ⟨516048, by rfl⟩ : syracuseStep 1376129 = 1032097) B1032097
theorem B917379 : Blo 916578 917379 := bstep (se 1 (by rfl) ⟨688034, by rfl⟩ : syracuseStep 917379 = 1376069) B1376069
theorem B1179523 : Blo 916578 1179523 := bstep (se 1 (by rfl) ⟨884642, by rfl⟩ : syracuseStep 1179523 = 1769285) B1769285
theorem B917395 : Blo 916578 917395 := bstep (se 1 (by rfl) ⟨688046, by rfl⟩ : syracuseStep 917395 = 1376093) B1376093
theorem B1376147 : Blo 916578 1376147 := bstep (se 1 (by rfl) ⟨1032110, by rfl⟩ : syracuseStep 1376147 = 2064221) B2064221
theorem B917411 : Blo 916578 917411 := bstep (se 1 (by rfl) ⟨688058, by rfl⟩ : syracuseStep 917411 = 1376117) B1376117
theorem B4652963 : Blo 916578 4652963 := bstep (se 1 (by rfl) ⟨3489722, by rfl⟩ : syracuseStep 4652963 = 6979445) B6979445
theorem B1376177 : Blo 916578 1376177 := bstep (se 2 (by rfl) ⟨516066, by rfl⟩ : syracuseStep 1376177 = 1032133) B1032133
theorem B917427 : Blo 916578 917427 := bstep (se 1 (by rfl) ⟨688070, by rfl⟩ : syracuseStep 917427 = 1376141) B1376141
theorem B982963 : Blo 916578 982963 := bstep (se 1 (by rfl) ⟨737222, by rfl⟩ : syracuseStep 982963 = 1474445) B1474445
theorem B917443 : Blo 916578 917443 := bstep (se 1 (by rfl) ⟨688082, by rfl⟩ : syracuseStep 917443 = 1376165) B1376165
theorem B1376195 : Blo 916578 1376195 := bstep (se 1 (by rfl) ⟨1032146, by rfl⟩ : syracuseStep 1376195 = 2064293) B2064293
theorem B2621393 : Blo 916578 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B917459 : Blo 916578 917459 := bstep (se 1 (by rfl) ⟨688094, by rfl⟩ : syracuseStep 917459 = 1376189) B1376189
theorem B1376225 : Blo 916578 1376225 := bstep (se 2 (by rfl) ⟨516084, by rfl⟩ : syracuseStep 1376225 = 1032169) B1032169
theorem B917475 : Blo 916578 917475 := bstep (se 1 (by rfl) ⟨688106, by rfl⟩ : syracuseStep 917475 = 1376213) B1376213
theorem B917491 : Blo 916578 917491 := bstep (se 1 (by rfl) ⟨688118, by rfl⟩ : syracuseStep 917491 = 1376237) B1376237
theorem B1376243 : Blo 916578 1376243 := bstep (se 1 (by rfl) ⟨1032182, by rfl⟩ : syracuseStep 1376243 = 2064365) B2064365
theorem B1376267 : Blo 916578 1376267 := bstep (se 1 (by rfl) ⟨1032200, by rfl⟩ : syracuseStep 1376267 = 2064401) B2064401
theorem B917515 : Blo 916578 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B1376279 : Blo 916578 1376279 := bstep (se 1 (by rfl) ⟨1032209, by rfl⟩ : syracuseStep 1376279 = 2064419) B2064419
theorem B917527 : Blo 916578 917527 := bstep (se 1 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 917527 = 1376291) B1376291
theorem B917547 : Blo 916578 917547 := bstep (se 1 (by rfl) ⟨688160, by rfl⟩ : syracuseStep 917547 = 1376321) B1376321
theorem B917559 : Blo 916578 917559 := bstep (se 1 (by rfl) ⟨688169, by rfl⟩ : syracuseStep 917559 = 1376339) B1376339
theorem B917579 : Blo 916578 917579 := bstep (se 1 (by rfl) ⟨688184, by rfl⟩ : syracuseStep 917579 = 1376369) B1376369
theorem B2326603 : Blo 916578 2326603 := bstep (se 1 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 2326603 = 3489905) B3489905
theorem B917591 : Blo 916578 917591 := bstep (se 1 (by rfl) ⟨688193, by rfl⟩ : syracuseStep 917591 = 1376387) B1376387
theorem B2064473 : Blo 916578 2064473 := bstep (se 2 (by rfl) ⟨774177, by rfl⟩ : syracuseStep 2064473 = 1548355) B1548355
theorem B1376345 : Blo 916578 1376345 := bstep (se 2 (by rfl) ⟨516129, by rfl⟩ : syracuseStep 1376345 = 1032259) B1032259
theorem B6619229 : Blo 916578 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B917611 : Blo 916578 917611 := bstep (se 1 (by rfl) ⟨688208, by rfl⟩ : syracuseStep 917611 = 1376417) B1376417
theorem B917623 : Blo 916578 917623 := bstep (se 1 (by rfl) ⟨688217, by rfl⟩ : syracuseStep 917623 = 1376435) B1376435
theorem B917643 : Blo 916578 917643 := bstep (se 1 (by rfl) ⟨688232, by rfl⟩ : syracuseStep 917643 = 1376465) B1376465
theorem B917655 : Blo 916578 917655 := bstep (se 1 (by rfl) ⟨688241, by rfl⟩ : syracuseStep 917655 = 1376483) B1376483
theorem B917675 : Blo 916578 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B2064563 : Blo 916578 2064563 := bstep (se 1 (by rfl) ⟨1548422, by rfl⟩ : syracuseStep 2064563 = 3096845) B3096845
theorem B917687 : Blo 916578 917687 := bstep (se 1 (by rfl) ⟨688265, by rfl⟩ : syracuseStep 917687 = 1376531) B1376531
theorem B1376459 : Blo 916578 1376459 := bstep (se 1 (by rfl) ⟨1032344, by rfl⟩ : syracuseStep 1376459 = 2064689) B2064689
theorem B917707 : Blo 916578 917707 := bstep (se 1 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 917707 = 1376561) B1376561
theorem B1179851 : Blo 916578 1179851 := bstep (se 1 (by rfl) ⟨884888, by rfl⟩ : syracuseStep 1179851 = 1769777) B1769777
theorem B2064599 : Blo 916578 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B1376471 : Blo 916578 1376471 := bstep (se 1 (by rfl) ⟨1032353, by rfl⟩ : syracuseStep 1376471 = 2064707) B2064707
theorem B917719 : Blo 916578 917719 := bstep (se 1 (by rfl) ⟨688289, by rfl⟩ : syracuseStep 917719 = 1376579) B1376579
theorem B2326745 : Blo 916578 2326745 := bstep (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) B1745059
theorem B917739 : Blo 916578 917739 := bstep (se 1 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 917739 = 1376609) B1376609
theorem B917751 : Blo 916578 917751 := bstep (se 1 (by rfl) ⟨688313, by rfl⟩ : syracuseStep 917751 = 1376627) B1376627
theorem B917771 : Blo 916578 917771 := bstep (se 1 (by rfl) ⟨688328, by rfl⟩ : syracuseStep 917771 = 1376657) B1376657
theorem B917783 : Blo 916578 917783 := bstep (se 1 (by rfl) ⟨688337, by rfl⟩ : syracuseStep 917783 = 1376675) B1376675
theorem B1376537 : Blo 916578 1376537 := bstep (se 2 (by rfl) ⟨516201, by rfl⟩ : syracuseStep 1376537 = 1032403) B1032403
theorem B917803 : Blo 916578 917803 := bstep (se 1 (by rfl) ⟨688352, by rfl⟩ : syracuseStep 917803 = 1376705) B1376705
theorem B917815 : Blo 916578 917815 := bstep (se 1 (by rfl) ⟨688361, by rfl⟩ : syracuseStep 917815 = 1376723) B1376723
theorem B917835 : Blo 916578 917835 := bstep (se 1 (by rfl) ⟨688376, by rfl⟩ : syracuseStep 917835 = 1376753) B1376753
theorem B917847 : Blo 916578 917847 := bstep (se 1 (by rfl) ⟨688385, by rfl⟩ : syracuseStep 917847 = 1376771) B1376771
theorem B917867 : Blo 916578 917867 := bstep (se 1 (by rfl) ⟨688400, by rfl⟩ : syracuseStep 917867 = 1376801) B1376801
theorem B917879 : Blo 916578 917879 := bstep (se 1 (by rfl) ⟨688409, by rfl⟩ : syracuseStep 917879 = 1376819) B1376819
theorem B2064779 : Blo 916578 2064779 := bstep (se 1 (by rfl) ⟨1548584, by rfl⟩ : syracuseStep 2064779 = 3097169) B3097169
theorem B1376651 : Blo 916578 1376651 := bstep (se 1 (by rfl) ⟨1032488, by rfl⟩ : syracuseStep 1376651 = 2064977) B2064977
theorem B917899 : Blo 916578 917899 := bstep (se 1 (by rfl) ⟨688424, by rfl⟩ : syracuseStep 917899 = 1376849) B1376849
theorem B1376663 : Blo 916578 1376663 := bstep (se 1 (by rfl) ⟨1032497, by rfl⟩ : syracuseStep 1376663 = 2064995) B2064995
theorem B917911 : Blo 916578 917911 := bstep (se 1 (by rfl) ⟨688433, by rfl⟩ : syracuseStep 917911 = 1376867) B1376867
theorem B1573273 : Blo 916578 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B917931 : Blo 916578 917931 := bstep (se 1 (by rfl) ⟨688448, by rfl⟩ : syracuseStep 917931 = 1376897) B1376897
theorem B917943 : Blo 916578 917943 := bstep (se 1 (by rfl) ⟨688457, by rfl⟩ : syracuseStep 917943 = 1376915) B1376915
theorem B2064833 : Blo 916578 2064833 := bstep (se 2 (by rfl) ⟨774312, by rfl⟩ : syracuseStep 2064833 = 1548625) B1548625
theorem B917963 : Blo 916578 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B917975 : Blo 916578 917975 := bstep (se 1 (by rfl) ⟨688481, by rfl⟩ : syracuseStep 917975 = 1376963) B1376963
theorem B1376729 : Blo 916578 1376729 := bstep (se 2 (by rfl) ⟨516273, by rfl⟩ : syracuseStep 1376729 = 1032547) B1032547
theorem B917995 : Blo 916578 917995 := bstep (se 1 (by rfl) ⟨688496, by rfl⟩ : syracuseStep 917995 = 1376993) B1376993
theorem B918007 : Blo 916578 918007 := bstep (se 1 (by rfl) ⟨688505, by rfl⟩ : syracuseStep 918007 = 1377011) B1377011
theorem B918027 : Blo 916578 918027 := bstep (se 1 (by rfl) ⟨688520, by rfl⟩ : syracuseStep 918027 = 1377041) B1377041
theorem B918039 : Blo 916578 918039 := bstep (se 1 (by rfl) ⟨688529, by rfl⟩ : syracuseStep 918039 = 1377059) B1377059
theorem B918059 : Blo 916578 918059 := bstep (se 1 (by rfl) ⟨688544, by rfl⟩ : syracuseStep 918059 = 1377089) B1377089
theorem B918071 : Blo 916578 918071 := bstep (se 1 (by rfl) ⟨688553, by rfl⟩ : syracuseStep 918071 = 1377107) B1377107
theorem B1376843 : Blo 916578 1376843 := bstep (se 1 (by rfl) ⟨1032632, by rfl⟩ : syracuseStep 1376843 = 2065265) B2065265
theorem B918091 : Blo 916578 918091 := bstep (se 1 (by rfl) ⟨688568, by rfl⟩ : syracuseStep 918091 = 1377137) B1377137
theorem B1376855 : Blo 916578 1376855 := bstep (se 1 (by rfl) ⟨1032641, by rfl⟩ : syracuseStep 1376855 = 2065283) B2065283
theorem B918103 : Blo 916578 918103 := bstep (se 1 (by rfl) ⟨688577, by rfl⟩ : syracuseStep 918103 = 1377155) B1377155
theorem B918123 : Blo 916578 918123 := bstep (se 1 (by rfl) ⟨688592, by rfl⟩ : syracuseStep 918123 = 1377185) B1377185
theorem B918135 : Blo 916578 918135 := bstep (se 1 (by rfl) ⟨688601, by rfl⟩ : syracuseStep 918135 = 1377203) B1377203
theorem B918155 : Blo 916578 918155 := bstep (se 1 (by rfl) ⟨688616, by rfl⟩ : syracuseStep 918155 = 1377233) B1377233
theorem B918167 : Blo 916578 918167 := bstep (se 1 (by rfl) ⟨688625, by rfl⟩ : syracuseStep 918167 = 1377251) B1377251
theorem B2065049 : Blo 916578 2065049 := bstep (se 2 (by rfl) ⟨774393, by rfl⟩ : syracuseStep 2065049 = 1548787) B1548787
theorem B1376921 : Blo 916578 1376921 := bstep (se 2 (by rfl) ⟨516345, by rfl⟩ : syracuseStep 1376921 = 1032691) B1032691
theorem B918187 : Blo 916578 918187 := bstep (se 1 (by rfl) ⟨688640, by rfl⟩ : syracuseStep 918187 = 1377281) B1377281
theorem B918199 : Blo 916578 918199 := bstep (se 1 (by rfl) ⟨688649, by rfl⟩ : syracuseStep 918199 = 1377299) B1377299
theorem B918219 : Blo 916578 918219 := bstep (se 1 (by rfl) ⟨688664, by rfl⟩ : syracuseStep 918219 = 1377329) B1377329
theorem B918231 : Blo 916578 918231 := bstep (se 1 (by rfl) ⟨688673, by rfl⟩ : syracuseStep 918231 = 1377347) B1377347
theorem B918251 : Blo 916578 918251 := bstep (se 1 (by rfl) ⟨688688, by rfl⟩ : syracuseStep 918251 = 1377377) B1377377
theorem B2065139 : Blo 916578 2065139 := bstep (se 1 (by rfl) ⟨1548854, by rfl⟩ : syracuseStep 2065139 = 3097709) B3097709
theorem B918263 : Blo 916578 918263 := bstep (se 1 (by rfl) ⟨688697, by rfl⟩ : syracuseStep 918263 = 1377395) B1377395
theorem B1377035 : Blo 916578 1377035 := bstep (se 1 (by rfl) ⟨1032776, by rfl⟩ : syracuseStep 1377035 = 2065553) B2065553
theorem B918283 : Blo 916578 918283 := bstep (se 1 (by rfl) ⟨688712, by rfl⟩ : syracuseStep 918283 = 1377425) B1377425
theorem B2065175 : Blo 916578 2065175 := bstep (se 1 (by rfl) ⟨1548881, by rfl⟩ : syracuseStep 2065175 = 3097763) B3097763
theorem B1377047 : Blo 916578 1377047 := bstep (se 1 (by rfl) ⟨1032785, by rfl⟩ : syracuseStep 1377047 = 2065571) B2065571
theorem B918295 : Blo 916578 918295 := bstep (se 1 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 918295 = 1377443) B1377443
theorem B918315 : Blo 916578 918315 := bstep (se 1 (by rfl) ⟨688736, by rfl⟩ : syracuseStep 918315 = 1377473) B1377473
theorem B918327 : Blo 916578 918327 := bstep (se 1 (by rfl) ⟨688745, by rfl⟩ : syracuseStep 918327 = 1377491) B1377491
theorem B6980417 : Blo 916578 6980417 := bstep (se 2 (by rfl) ⟨2617656, by rfl⟩ : syracuseStep 6980417 = 5235313) B5235313
theorem B918347 : Blo 916578 918347 := bstep (se 1 (by rfl) ⟨688760, by rfl⟩ : syracuseStep 918347 = 1377521) B1377521
theorem B918359 : Blo 916578 918359 := bstep (se 1 (by rfl) ⟨688769, by rfl⟩ : syracuseStep 918359 = 1377539) B1377539
theorem B1377113 : Blo 916578 1377113 := bstep (se 2 (by rfl) ⟨516417, by rfl⟩ : syracuseStep 1377113 = 1032835) B1032835
theorem B8389469 : Blo 916578 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B918379 : Blo 916578 918379 := bstep (se 1 (by rfl) ⟨688784, by rfl⟩ : syracuseStep 918379 = 1377569) B1377569
theorem B918391 : Blo 916578 918391 := bstep (se 1 (by rfl) ⟨688793, by rfl⟩ : syracuseStep 918391 = 1377587) B1377587
theorem B918411 : Blo 916578 918411 := bstep (se 1 (by rfl) ⟨688808, by rfl⟩ : syracuseStep 918411 = 1377617) B1377617
theorem B1049483 : Blo 916578 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B918423 : Blo 916578 918423 := bstep (se 1 (by rfl) ⟨688817, by rfl⟩ : syracuseStep 918423 = 1377635) B1377635
theorem B918443 : Blo 916578 918443 := bstep (se 1 (by rfl) ⟨688832, by rfl⟩ : syracuseStep 918443 = 1377665) B1377665
theorem B21201841 : Blo 916578 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B918455 : Blo 916578 918455 := bstep (se 1 (by rfl) ⟨688841, by rfl⟩ : syracuseStep 918455 = 1377683) B1377683
theorem B2065355 : Blo 916578 2065355 := bstep (se 1 (by rfl) ⟨1549016, by rfl⟩ : syracuseStep 2065355 = 3098033) B3098033
theorem B1377227 : Blo 916578 1377227 := bstep (se 1 (by rfl) ⟨1032920, by rfl⟩ : syracuseStep 1377227 = 2065841) B2065841
theorem B918475 : Blo 916578 918475 := bstep (se 1 (by rfl) ⟨688856, by rfl⟩ : syracuseStep 918475 = 1377713) B1377713
theorem B1377239 : Blo 916578 1377239 := bstep (se 1 (by rfl) ⟨1032929, by rfl⟩ : syracuseStep 1377239 = 2065859) B2065859
theorem B918487 : Blo 916578 918487 := bstep (se 1 (by rfl) ⟨688865, by rfl⟩ : syracuseStep 918487 = 1377731) B1377731
theorem B7832537 : Blo 916578 7832537 := bstep (se 2 (by rfl) ⟨2937201, by rfl⟩ : syracuseStep 7832537 = 5874403) B5874403
theorem B918507 : Blo 916578 918507 := bstep (se 1 (by rfl) ⟨688880, by rfl⟩ : syracuseStep 918507 = 1377761) B1377761
theorem B2098163 : Blo 916578 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B918519 : Blo 916578 918519 := bstep (se 1 (by rfl) ⟨688889, by rfl⟩ : syracuseStep 918519 = 1377779) B1377779
theorem B2065409 : Blo 916578 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B918539 : Blo 916578 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B4654097 : Blo 916578 4654097 := bstep (se 2 (by rfl) ⟨1745286, by rfl⟩ : syracuseStep 4654097 = 3490573) B3490573
theorem B918551 : Blo 916578 918551 := bstep (se 1 (by rfl) ⟨688913, by rfl⟩ : syracuseStep 918551 = 1377827) B1377827
theorem B2327575 : Blo 916578 2327575 := bstep (se 1 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 2327575 = 3491363) B3491363
theorem B1377305 : Blo 916578 1377305 := bstep (se 2 (by rfl) ⟨516489, by rfl⟩ : syracuseStep 1377305 = 1032979) B1032979
theorem B918571 : Blo 916578 918571 := bstep (se 1 (by rfl) ⟨688928, by rfl⟩ : syracuseStep 918571 = 1377857) B1377857
theorem B918583 : Blo 916578 918583 := bstep (se 1 (by rfl) ⟨688937, by rfl⟩ : syracuseStep 918583 = 1377875) B1377875
theorem B918603 : Blo 916578 918603 := bstep (se 1 (by rfl) ⟨688952, by rfl⟩ : syracuseStep 918603 = 1377905) B1377905
theorem B918615 : Blo 916578 918615 := bstep (se 1 (by rfl) ⟨688961, by rfl⟩ : syracuseStep 918615 = 1377923) B1377923
theorem B918635 : Blo 916578 918635 := bstep (se 1 (by rfl) ⟨688976, by rfl⟩ : syracuseStep 918635 = 1377953) B1377953
theorem B918647 : Blo 916578 918647 := bstep (se 1 (by rfl) ⟨688985, by rfl⟩ : syracuseStep 918647 = 1377971) B1377971
theorem B1377419 : Blo 916578 1377419 := bstep (se 1 (by rfl) ⟨1033064, by rfl⟩ : syracuseStep 1377419 = 2066129) B2066129
theorem B918667 : Blo 916578 918667 := bstep (se 1 (by rfl) ⟨689000, by rfl⟩ : syracuseStep 918667 = 1378001) B1378001
theorem B1377431 : Blo 916578 1377431 := bstep (se 1 (by rfl) ⟨1033073, by rfl⟩ : syracuseStep 1377431 = 2066147) B2066147
theorem B918679 : Blo 916578 918679 := bstep (se 1 (by rfl) ⟨689009, by rfl⟩ : syracuseStep 918679 = 1378019) B1378019
theorem B918699 : Blo 916578 918699 := bstep (se 1 (by rfl) ⟨689024, by rfl⟩ : syracuseStep 918699 = 1378049) B1378049
theorem B4654259 : Blo 916578 4654259 := bstep (se 1 (by rfl) ⟨3490694, by rfl⟩ : syracuseStep 4654259 = 6981389) B6981389
theorem B918711 : Blo 916578 918711 := bstep (se 1 (by rfl) ⟨689033, by rfl⟩ : syracuseStep 918711 = 1378067) B1378067
theorem B918731 : Blo 916578 918731 := bstep (se 1 (by rfl) ⟨689048, by rfl⟩ : syracuseStep 918731 = 1378097) B1378097
theorem B918743 : Blo 916578 918743 := bstep (se 1 (by rfl) ⟨689057, by rfl⟩ : syracuseStep 918743 = 1378115) B1378115
theorem B2065625 : Blo 916578 2065625 := bstep (se 2 (by rfl) ⟨774609, by rfl⟩ : syracuseStep 2065625 = 1549219) B1549219
theorem B1377497 : Blo 916578 1377497 := bstep (se 2 (by rfl) ⟨516561, by rfl⟩ : syracuseStep 1377497 = 1033123) B1033123
theorem B918763 : Blo 916578 918763 := bstep (se 1 (by rfl) ⟨689072, by rfl⟩ : syracuseStep 918763 = 1378145) B1378145
theorem B918775 : Blo 916578 918775 := bstep (se 1 (by rfl) ⟨689081, by rfl⟩ : syracuseStep 918775 = 1378163) B1378163
theorem B918795 : Blo 916578 918795 := bstep (se 1 (by rfl) ⟨689096, by rfl⟩ : syracuseStep 918795 = 1378193) B1378193
theorem B918807 : Blo 916578 918807 := bstep (se 1 (by rfl) ⟨689105, by rfl⟩ : syracuseStep 918807 = 1378211) B1378211
theorem B918827 : Blo 916578 918827 := bstep (se 1 (by rfl) ⟨689120, by rfl⟩ : syracuseStep 918827 = 1378241) B1378241
theorem B2065715 : Blo 916578 2065715 := bstep (se 1 (by rfl) ⟨1549286, by rfl⟩ : syracuseStep 2065715 = 3098573) B3098573
theorem B918839 : Blo 916578 918839 := bstep (se 1 (by rfl) ⟨689129, by rfl⟩ : syracuseStep 918839 = 1378259) B1378259
theorem B1770817 : Blo 916578 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B1377611 : Blo 916578 1377611 := bstep (se 1 (by rfl) ⟨1033208, by rfl⟩ : syracuseStep 1377611 = 2066417) B2066417
theorem B918859 : Blo 916578 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B2065751 : Blo 916578 2065751 := bstep (se 1 (by rfl) ⟨1549313, by rfl⟩ : syracuseStep 2065751 = 3098627) B3098627
theorem B1377623 : Blo 916578 1377623 := bstep (se 1 (by rfl) ⟨1033217, by rfl⟩ : syracuseStep 1377623 = 2066435) B2066435
theorem B918871 : Blo 916578 918871 := bstep (se 1 (by rfl) ⟨689153, by rfl⟩ : syracuseStep 918871 = 1378307) B1378307
theorem B918891 : Blo 916578 918891 := bstep (se 1 (by rfl) ⟨689168, by rfl⟩ : syracuseStep 918891 = 1378337) B1378337
theorem B918903 : Blo 916578 918903 := bstep (se 1 (by rfl) ⟨689177, by rfl⟩ : syracuseStep 918903 = 1378355) B1378355
theorem B918923 : Blo 916578 918923 := bstep (se 1 (by rfl) ⟨689192, by rfl⟩ : syracuseStep 918923 = 1378385) B1378385
theorem B918935 : Blo 916578 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B1377689 : Blo 916578 1377689 := bstep (se 2 (by rfl) ⟨516633, by rfl⟩ : syracuseStep 1377689 = 1033267) B1033267
theorem B918955 : Blo 916578 918955 := bstep (se 1 (by rfl) ⟨689216, by rfl⟩ : syracuseStep 918955 = 1378433) B1378433
theorem B918967 : Blo 916578 918967 := bstep (se 1 (by rfl) ⟨689225, by rfl⟩ : syracuseStep 918967 = 1378451) B1378451
theorem B918987 : Blo 916578 918987 := bstep (se 1 (by rfl) ⟨689240, by rfl⟩ : syracuseStep 918987 = 1378481) B1378481
theorem B2328011 : Blo 916578 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B918999 : Blo 916578 918999 := bstep (se 1 (by rfl) ⟨689249, by rfl⟩ : syracuseStep 918999 = 1378499) B1378499
theorem B919019 : Blo 916578 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B919031 : Blo 916578 919031 := bstep (se 1 (by rfl) ⟨689273, by rfl⟩ : syracuseStep 919031 = 1378547) B1378547
theorem B2065931 : Blo 916578 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B1377803 : Blo 916578 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B919051 : Blo 916578 919051 := bstep (se 1 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 919051 = 1378577) B1378577
theorem B1377815 : Blo 916578 1377815 := bstep (se 1 (by rfl) ⟨1033361, by rfl⟩ : syracuseStep 1377815 = 2066723) B2066723
theorem B919063 : Blo 916578 919063 := bstep (se 1 (by rfl) ⟨689297, by rfl⟩ : syracuseStep 919063 = 1378595) B1378595
theorem B919083 : Blo 916578 919083 := bstep (se 1 (by rfl) ⟨689312, by rfl⟩ : syracuseStep 919083 = 1378625) B1378625
theorem B919095 : Blo 916578 919095 := bstep (se 1 (by rfl) ⟨689321, by rfl⟩ : syracuseStep 919095 = 1378643) B1378643
theorem B2065985 : Blo 916578 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B919115 : Blo 916578 919115 := bstep (se 1 (by rfl) ⟨689336, by rfl⟩ : syracuseStep 919115 = 1378673) B1378673
theorem B919127 : Blo 916578 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B1377881 : Blo 916578 1377881 := bstep (se 2 (by rfl) ⟨516705, by rfl⟩ : syracuseStep 1377881 = 1033411) B1033411
theorem B919147 : Blo 916578 919147 := bstep (se 1 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 919147 = 1378721) B1378721
theorem B919159 : Blo 916578 919159 := bstep (se 1 (by rfl) ⟨689369, by rfl⟩ : syracuseStep 919159 = 1378739) B1378739
theorem B919179 : Blo 916578 919179 := bstep (se 1 (by rfl) ⟨689384, by rfl⟩ : syracuseStep 919179 = 1378769) B1378769
theorem B919191 : Blo 916578 919191 := bstep (se 1 (by rfl) ⟨689393, by rfl⟩ : syracuseStep 919191 = 1378787) B1378787
theorem B919211 : Blo 916578 919211 := bstep (se 1 (by rfl) ⟨689408, by rfl⟩ : syracuseStep 919211 = 1378817) B1378817
theorem B919223 : Blo 916578 919223 := bstep (se 1 (by rfl) ⟨689417, by rfl⟩ : syracuseStep 919223 = 1378835) B1378835
theorem B1377995 : Blo 916578 1377995 := bstep (se 1 (by rfl) ⟨1033496, by rfl⟩ : syracuseStep 1377995 = 2066993) B2066993
theorem B919243 : Blo 916578 919243 := bstep (se 1 (by rfl) ⟨689432, by rfl⟩ : syracuseStep 919243 = 1378865) B1378865
theorem B1378007 : Blo 916578 1378007 := bstep (se 1 (by rfl) ⟨1033505, by rfl⟩ : syracuseStep 1378007 = 2067011) B2067011
theorem B919255 : Blo 916578 919255 := bstep (se 1 (by rfl) ⟨689441, by rfl⟩ : syracuseStep 919255 = 1378883) B1378883
theorem B919275 : Blo 916578 919275 := bstep (se 1 (by rfl) ⟨689456, by rfl⟩ : syracuseStep 919275 = 1378913) B1378913
theorem B919287 : Blo 916578 919287 := bstep (se 1 (by rfl) ⟨689465, by rfl⟩ : syracuseStep 919287 = 1378931) B1378931
theorem B919307 : Blo 916578 919307 := bstep (se 1 (by rfl) ⟨689480, by rfl⟩ : syracuseStep 919307 = 1378961) B1378961
theorem B919319 : Blo 916578 919319 := bstep (se 1 (by rfl) ⟨689489, by rfl⟩ : syracuseStep 919319 = 1378979) B1378979
theorem B2066201 : Blo 916578 2066201 := bstep (se 2 (by rfl) ⟨774825, by rfl⟩ : syracuseStep 2066201 = 1549651) B1549651
theorem B1378073 : Blo 916578 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B919339 : Blo 916578 919339 := bstep (se 1 (by rfl) ⟨689504, by rfl⟩ : syracuseStep 919339 = 1379009) B1379009
theorem B919351 : Blo 916578 919351 := bstep (se 1 (by rfl) ⟨689513, by rfl⟩ : syracuseStep 919351 = 1379027) B1379027
theorem B2328385 : Blo 916578 2328385 := bstep (se 2 (by rfl) ⟨873144, by rfl⟩ : syracuseStep 2328385 = 1746289) B1746289
theorem B919371 : Blo 916578 919371 := bstep (se 1 (by rfl) ⟨689528, by rfl⟩ : syracuseStep 919371 = 1379057) B1379057
theorem B919383 : Blo 916578 919383 := bstep (se 1 (by rfl) ⟨689537, by rfl⟩ : syracuseStep 919383 = 1379075) B1379075
theorem B919403 : Blo 916578 919403 := bstep (se 1 (by rfl) ⟨689552, by rfl⟩ : syracuseStep 919403 = 1379105) B1379105
theorem B2066291 : Blo 916578 2066291 := bstep (se 1 (by rfl) ⟨1549718, by rfl⟩ : syracuseStep 2066291 = 3099437) B3099437
theorem B9930613 : Blo 916578 9930613 := bstep (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) B930995
theorem B919415 : Blo 916578 919415 := bstep (se 1 (by rfl) ⟨689561, by rfl⟩ : syracuseStep 919415 = 1379123) B1379123
theorem B1771379 : Blo 916578 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1378187 : Blo 916578 1378187 := bstep (se 1 (by rfl) ⟨1033640, by rfl⟩ : syracuseStep 1378187 = 2067281) B2067281
theorem B919435 : Blo 916578 919435 := bstep (se 1 (by rfl) ⟨689576, by rfl⟩ : syracuseStep 919435 = 1379153) B1379153
theorem B2066327 : Blo 916578 2066327 := bstep (se 1 (by rfl) ⟨1549745, by rfl⟩ : syracuseStep 2066327 = 3099491) B3099491
theorem B1378199 : Blo 916578 1378199 := bstep (se 1 (by rfl) ⟨1033649, by rfl⟩ : syracuseStep 1378199 = 2067299) B2067299
theorem B919447 : Blo 916578 919447 := bstep (se 1 (by rfl) ⟨689585, by rfl⟩ : syracuseStep 919447 = 1379171) B1379171
theorem B919467 : Blo 916578 919467 := bstep (se 1 (by rfl) ⟨689600, by rfl⟩ : syracuseStep 919467 = 1379201) B1379201
theorem B919479 : Blo 916578 919479 := bstep (se 1 (by rfl) ⟨689609, by rfl⟩ : syracuseStep 919479 = 1379219) B1379219
theorem B919499 : Blo 916578 919499 := bstep (se 1 (by rfl) ⟨689624, by rfl⟩ : syracuseStep 919499 = 1379249) B1379249
theorem B919511 : Blo 916578 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B1378265 : Blo 916578 1378265 := bstep (se 2 (by rfl) ⟨516849, by rfl⟩ : syracuseStep 1378265 = 1033699) B1033699
theorem B919531 : Blo 916578 919531 := bstep (se 1 (by rfl) ⟨689648, by rfl⟩ : syracuseStep 919531 = 1379297) B1379297
theorem B919543 : Blo 916578 919543 := bstep (se 1 (by rfl) ⟨689657, by rfl⟩ : syracuseStep 919543 = 1379315) B1379315
theorem B919563 : Blo 916578 919563 := bstep (se 1 (by rfl) ⟨689672, by rfl⟩ : syracuseStep 919563 = 1379345) B1379345
theorem B919575 : Blo 916578 919575 := bstep (se 1 (by rfl) ⟨689681, by rfl⟩ : syracuseStep 919575 = 1379363) B1379363
theorem B919595 : Blo 916578 919595 := bstep (se 1 (by rfl) ⟨689696, by rfl⟩ : syracuseStep 919595 = 1379393) B1379393
theorem B919607 : Blo 916578 919607 := bstep (se 1 (by rfl) ⟨689705, by rfl⟩ : syracuseStep 919607 = 1379411) B1379411
theorem B2066507 : Blo 916578 2066507 := bstep (se 1 (by rfl) ⟨1549880, by rfl⟩ : syracuseStep 2066507 = 3099761) B3099761
theorem B1378379 : Blo 916578 1378379 := bstep (se 1 (by rfl) ⟨1033784, by rfl⟩ : syracuseStep 1378379 = 2067569) B2067569
theorem B919627 : Blo 916578 919627 := bstep (se 1 (by rfl) ⟨689720, by rfl⟩ : syracuseStep 919627 = 1379441) B1379441
theorem B1378391 : Blo 916578 1378391 := bstep (se 1 (by rfl) ⟨1033793, by rfl⟩ : syracuseStep 1378391 = 2067587) B2067587
theorem B919639 : Blo 916578 919639 := bstep (se 1 (by rfl) ⟨689729, by rfl⟩ : syracuseStep 919639 = 1379459) B1379459
theorem B919659 : Blo 916578 919659 := bstep (se 1 (by rfl) ⟨689744, by rfl⟩ : syracuseStep 919659 = 1379489) B1379489
theorem B919671 : Blo 916578 919671 := bstep (se 1 (by rfl) ⟨689753, by rfl⟩ : syracuseStep 919671 = 1379507) B1379507
theorem B2066561 : Blo 916578 2066561 := bstep (se 2 (by rfl) ⟨774960, by rfl⟩ : syracuseStep 2066561 = 1549921) B1549921
theorem B919691 : Blo 916578 919691 := bstep (se 1 (by rfl) ⟨689768, by rfl⟩ : syracuseStep 919691 = 1379537) B1379537
theorem B919703 : Blo 916578 919703 := bstep (se 1 (by rfl) ⟨689777, by rfl⟩ : syracuseStep 919703 = 1379555) B1379555
theorem B1378457 : Blo 916578 1378457 := bstep (se 2 (by rfl) ⟨516921, by rfl⟩ : syracuseStep 1378457 = 1033843) B1033843
theorem B919723 : Blo 916578 919723 := bstep (se 1 (by rfl) ⟨689792, by rfl⟩ : syracuseStep 919723 = 1379585) B1379585
theorem B919735 : Blo 916578 919735 := bstep (se 1 (by rfl) ⟨689801, by rfl⟩ : syracuseStep 919735 = 1379603) B1379603
theorem B919755 : Blo 916578 919755 := bstep (se 1 (by rfl) ⟨689816, by rfl⟩ : syracuseStep 919755 = 1379633) B1379633
theorem B919767 : Blo 916578 919767 := bstep (se 1 (by rfl) ⟨689825, by rfl⟩ : syracuseStep 919767 = 1379651) B1379651
theorem B919787 : Blo 916578 919787 := bstep (se 1 (by rfl) ⟨689840, by rfl⟩ : syracuseStep 919787 = 1379681) B1379681
theorem B919799 : Blo 916578 919799 := bstep (se 1 (by rfl) ⟨689849, by rfl⟩ : syracuseStep 919799 = 1379699) B1379699
theorem B1378571 : Blo 916578 1378571 := bstep (se 1 (by rfl) ⟨1033928, by rfl⟩ : syracuseStep 1378571 = 2067857) B2067857
theorem B919819 : Blo 916578 919819 := bstep (se 1 (by rfl) ⟨689864, by rfl⟩ : syracuseStep 919819 = 1379729) B1379729
theorem B1378583 : Blo 916578 1378583 := bstep (se 1 (by rfl) ⟨1033937, by rfl⟩ : syracuseStep 1378583 = 2067875) B2067875
theorem B919831 : Blo 916578 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B919851 : Blo 916578 919851 := bstep (se 1 (by rfl) ⟨689888, by rfl⟩ : syracuseStep 919851 = 1379777) B1379777
theorem B919863 : Blo 916578 919863 := bstep (se 1 (by rfl) ⟨689897, by rfl⟩ : syracuseStep 919863 = 1379795) B1379795
theorem B919883 : Blo 916578 919883 := bstep (se 1 (by rfl) ⟨689912, by rfl⟩ : syracuseStep 919883 = 1379825) B1379825
theorem B919895 : Blo 916578 919895 := bstep (se 1 (by rfl) ⟨689921, by rfl⟩ : syracuseStep 919895 = 1379843) B1379843
theorem B2066777 : Blo 916578 2066777 := bstep (se 2 (by rfl) ⟨775041, by rfl⟩ : syracuseStep 2066777 = 1550083) B1550083
theorem B1378649 : Blo 916578 1378649 := bstep (se 2 (by rfl) ⟨516993, by rfl⟩ : syracuseStep 1378649 = 1033987) B1033987
theorem B919915 : Blo 916578 919915 := bstep (se 1 (by rfl) ⟨689936, by rfl⟩ : syracuseStep 919915 = 1379873) B1379873
theorem B919927 : Blo 916578 919927 := bstep (se 1 (by rfl) ⟨689945, by rfl⟩ : syracuseStep 919927 = 1379891) B1379891
theorem B919947 : Blo 916578 919947 := bstep (se 1 (by rfl) ⟨689960, by rfl⟩ : syracuseStep 919947 = 1379921) B1379921
theorem B919959 : Blo 916578 919959 := bstep (se 1 (by rfl) ⟨689969, by rfl⟩ : syracuseStep 919959 = 1379939) B1379939
theorem B2328983 : Blo 916578 2328983 := bstep (se 1 (by rfl) ⟨1746737, by rfl⟩ : syracuseStep 2328983 = 3493475) B3493475
theorem B919979 : Blo 916578 919979 := bstep (se 1 (by rfl) ⟨689984, by rfl⟩ : syracuseStep 919979 = 1379969) B1379969
theorem B2066867 : Blo 916578 2066867 := bstep (se 1 (by rfl) ⟨1550150, by rfl⟩ : syracuseStep 2066867 = 3100301) B3100301
theorem B919991 : Blo 916578 919991 := bstep (se 1 (by rfl) ⟨689993, by rfl⟩ : syracuseStep 919991 = 1379987) B1379987
theorem B1378763 : Blo 916578 1378763 := bstep (se 1 (by rfl) ⟨1034072, by rfl⟩ : syracuseStep 1378763 = 2068145) B2068145
theorem B920011 : Blo 916578 920011 := bstep (se 1 (by rfl) ⟨690008, by rfl⟩ : syracuseStep 920011 = 1380017) B1380017
theorem B2066903 : Blo 916578 2066903 := bstep (se 1 (by rfl) ⟨1550177, by rfl⟩ : syracuseStep 2066903 = 3100355) B3100355
theorem B1378775 : Blo 916578 1378775 := bstep (se 1 (by rfl) ⟨1034081, by rfl⟩ : syracuseStep 1378775 = 2068163) B2068163
theorem B920023 : Blo 916578 920023 := bstep (se 1 (by rfl) ⟨690017, by rfl⟩ : syracuseStep 920023 = 1380035) B1380035
theorem B920043 : Blo 916578 920043 := bstep (se 1 (by rfl) ⟨690032, by rfl⟩ : syracuseStep 920043 = 1380065) B1380065
theorem B920055 : Blo 916578 920055 := bstep (se 1 (by rfl) ⟨690041, by rfl⟩ : syracuseStep 920055 = 1380083) B1380083
theorem B920075 : Blo 916578 920075 := bstep (se 1 (by rfl) ⟨690056, by rfl⟩ : syracuseStep 920075 = 1380113) B1380113
theorem B920087 : Blo 916578 920087 := bstep (se 1 (by rfl) ⟨690065, by rfl⟩ : syracuseStep 920087 = 1380131) B1380131
theorem B1378841 : Blo 916578 1378841 := bstep (se 2 (by rfl) ⟨517065, by rfl⟩ : syracuseStep 1378841 = 1034131) B1034131
theorem B920107 : Blo 916578 920107 := bstep (se 1 (by rfl) ⟨690080, by rfl⟩ : syracuseStep 920107 = 1380161) B1380161
theorem B920119 : Blo 916578 920119 := bstep (se 1 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 920119 = 1380179) B1380179
theorem B920139 : Blo 916578 920139 := bstep (se 1 (by rfl) ⟨690104, by rfl⟩ : syracuseStep 920139 = 1380209) B1380209
theorem B920151 : Blo 916578 920151 := bstep (se 1 (by rfl) ⟨690113, by rfl⟩ : syracuseStep 920151 = 1380227) B1380227
theorem B920171 : Blo 916578 920171 := bstep (se 1 (by rfl) ⟨690128, by rfl⟩ : syracuseStep 920171 = 1380257) B1380257
theorem B920183 : Blo 916578 920183 := bstep (se 1 (by rfl) ⟨690137, by rfl⟩ : syracuseStep 920183 = 1380275) B1380275
theorem B2067083 : Blo 916578 2067083 := bstep (se 1 (by rfl) ⟨1550312, by rfl⟩ : syracuseStep 2067083 = 3100625) B3100625
theorem B1378955 : Blo 916578 1378955 := bstep (se 1 (by rfl) ⟨1034216, by rfl⟩ : syracuseStep 1378955 = 2068433) B2068433
theorem B920203 : Blo 916578 920203 := bstep (se 1 (by rfl) ⟨690152, by rfl⟩ : syracuseStep 920203 = 1380305) B1380305
theorem B1378967 : Blo 916578 1378967 := bstep (se 1 (by rfl) ⟨1034225, by rfl⟩ : syracuseStep 1378967 = 2068451) B2068451
theorem B920215 : Blo 916578 920215 := bstep (se 1 (by rfl) ⟨690161, by rfl⟩ : syracuseStep 920215 = 1380323) B1380323
theorem B920235 : Blo 916578 920235 := bstep (se 1 (by rfl) ⟨690176, by rfl⟩ : syracuseStep 920235 = 1380353) B1380353
theorem B920247 : Blo 916578 920247 := bstep (se 1 (by rfl) ⟨690185, by rfl⟩ : syracuseStep 920247 = 1380371) B1380371
theorem B2067137 : Blo 916578 2067137 := bstep (se 2 (by rfl) ⟨775176, by rfl⟩ : syracuseStep 2067137 = 1550353) B1550353
theorem B920267 : Blo 916578 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B920279 : Blo 916578 920279 := bstep (se 1 (by rfl) ⟨690209, by rfl⟩ : syracuseStep 920279 = 1380419) B1380419
theorem B1379033 : Blo 916578 1379033 := bstep (se 2 (by rfl) ⟨517137, by rfl⟩ : syracuseStep 1379033 = 1034275) B1034275
theorem B6982361 : Blo 916578 6982361 := bstep (se 2 (by rfl) ⟨2618385, by rfl⟩ : syracuseStep 6982361 = 5236771) B5236771
theorem B920299 : Blo 916578 920299 := bstep (se 1 (by rfl) ⟨690224, by rfl⟩ : syracuseStep 920299 = 1380449) B1380449
theorem B920311 : Blo 916578 920311 := bstep (se 1 (by rfl) ⟨690233, by rfl⟩ : syracuseStep 920311 = 1380467) B1380467
theorem B920331 : Blo 916578 920331 := bstep (se 1 (by rfl) ⟨690248, by rfl⟩ : syracuseStep 920331 = 1380497) B1380497
theorem B920343 : Blo 916578 920343 := bstep (se 1 (by rfl) ⟨690257, by rfl⟩ : syracuseStep 920343 = 1380515) B1380515
theorem B920363 : Blo 916578 920363 := bstep (se 1 (by rfl) ⟨690272, by rfl⟩ : syracuseStep 920363 = 1380545) B1380545
theorem B920375 : Blo 916578 920375 := bstep (se 1 (by rfl) ⟨690281, by rfl⟩ : syracuseStep 920375 = 1380563) B1380563
theorem B1379147 : Blo 916578 1379147 := bstep (se 1 (by rfl) ⟨1034360, by rfl⟩ : syracuseStep 1379147 = 2068721) B2068721
theorem B920395 : Blo 916578 920395 := bstep (se 1 (by rfl) ⟨690296, by rfl⟩ : syracuseStep 920395 = 1380593) B1380593
theorem B1379159 : Blo 916578 1379159 := bstep (se 1 (by rfl) ⟨1034369, by rfl⟩ : syracuseStep 1379159 = 2068739) B2068739
theorem B920407 : Blo 916578 920407 := bstep (se 1 (by rfl) ⟨690305, by rfl⟩ : syracuseStep 920407 = 1380611) B1380611
theorem B920427 : Blo 916578 920427 := bstep (se 1 (by rfl) ⟨690320, by rfl⟩ : syracuseStep 920427 = 1380641) B1380641
theorem B920439 : Blo 916578 920439 := bstep (se 1 (by rfl) ⟨690329, by rfl⟩ : syracuseStep 920439 = 1380659) B1380659
theorem B920459 : Blo 916578 920459 := bstep (se 1 (by rfl) ⟨690344, by rfl⟩ : syracuseStep 920459 = 1380689) B1380689
theorem B920471 : Blo 916578 920471 := bstep (se 1 (by rfl) ⟨690353, by rfl⟩ : syracuseStep 920471 = 1380707) B1380707
theorem B2067353 : Blo 916578 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B1379225 : Blo 916578 1379225 := bstep (se 2 (by rfl) ⟨517209, by rfl⟩ : syracuseStep 1379225 = 1034419) B1034419
theorem B920491 : Blo 916578 920491 := bstep (se 1 (by rfl) ⟨690368, by rfl⟩ : syracuseStep 920491 = 1380737) B1380737
theorem B920503 : Blo 916578 920503 := bstep (se 1 (by rfl) ⟨690377, by rfl⟩ : syracuseStep 920503 = 1380755) B1380755
theorem B920523 : Blo 916578 920523 := bstep (se 1 (by rfl) ⟨690392, by rfl⟩ : syracuseStep 920523 = 1380785) B1380785
theorem B920535 : Blo 916578 920535 := bstep (se 1 (by rfl) ⟨690401, by rfl⟩ : syracuseStep 920535 = 1380803) B1380803
theorem B920555 : Blo 916578 920555 := bstep (se 1 (by rfl) ⟨690416, by rfl⟩ : syracuseStep 920555 = 1380833) B1380833
theorem B2067443 : Blo 916578 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B920567 : Blo 916578 920567 := bstep (se 1 (by rfl) ⟨690425, by rfl⟩ : syracuseStep 920567 = 1380851) B1380851
theorem B1379339 : Blo 916578 1379339 := bstep (se 1 (by rfl) ⟨1034504, by rfl⟩ : syracuseStep 1379339 = 2069009) B2069009
theorem B2067479 : Blo 916578 2067479 := bstep (se 1 (by rfl) ⟨1550609, by rfl⟩ : syracuseStep 2067479 = 3101219) B3101219
theorem B1379351 : Blo 916578 1379351 := bstep (se 1 (by rfl) ⟨1034513, by rfl⟩ : syracuseStep 1379351 = 2069027) B2069027
theorem B4656203 : Blo 916578 4656203 := bstep (se 1 (by rfl) ⟨3492152, by rfl⟩ : syracuseStep 4656203 = 6984305) B6984305
theorem B4787275 : Blo 916578 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B1379417 : Blo 916578 1379417 := bstep (se 2 (by rfl) ⟨517281, by rfl⟩ : syracuseStep 1379417 = 1034563) B1034563
theorem B2329793 : Blo 916578 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B2067659 : Blo 916578 2067659 := bstep (se 1 (by rfl) ⟨1550744, by rfl⟩ : syracuseStep 2067659 = 3101489) B3101489
theorem B1379531 : Blo 916578 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1379543 : Blo 916578 1379543 := bstep (se 1 (by rfl) ⟨1034657, by rfl⟩ : syracuseStep 1379543 = 2069315) B2069315
theorem B3312857 : Blo 916578 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B2067713 : Blo 916578 2067713 := bstep (se 2 (by rfl) ⟨775392, by rfl⟩ : syracuseStep 2067713 = 1550785) B1550785
theorem B1379609 : Blo 916578 1379609 := bstep (se 2 (by rfl) ⟨517353, by rfl⟩ : syracuseStep 1379609 = 1034707) B1034707
theorem B1379723 : Blo 916578 1379723 := bstep (se 1 (by rfl) ⟨1034792, by rfl⟩ : syracuseStep 1379723 = 2069585) B2069585
theorem B1379735 : Blo 916578 1379735 := bstep (se 1 (by rfl) ⟨1034801, by rfl⟩ : syracuseStep 1379735 = 2069603) B2069603
theorem B1510859 : Blo 916578 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B2067929 : Blo 916578 2067929 := bstep (se 2 (by rfl) ⟨775473, by rfl⟩ : syracuseStep 2067929 = 1550947) B1550947
theorem B1379801 : Blo 916578 1379801 := bstep (se 2 (by rfl) ⟨517425, by rfl⟩ : syracuseStep 1379801 = 1034851) B1034851
theorem B1740275 : Blo 916578 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B2068019 : Blo 916578 2068019 := bstep (se 1 (by rfl) ⟨1551014, by rfl⟩ : syracuseStep 2068019 = 3102029) B3102029
theorem B7835201 : Blo 916578 7835201 := bstep (se 2 (by rfl) ⟨2938200, by rfl⟩ : syracuseStep 7835201 = 5876401) B5876401
theorem B1379915 : Blo 916578 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B2068055 : Blo 916578 2068055 := bstep (se 1 (by rfl) ⟨1551041, by rfl⟩ : syracuseStep 2068055 = 3102083) B3102083
theorem B1379927 : Blo 916578 1379927 := bstep (se 1 (by rfl) ⟨1034945, by rfl⟩ : syracuseStep 1379927 = 2069891) B2069891
theorem B1379993 : Blo 916578 1379993 := bstep (se 2 (by rfl) ⟨517497, by rfl⟩ : syracuseStep 1379993 = 1034995) B1034995
theorem B1740503 : Blo 916578 1740503 := bstep (se 1 (by rfl) ⟨1305377, by rfl⟩ : syracuseStep 1740503 = 2610755) B2610755
theorem B2068235 : Blo 916578 2068235 := bstep (se 1 (by rfl) ⟨1551176, by rfl⟩ : syracuseStep 2068235 = 3102353) B3102353
theorem B1380107 : Blo 916578 1380107 := bstep (se 1 (by rfl) ⟨1035080, by rfl⟩ : syracuseStep 1380107 = 2070161) B2070161
theorem B1380119 : Blo 916578 1380119 := bstep (se 1 (by rfl) ⟨1035089, by rfl⟩ : syracuseStep 1380119 = 2070179) B2070179
theorem B2068289 : Blo 916578 2068289 := bstep (se 2 (by rfl) ⟨775608, by rfl⟩ : syracuseStep 2068289 = 1551217) B1551217
theorem B1380185 : Blo 916578 1380185 := bstep (se 2 (by rfl) ⟨517569, by rfl⟩ : syracuseStep 1380185 = 1035139) B1035139
theorem B1380299 : Blo 916578 1380299 := bstep (se 1 (by rfl) ⟨1035224, by rfl⟩ : syracuseStep 1380299 = 2070449) B2070449
theorem B1380311 : Blo 916578 1380311 := bstep (se 1 (by rfl) ⟨1035233, by rfl⟩ : syracuseStep 1380311 = 2070467) B2070467
theorem B1740761 : Blo 916578 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B2068505 : Blo 916578 2068505 := bstep (se 2 (by rfl) ⟨775689, by rfl⟩ : syracuseStep 2068505 = 1551379) B1551379
theorem B1380377 : Blo 916578 1380377 := bstep (se 2 (by rfl) ⟨517641, by rfl⟩ : syracuseStep 1380377 = 1035283) B1035283
theorem B7082059 : Blo 916578 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B2068595 : Blo 916578 2068595 := bstep (se 1 (by rfl) ⟨1551446, by rfl⟩ : syracuseStep 2068595 = 3102893) B3102893
theorem B1380491 : Blo 916578 1380491 := bstep (se 1 (by rfl) ⟨1035368, by rfl⟩ : syracuseStep 1380491 = 2070737) B2070737
theorem B2068631 : Blo 916578 2068631 := bstep (se 1 (by rfl) ⟨1551473, by rfl⟩ : syracuseStep 2068631 = 3102947) B3102947
theorem B1380503 : Blo 916578 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B1380569 : Blo 916578 1380569 := bstep (se 2 (by rfl) ⟨517713, by rfl⟩ : syracuseStep 1380569 = 1035427) B1035427
theorem B2068811 : Blo 916578 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1380683 : Blo 916578 1380683 := bstep (se 1 (by rfl) ⟨1035512, by rfl⟩ : syracuseStep 1380683 = 2071025) B2071025
theorem B1380695 : Blo 916578 1380695 := bstep (se 1 (by rfl) ⟨1035521, by rfl⟩ : syracuseStep 1380695 = 2071043) B2071043
theorem B2232665 : Blo 916578 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B1741171 : Blo 916578 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B2068865 : Blo 916578 2068865 := bstep (se 2 (by rfl) ⟨775824, by rfl⟩ : syracuseStep 2068865 = 1551649) B1551649
theorem B6623639 : Blo 916578 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B1380761 : Blo 916578 1380761 := bstep (se 2 (by rfl) ⟨517785, by rfl⟩ : syracuseStep 1380761 = 1035571) B1035571
theorem B2069081 : Blo 916578 2069081 := bstep (se 2 (by rfl) ⟨775905, by rfl⟩ : syracuseStep 2069081 = 1551811) B1551811
theorem B2069171 : Blo 916578 2069171 := bstep (se 1 (by rfl) ⟨1551878, by rfl⟩ : syracuseStep 2069171 = 3103757) B3103757
theorem B2069207 : Blo 916578 2069207 := bstep (se 1 (by rfl) ⟨1551905, by rfl⟩ : syracuseStep 2069207 = 3103811) B3103811
theorem B3969809 : Blo 916578 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B4657985 : Blo 916578 4657985 := bstep (se 2 (by rfl) ⟨1746744, by rfl⟩ : syracuseStep 4657985 = 3493489) B3493489
theorem B1741657 : Blo 916578 1741657 := bstep (se 2 (by rfl) ⟨653121, by rfl⟩ : syracuseStep 1741657 = 1306243) B1306243
theorem B2069387 : Blo 916578 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B2069441 : Blo 916578 2069441 := bstep (se 2 (by rfl) ⟨776040, by rfl⟩ : syracuseStep 2069441 = 1552081) B1552081
theorem B2069657 : Blo 916578 2069657 := bstep (se 2 (by rfl) ⟨776121, by rfl⟩ : syracuseStep 2069657 = 1552243) B1552243
theorem B13407437 : Blo 916578 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B2069747 : Blo 916578 2069747 := bstep (se 1 (by rfl) ⟨1552310, by rfl⟩ : syracuseStep 2069747 = 3104621) B3104621
theorem B2069783 : Blo 916578 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B2790749 : Blo 916578 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B7968131 : Blo 916578 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1742219 : Blo 916578 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B2069963 : Blo 916578 2069963 := bstep (se 1 (by rfl) ⟨1552472, by rfl⟩ : syracuseStep 2069963 = 3104945) B3104945
theorem B2070017 : Blo 916578 2070017 := bstep (se 2 (by rfl) ⟨776256, by rfl⟩ : syracuseStep 2070017 = 1552513) B1552513
theorem B1742401 : Blo 916578 1742401 := bstep (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) B1306801
theorem B2070233 : Blo 916578 2070233 := bstep (se 2 (by rfl) ⟨776337, by rfl⟩ : syracuseStep 2070233 = 1552675) B1552675
theorem B2070323 : Blo 916578 2070323 := bstep (se 1 (by rfl) ⟨1552742, by rfl⟩ : syracuseStep 2070323 = 3105485) B3105485
theorem B2070359 : Blo 916578 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B2070539 : Blo 916578 2070539 := bstep (se 1 (by rfl) ⟨1552904, by rfl⟩ : syracuseStep 2070539 = 3105809) B3105809
theorem B6985763 : Blo 916578 6985763 := bstep (se 1 (by rfl) ⟨5239322, by rfl⟩ : syracuseStep 6985763 = 10478645) B10478645
theorem B2070593 : Blo 916578 2070593 := bstep (se 2 (by rfl) ⟨776472, by rfl⟩ : syracuseStep 2070593 = 1552945) B1552945
theorem B21174533 : Blo 916578 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B1743115 : Blo 916578 1743115 := bstep (se 1 (by rfl) ⟨1307336, by rfl⟩ : syracuseStep 1743115 = 2614673) B2614673
theorem B2070809 : Blo 916578 2070809 := bstep (se 2 (by rfl) ⟨776553, by rfl⟩ : syracuseStep 2070809 = 1553107) B1553107
theorem B1743191 : Blo 916578 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B2070899 : Blo 916578 2070899 := bstep (se 1 (by rfl) ⟨1553174, by rfl⟩ : syracuseStep 2070899 = 3106349) B3106349
theorem B2070935 : Blo 916578 2070935 := bstep (se 1 (by rfl) ⟨1553201, by rfl⟩ : syracuseStep 2070935 = 3106403) B3106403
theorem B2071115 : Blo 916578 2071115 := bstep (se 1 (by rfl) ⟨1553336, by rfl⟩ : syracuseStep 2071115 = 3106673) B3106673
theorem B2071169 : Blo 916578 2071169 := bstep (se 2 (by rfl) ⟨776688, by rfl⟩ : syracuseStep 2071169 = 1553377) B1553377
theorem B15702659 : Blo 916578 15702659 := bstep (se 1 (by rfl) ⟨11776994, by rfl⟩ : syracuseStep 15702659 = 23553989) B23553989
theorem B4659929 : Blo 916578 4659929 := bstep (se 2 (by rfl) ⟨1747473, by rfl⟩ : syracuseStep 4659929 = 3494947) B3494947
theorem B1547147 : Blo 916578 1547147 := bstep (se 1 (by rfl) ⟨1160360, by rfl⟩ : syracuseStep 1547147 = 2320721) B2320721
theorem B1743859 : Blo 916578 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B1547275 : Blo 916578 1547275 := bstep (se 1 (by rfl) ⟨1160456, by rfl⟩ : syracuseStep 1547275 = 2320913) B2320913
theorem B3480641 : Blo 916578 3480641 := bstep (se 2 (by rfl) ⟨1305240, by rfl⟩ : syracuseStep 3480641 = 2610481) B2610481
theorem B6626405 : Blo 916578 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B1547417 : Blo 916578 1547417 := bstep (se 2 (by rfl) ⟨580281, by rfl⟩ : syracuseStep 1547417 = 1160563) B1160563
theorem B2038937 : Blo 916578 2038937 := bstep (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) B1529203
theorem B1744087 : Blo 916578 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B1547545 : Blo 916578 1547545 := bstep (se 2 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 1547545 = 1160659) B1160659
theorem B1744193 : Blo 916578 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B1744345 : Blo 916578 1744345 := bstep (se 2 (by rfl) ⟨654129, by rfl⟩ : syracuseStep 1744345 = 1308259) B1308259
theorem B1548119 : Blo 916578 1548119 := bstep (se 1 (by rfl) ⟨1161089, by rfl⟩ : syracuseStep 1548119 = 2322179) B2322179
theorem B1548247 : Blo 916578 1548247 := bstep (se 1 (by rfl) ⟨1161185, by rfl⟩ : syracuseStep 1548247 = 2322371) B2322371
theorem B12754979 : Blo 916578 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B3482129 : Blo 916578 3482129 := bstep (se 2 (by rfl) ⟨1305798, by rfl⟩ : syracuseStep 3482129 = 2611597) B2611597
theorem B1548875 : Blo 916578 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1549003 : Blo 916578 1549003 := bstep (se 1 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 1549003 = 2323505) B2323505
theorem B1745651 : Blo 916578 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B1549145 : Blo 916578 1549145 := bstep (se 2 (by rfl) ⟨580929, by rfl⟩ : syracuseStep 1549145 = 1161859) B1161859
theorem B1745803 : Blo 916578 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B3482585 : Blo 916578 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B1549273 : Blo 916578 1549273 := bstep (se 2 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 1549273 = 1161955) B1161955
theorem B2204747 : Blo 916578 2204747 := bstep (se 1 (by rfl) ⟨1653560, by rfl⟩ : syracuseStep 2204747 = 3307121) B3307121
theorem B3482797 : Blo 916578 3482797 := bstep (se 3 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 3482797 = 1306049) B1306049
theorem B1746137 : Blo 916578 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B3483101 : Blo 916578 3483101 := bstep (se 3 (by rfl) ⟨653081, by rfl⟩ : syracuseStep 3483101 = 1306163) B1306163
theorem B7841285 : Blo 916578 7841285 := bstep (se 4 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 7841285 = 1470241) B1470241
theorem B1549847 : Blo 916578 1549847 := bstep (se 1 (by rfl) ⟨1162385, by rfl⟩ : syracuseStep 1549847 = 2324771) B2324771
theorem B1549975 : Blo 916578 1549975 := bstep (se 1 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 1549975 = 2324963) B2324963
theorem B1746775 : Blo 916578 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B9939095 : Blo 916578 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B1550603 : Blo 916578 1550603 := bstep (se 1 (by rfl) ⟨1162952, by rfl⟩ : syracuseStep 1550603 = 2325905) B2325905
theorem B1550731 : Blo 916578 1550731 := bstep (se 1 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 1550731 = 2326097) B2326097
theorem B1550873 : Blo 916578 1550873 := bstep (se 2 (by rfl) ⟨581577, by rfl⟩ : syracuseStep 1550873 = 1163155) B1163155
theorem B1747595 : Blo 916578 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B1551001 : Blo 916578 1551001 := bstep (se 2 (by rfl) ⟨581625, by rfl⟩ : syracuseStep 1551001 = 1163251) B1163251
theorem B1747649 : Blo 916578 1747649 := bstep (se 2 (by rfl) ⟨655368, by rfl⟩ : syracuseStep 1747649 = 1310737) B1310737
theorem B10464065 : Blo 916578 10464065 := bstep (se 2 (by rfl) ⟨3924024, by rfl⟩ : syracuseStep 10464065 = 7848049) B7848049
theorem B5581669 : Blo 916578 5581669 := bstep (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) B1046563
theorem B1813463 : Blo 916578 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B56503331 : Blo 916578 56503331 := bstep (se 1 (by rfl) ⟨42377498, by rfl⟩ : syracuseStep 56503331 = 84754997) B84754997
theorem B1551575 : Blo 916578 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B1551703 : Blo 916578 1551703 := bstep (se 1 (by rfl) ⟨1163777, by rfl⟩ : syracuseStep 1551703 = 2327555) B2327555
theorem B35794325 : Blo 916578 35794325 := bstep (se 6 (by rfl) ⟨838929, by rfl⟩ : syracuseStep 35794325 = 1677859) B1677859
theorem B2207179 : Blo 916578 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B31763981 : Blo 916578 31763981 := bstep (se 3 (by rfl) ⟨5955746, by rfl⟩ : syracuseStep 31763981 = 11911493) B11911493
theorem B1552331 : Blo 916578 1552331 := bstep (se 1 (by rfl) ⟨1164248, by rfl⟩ : syracuseStep 1552331 = 2328497) B2328497
theorem B3485699 : Blo 916578 3485699 := bstep (se 1 (by rfl) ⟨2614274, by rfl⟩ : syracuseStep 3485699 = 5228549) B5228549
theorem B3485713 : Blo 916578 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B5222465 : Blo 916578 5222465 := bstep (se 2 (by rfl) ⟨1958424, by rfl⟩ : syracuseStep 5222465 = 3916849) B3916849
theorem B1552459 : Blo 916578 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1552601 : Blo 916578 1552601 := bstep (se 2 (by rfl) ⟨582225, by rfl⟩ : syracuseStep 1552601 = 1164451) B1164451
theorem B3486017 : Blo 916578 3486017 := bstep (se 2 (by rfl) ⟨1307256, by rfl⟩ : syracuseStep 3486017 = 2614513) B2614513
theorem B1552729 : Blo 916578 1552729 := bstep (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) B1164547
theorem B2208563 : Blo 916578 2208563 := bstep (se 1 (by rfl) ⟨1656422, by rfl⟩ : syracuseStep 2208563 = 3312845) B3312845
theorem B1553303 : Blo 916578 1553303 := bstep (se 1 (by rfl) ⟨1164977, by rfl⟩ : syracuseStep 1553303 = 2329955) B2329955
theorem B3486685 : Blo 916578 3486685 := bstep (se 3 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 3486685 = 1307507) B1307507
theorem B1553431 : Blo 916578 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B4404611 : Blo 916578 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B3094091 : Blo 916578 3094091 := bstep (se 1 (by rfl) ⟨2320568, by rfl⟩ : syracuseStep 3094091 = 4641137) B4641137
theorem B4961893 : Blo 916578 4961893 := bstep (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) B930355
theorem B1160983 : Blo 916578 1160983 := bstep (se 1 (by rfl) ⟨870737, by rfl⟩ : syracuseStep 1160983 = 1741475) B1741475
theorem B3094361 : Blo 916578 3094361 := bstep (se 2 (by rfl) ⟨1160385, by rfl⟩ : syracuseStep 3094361 = 2320771) B2320771
theorem B9910289 : Blo 916578 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B12564497 : Blo 916578 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B4241497 : Blo 916578 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B3487961 : Blo 916578 3487961 := bstep (se 2 (by rfl) ⟨1307985, by rfl⟩ : syracuseStep 3487961 = 2615971) B2615971
theorem B3095063 : Blo 916578 3095063 := bstep (se 1 (by rfl) ⟨2321297, by rfl⟩ : syracuseStep 3095063 = 4642595) B4642595
theorem B1161803 : Blo 916578 1161803 := bstep (se 1 (by rfl) ⟨871352, by rfl⟩ : syracuseStep 1161803 = 1742705) B1742705
theorem B11778635 : Blo 916578 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B5880707 : Blo 916578 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B1653655 : Blo 916578 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B11189171 : Blo 916578 11189171 := bstep (se 1 (by rfl) ⟨8391878, by rfl⟩ : syracuseStep 11189171 = 16783757) B16783757
theorem B81476549 : Blo 916578 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1031179 : Blo 916578 1031179 := bstep (se 1 (by rfl) ⟨773384, by rfl⟩ : syracuseStep 1031179 = 1546769) B1546769
theorem B3095603 : Blo 916578 3095603 := bstep (se 1 (by rfl) ⟨2321702, by rfl⟩ : syracuseStep 3095603 = 4643405) B4643405
theorem B1031287 : Blo 916578 1031287 := bstep (se 1 (by rfl) ⟨773465, by rfl⟩ : syracuseStep 1031287 = 1546931) B1546931
theorem B1162507 : Blo 916578 1162507 := bstep (se 1 (by rfl) ⟨871880, by rfl⟩ : syracuseStep 1162507 = 1743761) B1743761
theorem B1031467 : Blo 916578 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B3095873 : Blo 916578 3095873 := bstep (se 2 (by rfl) ⟨1160952, by rfl⟩ : syracuseStep 3095873 = 2321905) B2321905
theorem B1031575 : Blo 916578 1031575 := bstep (se 1 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 1031575 = 1547363) B1547363
theorem B1162775 : Blo 916578 1162775 := bstep (se 1 (by rfl) ⟨872081, by rfl⟩ : syracuseStep 1162775 = 1744163) B1744163
theorem B1031755 : Blo 916578 1031755 := bstep (se 1 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 1031755 = 1547633) B1547633
theorem B5586533 : Blo 916578 5586533 := bstep (se 4 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 5586533 = 1047475) B1047475
theorem B1031863 : Blo 916578 1031863 := bstep (se 1 (by rfl) ⟨773897, by rfl⟩ : syracuseStep 1031863 = 1547795) B1547795
theorem B4964141 : Blo 916578 4964141 := bstep (se 3 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 4964141 = 1861553) B1861553
theorem B3489587 : Blo 916578 3489587 := bstep (se 1 (by rfl) ⟨2617190, by rfl⟩ : syracuseStep 3489587 = 5234381) B5234381
theorem B3489601 : Blo 916578 3489601 := bstep (se 2 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 3489601 = 2617201) B2617201
theorem B3096413 : Blo 916578 3096413 := bstep (se 3 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 3096413 = 1161155) B1161155
theorem B18825061 : Blo 916578 18825061 := bstep (se 4 (by rfl) ⟨1764849, by rfl⟩ : syracuseStep 18825061 = 3529699) B3529699
theorem B1032043 : Blo 916578 1032043 := bstep (se 1 (by rfl) ⟨774032, by rfl⟩ : syracuseStep 1032043 = 1548065) B1548065
theorem B1032151 : Blo 916578 1032151 := bstep (se 1 (by rfl) ⟨774113, by rfl⟩ : syracuseStep 1032151 = 1548227) B1548227
theorem B17678411 : Blo 916578 17678411 := bstep (se 1 (by rfl) ⟨13258808, by rfl⟩ : syracuseStep 17678411 = 26517617) B26517617
theorem B1032331 : Blo 916578 1032331 := bstep (se 1 (by rfl) ⟨774248, by rfl⟩ : syracuseStep 1032331 = 1548497) B1548497
theorem B1654987 : Blo 916578 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B1163479 : Blo 916578 1163479 := bstep (se 1 (by rfl) ⟨872609, by rfl⟩ : syracuseStep 1163479 = 1745219) B1745219
theorem B1032439 : Blo 916578 1032439 := bstep (se 1 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 1032439 = 1548659) B1548659
theorem B3359027 : Blo 916578 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B3916097 : Blo 916578 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B7848323 : Blo 916578 7848323 := bstep (se 1 (by rfl) ⟨5886242, by rfl⟩ : syracuseStep 7848323 = 11772485) B11772485
theorem B1032619 : Blo 916578 1032619 := bstep (se 1 (by rfl) ⟨774464, by rfl⟩ : syracuseStep 1032619 = 1548929) B1548929
theorem B1032727 : Blo 916578 1032727 := bstep (se 1 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 1032727 = 1549091) B1549091
theorem B163627573 : Blo 916578 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B29803139 : Blo 916578 29803139 := bstep (se 1 (by rfl) ⟨22352354, by rfl⟩ : syracuseStep 29803139 = 44704709) B44704709
theorem B1032907 : Blo 916578 1032907 := bstep (se 1 (by rfl) ⟨774680, by rfl⟩ : syracuseStep 1032907 = 1549361) B1549361
theorem B4965137 : Blo 916578 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1033015 : Blo 916578 1033015 := bstep (se 1 (by rfl) ⟨774761, by rfl⟩ : syracuseStep 1033015 = 1549523) B1549523
theorem B3097547 : Blo 916578 3097547 := bstep (se 1 (by rfl) ⟨2323160, by rfl⟩ : syracuseStep 3097547 = 4646321) B4646321
theorem B1033195 : Blo 916578 1033195 := bstep (se 1 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 1033195 = 1549793) B1549793
theorem B1655795 : Blo 916578 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1033303 : Blo 916578 1033303 := bstep (se 1 (by rfl) ⟨774977, by rfl⟩ : syracuseStep 1033303 = 1549955) B1549955
theorem B3097817 : Blo 916578 3097817 := bstep (se 2 (by rfl) ⟨1161681, by rfl⟩ : syracuseStep 3097817 = 2323363) B2323363
theorem B1033483 : Blo 916578 1033483 := bstep (se 1 (by rfl) ⟨775112, by rfl⟩ : syracuseStep 1033483 = 1550225) B1550225
theorem B5227841 : Blo 916578 5227841 := bstep (se 2 (by rfl) ⟨1960440, by rfl⟩ : syracuseStep 5227841 = 3920881) B3920881
theorem B1033591 : Blo 916578 1033591 := bstep (se 1 (by rfl) ⟨775193, by rfl⟩ : syracuseStep 1033591 = 1550387) B1550387
theorem B1033771 : Blo 916578 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B1033879 : Blo 916578 1033879 := bstep (se 1 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 1033879 = 1550819) B1550819
theorem B1394329 : Blo 916578 1394329 := bstep (se 2 (by rfl) ⟨522873, by rfl⟩ : syracuseStep 1394329 = 1045747) B1045747
theorem B3491531 : Blo 916578 3491531 := bstep (se 1 (by rfl) ⟨2618648, by rfl⟩ : syracuseStep 3491531 = 5237297) B5237297
theorem B3491545 : Blo 916578 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B3917585 : Blo 916578 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B1034059 : Blo 916578 1034059 := bstep (se 1 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 1034059 = 1551089) B1551089
theorem B3098519 : Blo 916578 3098519 := bstep (se 1 (by rfl) ⟨2323889, by rfl⟩ : syracuseStep 3098519 = 4647779) B4647779
theorem B1034167 : Blo 916578 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B1656769 : Blo 916578 1656769 := bstep (se 2 (by rfl) ⟨621288, by rfl⟩ : syracuseStep 1656769 = 1242577) B1242577
theorem B4409437 : Blo 916578 4409437 := bstep (se 3 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 4409437 = 1653539) B1653539
theorem B1034347 : Blo 916578 1034347 := bstep (se 1 (by rfl) ⟨775760, by rfl⟩ : syracuseStep 1034347 = 1551521) B1551521
theorem B23873687 : Blo 916578 23873687 := bstep (se 1 (by rfl) ⟨17905265, by rfl⟩ : syracuseStep 23873687 = 35810531) B35810531
theorem B1034455 : Blo 916578 1034455 := bstep (se 1 (by rfl) ⟨775841, by rfl⟩ : syracuseStep 1034455 = 1551683) B1551683
theorem B1034635 : Blo 916578 1034635 := bstep (se 1 (by rfl) ⟨775976, by rfl⟩ : syracuseStep 1034635 = 1551953) B1551953
theorem B9947569 : Blo 916578 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B3099059 : Blo 916578 3099059 := bstep (se 1 (by rfl) ⟨2324294, by rfl⟩ : syracuseStep 3099059 = 4648589) B4648589
theorem B1034743 : Blo 916578 1034743 := bstep (se 1 (by rfl) ⟨776057, by rfl⟩ : syracuseStep 1034743 = 1552115) B1552115
theorem B1395289 : Blo 916578 1395289 := bstep (se 2 (by rfl) ⟨523233, by rfl⟩ : syracuseStep 1395289 = 1046467) B1046467
theorem B3492503 : Blo 916578 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B1034923 : Blo 916578 1034923 := bstep (se 1 (by rfl) ⟨776192, by rfl⟩ : syracuseStep 1034923 = 1552385) B1552385
theorem B3099329 : Blo 916578 3099329 := bstep (se 2 (by rfl) ⟨1162248, by rfl⟩ : syracuseStep 3099329 = 2324497) B2324497
theorem B3918557 : Blo 916578 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B1035031 : Blo 916578 1035031 := bstep (se 1 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 1035031 = 1552547) B1552547
theorem B6277981 : Blo 916578 6277981 := bstep (se 3 (by rfl) ⟨1177121, by rfl⟩ : syracuseStep 6277981 = 2354243) B2354243
theorem B7457629 : Blo 916578 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B1035211 : Blo 916578 1035211 := bstep (se 1 (by rfl) ⟨776408, by rfl⟩ : syracuseStep 1035211 = 1552817) B1552817
theorem B11160611 : Blo 916578 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B1035319 : Blo 916578 1035319 := bstep (se 1 (by rfl) ⟨776489, by rfl⟩ : syracuseStep 1035319 = 1552979) B1552979
theorem B31771723 : Blo 916578 31771723 := bstep (se 1 (by rfl) ⟨23828792, by rfl⟩ : syracuseStep 31771723 = 47657585) B47657585
theorem B5590109 : Blo 916578 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B3099869 : Blo 916578 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B1035499 : Blo 916578 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B6278417 : Blo 916578 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B1035607 : Blo 916578 1035607 := bstep (se 1 (by rfl) ⟨776705, by rfl⟩ : syracuseStep 1035607 = 1553411) B1553411
theorem B7458149 : Blo 916578 7458149 := bstep (se 4 (by rfl) ⟨699201, by rfl⟩ : syracuseStep 7458149 = 1398403) B1398403
theorem B35311301 : Blo 916578 35311301 := bstep (se 4 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 35311301 = 6620869) B6620869
theorem B3493763 : Blo 916578 3493763 := bstep (se 1 (by rfl) ⟨2620322, by rfl⟩ : syracuseStep 3493763 = 5240645) B5240645
theorem B4640813 : Blo 916578 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B7065805 : Blo 916578 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B3101003 : Blo 916578 3101003 := bstep (se 1 (by rfl) ⟨2325752, by rfl⟩ : syracuseStep 3101003 = 4651505) B4651505
theorem B1986905 : Blo 916578 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B3101273 : Blo 916578 3101273 := bstep (se 2 (by rfl) ⟨1162977, by rfl⟩ : syracuseStep 3101273 = 2325955) B2325955
theorem B6443821 : Blo 916578 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B8377181 : Blo 916578 8377181 := bstep (se 3 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 8377181 = 3141443) B3141443
theorem B3724177 : Blo 916578 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B2937779 : Blo 916578 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B2610265 : Blo 916578 2610265 := bstep (se 2 (by rfl) ⟨978849, by rfl⟩ : syracuseStep 2610265 = 1957699) B1957699
theorem B3921155 : Blo 916578 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B3101975 : Blo 916578 3101975 := bstep (se 1 (by rfl) ⟨2326481, by rfl⟩ : syracuseStep 3101975 = 4652963) B4652963
theorem B3527981 : Blo 916578 3527981 := bstep (se 3 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 3527981 = 1322993) B1322993
theorem B6968753 : Blo 916578 6968753 := bstep (se 2 (by rfl) ⟨2613282, by rfl⟩ : syracuseStep 6968753 = 5226565) B5226565
theorem B2938457 : Blo 916578 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B3921497 : Blo 916578 3921497 := bstep (se 2 (by rfl) ⟨1470561, by rfl⟩ : syracuseStep 3921497 = 2941123) B2941123
theorem B3528409 : Blo 916578 3528409 := bstep (se 2 (by rfl) ⟨1323153, by rfl⟩ : syracuseStep 3528409 = 2646307) B2646307
theorem B3102515 : Blo 916578 3102515 := bstep (se 1 (by rfl) ⟨2326886, by rfl⟩ : syracuseStep 3102515 = 4653773) B4653773
theorem B6969239 : Blo 916578 6969239 := bstep (se 1 (by rfl) ⟨5226929, by rfl⟩ : syracuseStep 6969239 = 10453859) B10453859
theorem B2480051 : Blo 916578 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B3102785 : Blo 916578 3102785 := bstep (se 2 (by rfl) ⟨1163544, by rfl⟩ : syracuseStep 3102785 = 2327089) B2327089
theorem B4413761 : Blo 916578 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B1890635 : Blo 916578 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B5527939 : Blo 916578 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B3103325 : Blo 916578 3103325 := bstep (se 3 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 3103325 = 1163747) B1163747
theorem B3726125 : Blo 916578 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B2612189 : Blo 916578 2612189 := bstep (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) B979571
theorem B4185395 : Blo 916578 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B5954917 : Blo 916578 5954917 := bstep (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) B1116547
theorem B7462493 : Blo 916578 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B10477187 : Blo 916578 10477187 := bstep (se 1 (by rfl) ⟨7857890, by rfl⟩ : syracuseStep 10477187 = 15715781) B15715781
theorem B3104459 : Blo 916578 3104459 := bstep (se 1 (by rfl) ⟨2328344, by rfl⟩ : syracuseStep 3104459 = 4656689) B4656689
theorem B4644701 : Blo 916578 4644701 := bstep (se 3 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 4644701 = 1741763) B1741763
theorem B3104729 : Blo 916578 3104729 := bstep (se 2 (by rfl) ⟨1164273, by rfl⟩ : syracuseStep 3104729 = 2328547) B2328547
theorem B2940893 : Blo 916578 2940893 := bstep (se 3 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 2940893 = 1102835) B1102835
theorem B1859915 : Blo 916578 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B4252097 : Blo 916578 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B7168517 : Blo 916578 7168517 := bstep (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) B1344097
theorem B3105431 : Blo 916578 3105431 := bstep (se 1 (by rfl) ⟨2329073, by rfl⟩ : syracuseStep 3105431 = 4658147) B4658147
theorem B1958681 : Blo 916578 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B5235587 : Blo 916578 5235587 := bstep (se 1 (by rfl) ⟨3926690, by rfl⟩ : syracuseStep 5235587 = 7853381) B7853381
theorem B2155403 : Blo 916578 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B3924881 : Blo 916578 3924881 := bstep (se 2 (by rfl) ⟨1471830, by rfl⟩ : syracuseStep 3924881 = 2943661) B2943661
theorem B8479667 : Blo 916578 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B26240021 : Blo 916578 26240021 := bstep (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) B1230001
theorem B3105971 : Blo 916578 3105971 := bstep (se 1 (by rfl) ⟨2329478, by rfl⟩ : syracuseStep 3105971 = 4658957) B4658957
theorem B1959347 : Blo 916578 1959347 := bstep (se 1 (by rfl) ⟨1469510, by rfl⟩ : syracuseStep 1959347 = 2939021) B2939021
theorem B8381875 : Blo 916578 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B3106241 : Blo 916578 3106241 := bstep (se 2 (by rfl) ⟨1164840, by rfl⟩ : syracuseStep 3106241 = 2329681) B2329681
theorem B2483801 : Blo 916578 2483801 := bstep (se 2 (by rfl) ⟨931425, by rfl⟩ : syracuseStep 2483801 = 1862851) B1862851
theorem B3925597 : Blo 916578 3925597 := bstep (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) B1472099
theorem B1861399 : Blo 916578 1861399 := bstep (se 1 (by rfl) ⟨1396049, by rfl⟩ : syracuseStep 1861399 = 2792099) B2792099
theorem B15689537 : Blo 916578 15689537 := bstep (se 2 (by rfl) ⟨5883576, by rfl⟩ : syracuseStep 15689537 = 11767153) B11767153
theorem B2615105 : Blo 916578 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B1238873 : Blo 916578 1238873 := bstep (se 2 (by rfl) ⟨464577, by rfl⟩ : syracuseStep 1238873 = 929155) B929155
theorem B2615129 : Blo 916578 2615129 := bstep (se 2 (by rfl) ⟨980673, by rfl⟩ : syracuseStep 2615129 = 1961347) B1961347
theorem B4646807 : Blo 916578 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B1238987 : Blo 916578 1238987 := bstep (se 1 (by rfl) ⟨929240, by rfl⟩ : syracuseStep 1238987 = 1858481) B1858481
theorem B3106781 : Blo 916578 3106781 := bstep (se 3 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 3106781 = 1165043) B1165043
theorem B6383717 : Blo 916578 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B3631639 : Blo 916578 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B7858781 : Blo 916578 7858781 := bstep (se 3 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 7858781 = 2947043) B2947043
theorem B2321075 : Blo 916578 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B6613721 : Blo 916578 6613721 := bstep (se 2 (by rfl) ⟨2480145, by rfl⟩ : syracuseStep 6613721 = 4960291) B4960291
theorem B1960843 : Blo 916578 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B1305497 : Blo 916578 1305497 := bstep (se 2 (by rfl) ⟨489561, by rfl⟩ : syracuseStep 1305497 = 979123) B979123
theorem B2321369 : Blo 916578 2321369 := bstep (se 2 (by rfl) ⟨870513, by rfl⟩ : syracuseStep 2321369 = 1741027) B1741027
theorem B6286297 : Blo 916578 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B2616371 : Blo 916578 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B3402931 : Blo 916578 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B2518237 : Blo 916578 2518237 := bstep (se 3 (by rfl) ⟨472169, by rfl⟩ : syracuseStep 2518237 = 944339) B944339
theorem B7859531 : Blo 916578 7859531 := bstep (se 1 (by rfl) ⟨5894648, by rfl⟩ : syracuseStep 7859531 = 11789297) B11789297
theorem B1306135 : Blo 916578 1306135 := bstep (se 1 (by rfl) ⟨979601, by rfl⟩ : syracuseStep 1306135 = 1959203) B1959203
theorem B4419373 : Blo 916578 4419373 := bstep (se 3 (by rfl) ⟨828632, by rfl⟩ : syracuseStep 4419373 = 1657265) B1657265
theorem B17624897 : Blo 916578 17624897 := bstep (se 2 (by rfl) ⟨6609336, by rfl⟩ : syracuseStep 17624897 = 13218673) B13218673
theorem B2092915 : Blo 916578 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B2125835 : Blo 916578 2125835 := bstep (se 1 (by rfl) ⟨1594376, by rfl⟩ : syracuseStep 2125835 = 3188753) B3188753
theorem B3731507 : Blo 916578 3731507 := bstep (se 1 (by rfl) ⟨2798630, by rfl⟩ : syracuseStep 3731507 = 5597261) B5597261
theorem B1962073 : Blo 916578 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B13234357 : Blo 916578 13234357 := bstep (se 5 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 13234357 = 1240721) B1240721
theorem B14151941 : Blo 916578 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B1306955 : Blo 916578 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B979499 : Blo 916578 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B2323019 : Blo 916578 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B11760389 : Blo 916578 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B5894957 : Blo 916578 5894957 := bstep (se 3 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 5894957 = 2210609) B2210609
theorem B7861171 : Blo 916578 7861171 := bstep (se 1 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 7861171 = 11791757) B11791757
theorem B6976529 : Blo 916578 6976529 := bstep (se 2 (by rfl) ⟨2616198, by rfl⟩ : syracuseStep 6976529 = 5232397) B5232397
theorem B2094155 : Blo 916578 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B3929219 : Blo 916578 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B3306689 : Blo 916578 3306689 := bstep (se 2 (by rfl) ⟨1240008, by rfl⟩ : syracuseStep 3306689 = 2480017) B2480017
theorem B1307929 : Blo 916578 1307929 := bstep (se 2 (by rfl) ⟨490473, by rfl⟩ : syracuseStep 1307929 = 980947) B980947
theorem B11334977 : Blo 916578 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B4650371 : Blo 916578 4650371 := bstep (se 1 (by rfl) ⟨3487778, by rfl⟩ : syracuseStep 4650371 = 6975557) B6975557
theorem B2323991 : Blo 916578 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B1472087 : Blo 916578 1472087 := bstep (se 1 (by rfl) ⟨1104065, by rfl⟩ : syracuseStep 1472087 = 2208131) B2208131
theorem B980695 : Blo 916578 980695 := bstep (se 1 (by rfl) ⟨735521, by rfl⟩ : syracuseStep 980695 = 1471043) B1471043
theorem B2619229 : Blo 916578 2619229 := bstep (se 3 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 2619229 = 982211) B982211
theorem B1570699 : Blo 916578 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B2619287 : Blo 916578 2619287 := bstep (se 1 (by rfl) ⟨1964465, by rfl⟩ : syracuseStep 2619287 = 3928931) B3928931
theorem B5240963 : Blo 916578 5240963 := bstep (se 1 (by rfl) ⟨3930722, by rfl⟩ : syracuseStep 5240963 = 7861445) B7861445
theorem B2062475 : Blo 916578 2062475 := bstep (se 1 (by rfl) ⟨1546856, by rfl⟩ : syracuseStep 2062475 = 3093713) B3093713
theorem B1472651 : Blo 916578 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B11303063 : Blo 916578 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B2324659 : Blo 916578 2324659 := bstep (se 1 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 2324659 = 3486989) B3486989
theorem B22313141 : Blo 916578 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B2062529 : Blo 916578 2062529 := bstep (se 2 (by rfl) ⟨773448, by rfl⟩ : syracuseStep 2062529 = 1546897) B1546897
theorem B1472791 : Blo 916578 1472791 := bstep (se 1 (by rfl) ⟨1104593, by rfl⟩ : syracuseStep 1472791 = 2209187) B2209187
theorem B11794733 : Blo 916578 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B2324801 : Blo 916578 2324801 := bstep (se 2 (by rfl) ⟨871800, by rfl⟩ : syracuseStep 2324801 = 1743601) B1743601
theorem B1309079 : Blo 916578 1309079 := bstep (se 1 (by rfl) ⟨981809, by rfl⟩ : syracuseStep 1309079 = 1963619) B1963619
theorem B2062745 : Blo 916578 2062745 := bstep (se 2 (by rfl) ⟨773529, by rfl⟩ : syracuseStep 2062745 = 1547059) B1547059
theorem B2062835 : Blo 916578 2062835 := bstep (se 1 (by rfl) ⟨1547126, by rfl⟩ : syracuseStep 2062835 = 3094253) B3094253
theorem B981515 : Blo 916578 981515 := bstep (se 1 (by rfl) ⟨736136, by rfl⟩ : syracuseStep 981515 = 1472273) B1472273
theorem B2062871 : Blo 916578 2062871 := bstep (se 1 (by rfl) ⟨1547153, by rfl⟩ : syracuseStep 2062871 = 3094307) B3094307
theorem B5241419 : Blo 916578 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B1374923 : Blo 916578 1374923 := bstep (se 1 (by rfl) ⟨1031192, by rfl⟩ : syracuseStep 1374923 = 2062385) B2062385
theorem B2063051 : Blo 916578 2063051 := bstep (se 1 (by rfl) ⟨1547288, by rfl⟩ : syracuseStep 2063051 = 3094577) B3094577
theorem B1309387 : Blo 916578 1309387 := bstep (se 1 (by rfl) ⟨982040, by rfl⟩ : syracuseStep 1309387 = 1964081) B1964081
theorem B1374935 : Blo 916578 1374935 := bstep (se 1 (by rfl) ⟨1031201, by rfl⟩ : syracuseStep 1374935 = 2062403) B2062403
theorem B2063105 : Blo 916578 2063105 := bstep (se 2 (by rfl) ⟨773664, by rfl⟩ : syracuseStep 2063105 = 1547329) B1547329
theorem B1375001 : Blo 916578 1375001 := bstep (se 2 (by rfl) ⟨515625, by rfl⟩ : syracuseStep 1375001 = 1031251) B1031251
theorem B20380517 : Blo 916578 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B1375115 : Blo 916578 1375115 := bstep (se 1 (by rfl) ⟨1031336, by rfl⟩ : syracuseStep 1375115 = 2062673) B2062673
theorem B1178507 : Blo 916578 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B1375127 : Blo 916578 1375127 := bstep (se 1 (by rfl) ⟨1031345, by rfl⟩ : syracuseStep 1375127 = 2062691) B2062691
theorem B3931031 : Blo 916578 3931031 := bstep (se 1 (by rfl) ⟨2948273, by rfl⟩ : syracuseStep 3931031 = 5896547) B5896547
theorem B1375193 : Blo 916578 1375193 := bstep (se 2 (by rfl) ⟨515697, by rfl⟩ : syracuseStep 1375193 = 1031395) B1031395
theorem B2063321 : Blo 916578 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B2063411 : Blo 916578 2063411 := bstep (se 1 (by rfl) ⟨1547558, by rfl⟩ : syracuseStep 2063411 = 3095117) B3095117
theorem B1375307 : Blo 916578 1375307 := bstep (se 1 (by rfl) ⟨1031480, by rfl⟩ : syracuseStep 1375307 = 2062961) B2062961
theorem B1473611 : Blo 916578 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B1375319 : Blo 916578 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B2063447 : Blo 916578 2063447 := bstep (se 1 (by rfl) ⟨1547585, by rfl⟩ : syracuseStep 2063447 = 3095171) B3095171
theorem B2620505 : Blo 916578 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B916587 : Blo 916578 916587 := bstep (se 1 (by rfl) ⟨687440, by rfl⟩ : syracuseStep 916587 = 1374881) B1374881
theorem B916599 : Blo 916578 916599 := bstep (se 1 (by rfl) ⟨687449, by rfl⟩ : syracuseStep 916599 = 1374899) B1374899
theorem B916619 : Blo 916578 916619 := bstep (se 1 (by rfl) ⟨687464, by rfl⟩ : syracuseStep 916619 = 1374929) B1374929
theorem B916631 : Blo 916578 916631 := bstep (se 1 (by rfl) ⟨687473, by rfl⟩ : syracuseStep 916631 = 1374947) B1374947
theorem B1375385 : Blo 916578 1375385 := bstep (se 2 (by rfl) ⟨515769, by rfl⟩ : syracuseStep 1375385 = 1031539) B1031539
theorem B1473689 : Blo 916578 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B916651 : Blo 916578 916651 := bstep (se 1 (by rfl) ⟨687488, by rfl⟩ : syracuseStep 916651 = 1374977) B1374977
theorem B916663 : Blo 916578 916663 := bstep (se 1 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 916663 = 1374995) B1374995
theorem B916683 : Blo 916578 916683 := bstep (se 1 (by rfl) ⟨687512, by rfl⟩ : syracuseStep 916683 = 1375025) B1375025
theorem B1965259 : Blo 916578 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B2620619 : Blo 916578 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B916695 : Blo 916578 916695 := bstep (se 1 (by rfl) ⟨687521, by rfl⟩ : syracuseStep 916695 = 1375043) B1375043
theorem B916715 : Blo 916578 916715 := bstep (se 1 (by rfl) ⟨687536, by rfl⟩ : syracuseStep 916715 = 1375073) B1375073
theorem B916727 : Blo 916578 916727 := bstep (se 1 (by rfl) ⟨687545, by rfl⟩ : syracuseStep 916727 = 1375091) B1375091
theorem B916747 : Blo 916578 916747 := bstep (se 1 (by rfl) ⟨687560, by rfl⟩ : syracuseStep 916747 = 1375121) B1375121
theorem B1375499 : Blo 916578 1375499 := bstep (se 1 (by rfl) ⟨1031624, by rfl⟩ : syracuseStep 1375499 = 2063249) B2063249
theorem B2063627 : Blo 916578 2063627 := bstep (se 1 (by rfl) ⟨1547720, by rfl⟩ : syracuseStep 2063627 = 3095441) B3095441
theorem B916759 : Blo 916578 916759 := bstep (se 1 (by rfl) ⟨687569, by rfl⟩ : syracuseStep 916759 = 1375139) B1375139
theorem B1375511 : Blo 916578 1375511 := bstep (se 1 (by rfl) ⟨1031633, by rfl⟩ : syracuseStep 1375511 = 2063267) B2063267
theorem B916779 : Blo 916578 916779 := bstep (se 1 (by rfl) ⟨687584, by rfl⟩ : syracuseStep 916779 = 1375169) B1375169
theorem B916791 : Blo 916578 916791 := bstep (se 1 (by rfl) ⟨687593, by rfl⟩ : syracuseStep 916791 = 1375187) B1375187
theorem B2063681 : Blo 916578 2063681 := bstep (se 2 (by rfl) ⟨773880, by rfl⟩ : syracuseStep 2063681 = 1547761) B1547761
theorem B916811 : Blo 916578 916811 := bstep (se 1 (by rfl) ⟨687608, by rfl⟩ : syracuseStep 916811 = 1375217) B1375217
theorem B916823 : Blo 916578 916823 := bstep (se 1 (by rfl) ⟨687617, by rfl⟩ : syracuseStep 916823 = 1375235) B1375235
theorem B1375577 : Blo 916578 1375577 := bstep (se 2 (by rfl) ⟨515841, by rfl⟩ : syracuseStep 1375577 = 1031683) B1031683
theorem B916843 : Blo 916578 916843 := bstep (se 1 (by rfl) ⟨687632, by rfl⟩ : syracuseStep 916843 = 1375265) B1375265
theorem B916855 : Blo 916578 916855 := bstep (se 1 (by rfl) ⟨687641, by rfl⟩ : syracuseStep 916855 = 1375283) B1375283
theorem B916875 : Blo 916578 916875 := bstep (se 1 (by rfl) ⟨687656, by rfl⟩ : syracuseStep 916875 = 1375313) B1375313
theorem B916887 : Blo 916578 916887 := bstep (se 1 (by rfl) ⟨687665, by rfl⟩ : syracuseStep 916887 = 1375331) B1375331
theorem B916907 : Blo 916578 916907 := bstep (se 1 (by rfl) ⟨687680, by rfl⟩ : syracuseStep 916907 = 1375361) B1375361
theorem B10452401 : Blo 916578 10452401 := bstep (se 2 (by rfl) ⟨3919650, by rfl⟩ : syracuseStep 10452401 = 7839301) B7839301
theorem B916919 : Blo 916578 916919 := bstep (se 1 (by rfl) ⟨687689, by rfl⟩ : syracuseStep 916919 = 1375379) B1375379
theorem B1047991 : Blo 916578 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B916939 : Blo 916578 916939 := bstep (se 1 (by rfl) ⟨687704, by rfl⟩ : syracuseStep 916939 = 1375409) B1375409
theorem B1375691 : Blo 916578 1375691 := bstep (se 1 (by rfl) ⟨1031768, by rfl⟩ : syracuseStep 1375691 = 2063537) B2063537
theorem B2948555 : Blo 916578 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B916951 : Blo 916578 916951 := bstep (se 1 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 916951 = 1375427) B1375427
theorem B1375703 : Blo 916578 1375703 := bstep (se 1 (by rfl) ⟨1031777, by rfl⟩ : syracuseStep 1375703 = 2063555) B2063555
theorem B916971 : Blo 916578 916971 := bstep (se 1 (by rfl) ⟨687728, by rfl⟩ : syracuseStep 916971 = 1375457) B1375457
theorem B916983 : Blo 916578 916983 := bstep (se 1 (by rfl) ⟨687737, by rfl⟩ : syracuseStep 916983 = 1375475) B1375475
theorem B917003 : Blo 916578 917003 := bstep (se 1 (by rfl) ⟨687752, by rfl⟩ : syracuseStep 917003 = 1375505) B1375505
theorem B917015 : Blo 916578 917015 := bstep (se 1 (by rfl) ⟨687761, by rfl⟩ : syracuseStep 917015 = 1375523) B1375523
theorem B1375769 : Blo 916578 1375769 := bstep (se 2 (by rfl) ⟨515913, by rfl⟩ : syracuseStep 1375769 = 1031827) B1031827
theorem B2063897 : Blo 916578 2063897 := bstep (se 2 (by rfl) ⟨773961, by rfl⟩ : syracuseStep 2063897 = 1547923) B1547923
theorem B917035 : Blo 916578 917035 := bstep (se 1 (by rfl) ⟨687776, by rfl⟩ : syracuseStep 917035 = 1375553) B1375553
theorem B2326067 : Blo 916578 2326067 := bstep (se 1 (by rfl) ⟨1744550, by rfl⟩ : syracuseStep 2326067 = 3489101) B3489101
theorem B917047 : Blo 916578 917047 := bstep (se 1 (by rfl) ⟨687785, by rfl⟩ : syracuseStep 917047 = 1375571) B1375571
theorem B917067 : Blo 916578 917067 := bstep (se 1 (by rfl) ⟨687800, by rfl⟩ : syracuseStep 917067 = 1375601) B1375601
theorem B917079 : Blo 916578 917079 := bstep (se 1 (by rfl) ⟨687809, by rfl⟩ : syracuseStep 917079 = 1375619) B1375619
theorem B917099 : Blo 916578 917099 := bstep (se 1 (by rfl) ⟨687824, by rfl⟩ : syracuseStep 917099 = 1375649) B1375649
theorem B2063987 : Blo 916578 2063987 := bstep (se 1 (by rfl) ⟨1547990, by rfl⟩ : syracuseStep 2063987 = 3095981) B3095981
theorem B917111 : Blo 916578 917111 := bstep (se 1 (by rfl) ⟨687833, by rfl⟩ : syracuseStep 917111 = 1375667) B1375667
theorem B917131 : Blo 916578 917131 := bstep (se 1 (by rfl) ⟨687848, by rfl⟩ : syracuseStep 917131 = 1375697) B1375697
theorem B1375883 : Blo 916578 1375883 := bstep (se 1 (by rfl) ⟨1031912, by rfl⟩ : syracuseStep 1375883 = 2063825) B2063825
theorem B917143 : Blo 916578 917143 := bstep (se 1 (by rfl) ⟨687857, by rfl⟩ : syracuseStep 917143 = 1375715) B1375715
theorem B1375895 : Blo 916578 1375895 := bstep (se 1 (by rfl) ⟨1031921, by rfl⟩ : syracuseStep 1375895 = 2063843) B2063843
theorem B2064023 : Blo 916578 2064023 := bstep (se 1 (by rfl) ⟨1548017, by rfl⟩ : syracuseStep 2064023 = 3096035) B3096035
theorem B1965721 : Blo 916578 1965721 := bstep (se 2 (by rfl) ⟨737145, by rfl⟩ : syracuseStep 1965721 = 1474291) B1474291
theorem B917163 : Blo 916578 917163 := bstep (se 1 (by rfl) ⟨687872, by rfl⟩ : syracuseStep 917163 = 1375745) B1375745
theorem B917175 : Blo 916578 917175 := bstep (se 1 (by rfl) ⟨687881, by rfl⟩ : syracuseStep 917175 = 1375763) B1375763
theorem B917195 : Blo 916578 917195 := bstep (se 1 (by rfl) ⟨687896, by rfl⟩ : syracuseStep 917195 = 1375793) B1375793
theorem B917207 : Blo 916578 917207 := bstep (se 1 (by rfl) ⟨687905, by rfl⟩ : syracuseStep 917207 = 1375811) B1375811
theorem B1310423 : Blo 916578 1310423 := bstep (se 1 (by rfl) ⟨982817, by rfl⟩ : syracuseStep 1310423 = 1965635) B1965635
theorem B1375961 : Blo 916578 1375961 := bstep (se 2 (by rfl) ⟨515985, by rfl⟩ : syracuseStep 1375961 = 1031971) B1031971
theorem B917227 : Blo 916578 917227 := bstep (se 1 (by rfl) ⟨687920, by rfl⟩ : syracuseStep 917227 = 1375841) B1375841
theorem B917239 : Blo 916578 917239 := bstep (se 1 (by rfl) ⟨687929, by rfl⟩ : syracuseStep 917239 = 1375859) B1375859
theorem B917259 : Blo 916578 917259 := bstep (se 1 (by rfl) ⟨687944, by rfl⟩ : syracuseStep 917259 = 1375889) B1375889
theorem B917271 : Blo 916578 917271 := bstep (se 1 (by rfl) ⟨687953, by rfl⟩ : syracuseStep 917271 = 1375907) B1375907
theorem B917291 : Blo 916578 917291 := bstep (se 1 (by rfl) ⟨687968, by rfl⟩ : syracuseStep 917291 = 1375937) B1375937
theorem B917303 : Blo 916578 917303 := bstep (se 1 (by rfl) ⟨687977, by rfl⟩ : syracuseStep 917303 = 1375955) B1375955
theorem B917323 : Blo 916578 917323 := bstep (se 1 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 917323 = 1375985) B1375985
theorem B1376075 : Blo 916578 1376075 := bstep (se 1 (by rfl) ⟨1032056, by rfl⟩ : syracuseStep 1376075 = 2064113) B2064113
theorem B2064203 : Blo 916578 2064203 := bstep (se 1 (by rfl) ⟨1548152, by rfl⟩ : syracuseStep 2064203 = 3096305) B3096305
theorem B917335 : Blo 916578 917335 := bstep (se 1 (by rfl) ⟨688001, by rfl⟩ : syracuseStep 917335 = 1376003) B1376003
theorem B1376087 : Blo 916578 1376087 := bstep (se 1 (by rfl) ⟨1032065, by rfl⟩ : syracuseStep 1376087 = 2064131) B2064131
theorem B1572697 : Blo 916578 1572697 := bstep (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) B1179523
theorem B917355 : Blo 916578 917355 := bstep (se 1 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 917355 = 1376033) B1376033
theorem B917367 : Blo 916578 917367 := bstep (se 1 (by rfl) ⟨688025, by rfl⟩ : syracuseStep 917367 = 1376051) B1376051
theorem B982903 : Blo 916578 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B2064257 : Blo 916578 2064257 := bstep (se 2 (by rfl) ⟨774096, by rfl⟩ : syracuseStep 2064257 = 1548193) B1548193
theorem B917387 : Blo 916578 917387 := bstep (se 1 (by rfl) ⟨688040, by rfl⟩ : syracuseStep 917387 = 1376081) B1376081
theorem B917399 : Blo 916578 917399 := bstep (se 1 (by rfl) ⟨688049, by rfl⟩ : syracuseStep 917399 = 1376099) B1376099
theorem B1376153 : Blo 916578 1376153 := bstep (se 2 (by rfl) ⟨516057, by rfl⟩ : syracuseStep 1376153 = 1032115) B1032115
theorem B1310617 : Blo 916578 1310617 := bstep (se 2 (by rfl) ⟨491481, by rfl⟩ : syracuseStep 1310617 = 982963) B982963
theorem B917419 : Blo 916578 917419 := bstep (se 1 (by rfl) ⟨688064, by rfl⟩ : syracuseStep 917419 = 1376129) B1376129
theorem B917431 : Blo 916578 917431 := bstep (se 1 (by rfl) ⟨688073, by rfl⟩ : syracuseStep 917431 = 1376147) B1376147
theorem B917451 : Blo 916578 917451 := bstep (se 1 (by rfl) ⟨688088, by rfl⟩ : syracuseStep 917451 = 1376177) B1376177
theorem B917463 : Blo 916578 917463 := bstep (se 1 (by rfl) ⟨688097, by rfl⟩ : syracuseStep 917463 = 1376195) B1376195
theorem B917483 : Blo 916578 917483 := bstep (se 1 (by rfl) ⟨688112, by rfl⟩ : syracuseStep 917483 = 1376225) B1376225
theorem B917495 : Blo 916578 917495 := bstep (se 1 (by rfl) ⟨688121, by rfl⟩ : syracuseStep 917495 = 1376243) B1376243
theorem B917511 : Blo 916578 917511 := bstep (se 1 (by rfl) ⟨688133, by rfl⟩ : syracuseStep 917511 = 1376267) B1376267
theorem B917519 : Blo 916578 917519 := bstep (se 1 (by rfl) ⟨688139, by rfl⟩ : syracuseStep 917519 = 1376279) B1376279
theorem B1376315 : Blo 916578 1376315 := bstep (se 1 (by rfl) ⟨1032236, by rfl⟩ : syracuseStep 1376315 = 2064473) B2064473
theorem B917563 : Blo 916578 917563 := bstep (se 1 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 917563 = 1376345) B1376345
theorem B1376375 : Blo 916578 1376375 := bstep (se 1 (by rfl) ⟨1032281, by rfl⟩ : syracuseStep 1376375 = 2064563) B2064563
theorem B917639 : Blo 916578 917639 := bstep (se 1 (by rfl) ⟨688229, by rfl⟩ : syracuseStep 917639 = 1376459) B1376459
theorem B1376399 : Blo 916578 1376399 := bstep (se 1 (by rfl) ⟨1032299, by rfl⟩ : syracuseStep 1376399 = 2064599) B2064599
theorem B917647 : Blo 916578 917647 := bstep (se 1 (by rfl) ⟨688235, by rfl⟩ : syracuseStep 917647 = 1376471) B1376471
theorem B1376441 : Blo 916578 1376441 := bstep (se 2 (by rfl) ⟨516165, by rfl⟩ : syracuseStep 1376441 = 1032331) B1032331
theorem B917691 : Blo 916578 917691 := bstep (se 1 (by rfl) ⟨688268, by rfl⟩ : syracuseStep 917691 = 1376537) B1376537
theorem B1376519 : Blo 916578 1376519 := bstep (se 1 (by rfl) ⟨1032389, by rfl⟩ : syracuseStep 1376519 = 2064779) B2064779
theorem B917767 : Blo 916578 917767 := bstep (se 1 (by rfl) ⟨688325, by rfl⟩ : syracuseStep 917767 = 1376651) B1376651
theorem B917775 : Blo 916578 917775 := bstep (se 1 (by rfl) ⟨688331, by rfl⟩ : syracuseStep 917775 = 1376663) B1376663
theorem B1376555 : Blo 916578 1376555 := bstep (se 1 (by rfl) ⟨1032416, by rfl⟩ : syracuseStep 1376555 = 2064833) B2064833
theorem B917819 : Blo 916578 917819 := bstep (se 1 (by rfl) ⟨688364, by rfl⟩ : syracuseStep 917819 = 1376729) B1376729
theorem B1376585 : Blo 916578 1376585 := bstep (se 2 (by rfl) ⟨516219, by rfl⟩ : syracuseStep 1376585 = 1032439) B1032439
theorem B917895 : Blo 916578 917895 := bstep (se 1 (by rfl) ⟨688421, by rfl⟩ : syracuseStep 917895 = 1376843) B1376843
theorem B917903 : Blo 916578 917903 := bstep (se 1 (by rfl) ⟨688427, by rfl⟩ : syracuseStep 917903 = 1376855) B1376855
theorem B1376699 : Blo 916578 1376699 := bstep (se 1 (by rfl) ⟨1032524, by rfl⟩ : syracuseStep 1376699 = 2065049) B2065049
theorem B917947 : Blo 916578 917947 := bstep (se 1 (by rfl) ⟨688460, by rfl⟩ : syracuseStep 917947 = 1376921) B1376921
theorem B1376759 : Blo 916578 1376759 := bstep (se 1 (by rfl) ⟨1032569, by rfl⟩ : syracuseStep 1376759 = 2065139) B2065139
theorem B918023 : Blo 916578 918023 := bstep (se 1 (by rfl) ⟨688517, by rfl⟩ : syracuseStep 918023 = 1377035) B1377035
theorem B3310091 : Blo 916578 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B1376783 : Blo 916578 1376783 := bstep (se 1 (by rfl) ⟨1032587, by rfl⟩ : syracuseStep 1376783 = 2065175) B2065175
theorem B918031 : Blo 916578 918031 := bstep (se 1 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 918031 = 1377047) B1377047
theorem B4653611 : Blo 916578 4653611 := bstep (se 1 (by rfl) ⟨3490208, by rfl⟩ : syracuseStep 4653611 = 6980417) B6980417
theorem B1376825 : Blo 916578 1376825 := bstep (se 2 (by rfl) ⟨516309, by rfl⟩ : syracuseStep 1376825 = 1032619) B1032619
theorem B918075 : Blo 916578 918075 := bstep (se 1 (by rfl) ⟨688556, by rfl⟩ : syracuseStep 918075 = 1377113) B1377113
theorem B2065031 : Blo 916578 2065031 := bstep (se 1 (by rfl) ⟨1548773, by rfl⟩ : syracuseStep 2065031 = 3097547) B3097547
theorem B1376903 : Blo 916578 1376903 := bstep (se 1 (by rfl) ⟨1032677, by rfl⟩ : syracuseStep 1376903 = 2065355) B2065355
theorem B918151 : Blo 916578 918151 := bstep (se 1 (by rfl) ⟨688613, by rfl⟩ : syracuseStep 918151 = 1377227) B1377227
theorem B918159 : Blo 916578 918159 := bstep (se 1 (by rfl) ⟨688619, by rfl⟩ : syracuseStep 918159 = 1377239) B1377239
theorem B1376939 : Blo 916578 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B918203 : Blo 916578 918203 := bstep (se 1 (by rfl) ⟨688652, by rfl⟩ : syracuseStep 918203 = 1377305) B1377305
theorem B1376969 : Blo 916578 1376969 := bstep (se 2 (by rfl) ⟨516363, by rfl⟩ : syracuseStep 1376969 = 1032727) B1032727
theorem B218170097 : Blo 916578 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B918279 : Blo 916578 918279 := bstep (se 1 (by rfl) ⟨688709, by rfl⟩ : syracuseStep 918279 = 1377419) B1377419
theorem B918287 : Blo 916578 918287 := bstep (se 1 (by rfl) ⟨688715, by rfl⟩ : syracuseStep 918287 = 1377431) B1377431
theorem B2065211 : Blo 916578 2065211 := bstep (se 1 (by rfl) ⟨1548908, by rfl⟩ : syracuseStep 2065211 = 3097817) B3097817
theorem B1377083 : Blo 916578 1377083 := bstep (se 1 (by rfl) ⟨1032812, by rfl⟩ : syracuseStep 1377083 = 2065625) B2065625
theorem B918331 : Blo 916578 918331 := bstep (se 1 (by rfl) ⟨688748, by rfl⟩ : syracuseStep 918331 = 1377497) B1377497
theorem B1377143 : Blo 916578 1377143 := bstep (se 1 (by rfl) ⟨1032857, by rfl⟩ : syracuseStep 1377143 = 2065715) B2065715
theorem B918407 : Blo 916578 918407 := bstep (se 1 (by rfl) ⟨688805, by rfl⟩ : syracuseStep 918407 = 1377611) B1377611
theorem B1377167 : Blo 916578 1377167 := bstep (se 1 (by rfl) ⟨1032875, by rfl⟩ : syracuseStep 1377167 = 2065751) B2065751
theorem B918415 : Blo 916578 918415 := bstep (se 1 (by rfl) ⟨688811, by rfl⟩ : syracuseStep 918415 = 1377623) B1377623
theorem B2065337 : Blo 916578 2065337 := bstep (se 2 (by rfl) ⟨774501, by rfl⟩ : syracuseStep 2065337 = 1549003) B1549003
theorem B1377209 : Blo 916578 1377209 := bstep (se 2 (by rfl) ⟨516453, by rfl⟩ : syracuseStep 1377209 = 1032907) B1032907
theorem B918459 : Blo 916578 918459 := bstep (se 1 (by rfl) ⟨688844, by rfl⟩ : syracuseStep 918459 = 1377689) B1377689
theorem B1377287 : Blo 916578 1377287 := bstep (se 1 (by rfl) ⟨1032965, by rfl⟩ : syracuseStep 1377287 = 2065931) B2065931
theorem B918535 : Blo 916578 918535 := bstep (se 1 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 918535 = 1377803) B1377803
theorem B918543 : Blo 916578 918543 := bstep (se 1 (by rfl) ⟨688907, by rfl⟩ : syracuseStep 918543 = 1377815) B1377815
theorem B1377323 : Blo 916578 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B918587 : Blo 916578 918587 := bstep (se 1 (by rfl) ⟨688940, by rfl⟩ : syracuseStep 918587 = 1377881) B1377881
theorem B1377353 : Blo 916578 1377353 := bstep (se 2 (by rfl) ⟨516507, by rfl⟩ : syracuseStep 1377353 = 1033015) B1033015
theorem B918663 : Blo 916578 918663 := bstep (se 1 (by rfl) ⟨688997, by rfl⟩ : syracuseStep 918663 = 1377995) B1377995
theorem B2327687 : Blo 916578 2327687 := bstep (se 1 (by rfl) ⟨1745765, by rfl⟩ : syracuseStep 2327687 = 3491531) B3491531
theorem B918671 : Blo 916578 918671 := bstep (se 1 (by rfl) ⟨689003, by rfl⟩ : syracuseStep 918671 = 1378007) B1378007
theorem B2327737 : Blo 916578 2327737 := bstep (se 2 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 2327737 = 1745803) B1745803
theorem B1377467 : Blo 916578 1377467 := bstep (se 1 (by rfl) ⟨1033100, by rfl⟩ : syracuseStep 1377467 = 2066201) B2066201
theorem B918715 : Blo 916578 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B1377527 : Blo 916578 1377527 := bstep (se 1 (by rfl) ⟨1033145, by rfl⟩ : syracuseStep 1377527 = 2066291) B2066291
theorem B1180919 : Blo 916578 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B918791 : Blo 916578 918791 := bstep (se 1 (by rfl) ⟨689093, by rfl⟩ : syracuseStep 918791 = 1378187) B1378187
theorem B2065679 : Blo 916578 2065679 := bstep (se 1 (by rfl) ⟨1549259, by rfl⟩ : syracuseStep 2065679 = 3098519) B3098519
theorem B1377551 : Blo 916578 1377551 := bstep (se 1 (by rfl) ⟨1033163, by rfl⟩ : syracuseStep 1377551 = 2066327) B2066327
theorem B918799 : Blo 916578 918799 := bstep (se 1 (by rfl) ⟨689099, by rfl⟩ : syracuseStep 918799 = 1378199) B1378199
theorem B2065697 : Blo 916578 2065697 := bstep (se 2 (by rfl) ⟨774636, by rfl⟩ : syracuseStep 2065697 = 1549273) B1549273
theorem B1377593 : Blo 916578 1377593 := bstep (se 2 (by rfl) ⟨516597, by rfl⟩ : syracuseStep 1377593 = 1033195) B1033195
theorem B918843 : Blo 916578 918843 := bstep (se 1 (by rfl) ⟨689132, by rfl⟩ : syracuseStep 918843 = 1378265) B1378265
theorem B1377671 : Blo 916578 1377671 := bstep (se 1 (by rfl) ⟨1033253, by rfl⟩ : syracuseStep 1377671 = 2066507) B2066507
theorem B918919 : Blo 916578 918919 := bstep (se 1 (by rfl) ⟨689189, by rfl⟩ : syracuseStep 918919 = 1378379) B1378379
theorem B918927 : Blo 916578 918927 := bstep (se 1 (by rfl) ⟨689195, by rfl⟩ : syracuseStep 918927 = 1378391) B1378391
theorem B1377707 : Blo 916578 1377707 := bstep (se 1 (by rfl) ⟨1033280, by rfl⟩ : syracuseStep 1377707 = 2066561) B2066561
theorem B918971 : Blo 916578 918971 := bstep (se 1 (by rfl) ⟨689228, by rfl⟩ : syracuseStep 918971 = 1378457) B1378457
theorem B1377737 : Blo 916578 1377737 := bstep (se 2 (by rfl) ⟨516651, by rfl⟩ : syracuseStep 1377737 = 1033303) B1033303
theorem B919047 : Blo 916578 919047 := bstep (se 1 (by rfl) ⟨689285, by rfl⟩ : syracuseStep 919047 = 1378571) B1378571
theorem B919055 : Blo 916578 919055 := bstep (se 1 (by rfl) ⟨689291, by rfl⟩ : syracuseStep 919055 = 1378583) B1378583
theorem B1377851 : Blo 916578 1377851 := bstep (se 1 (by rfl) ⟨1033388, by rfl⟩ : syracuseStep 1377851 = 2066777) B2066777
theorem B919099 : Blo 916578 919099 := bstep (se 1 (by rfl) ⟨689324, by rfl⟩ : syracuseStep 919099 = 1378649) B1378649
theorem B2066039 : Blo 916578 2066039 := bstep (se 1 (by rfl) ⟨1549529, by rfl⟩ : syracuseStep 2066039 = 3099059) B3099059
theorem B1377911 : Blo 916578 1377911 := bstep (se 1 (by rfl) ⟨1033433, by rfl⟩ : syracuseStep 1377911 = 2066867) B2066867
theorem B919175 : Blo 916578 919175 := bstep (se 1 (by rfl) ⟨689381, by rfl⟩ : syracuseStep 919175 = 1378763) B1378763
theorem B1377935 : Blo 916578 1377935 := bstep (se 1 (by rfl) ⟨1033451, by rfl⟩ : syracuseStep 1377935 = 2066903) B2066903
theorem B919183 : Blo 916578 919183 := bstep (se 1 (by rfl) ⟨689387, by rfl⟩ : syracuseStep 919183 = 1378775) B1378775
theorem B1377977 : Blo 916578 1377977 := bstep (se 2 (by rfl) ⟨516741, by rfl⟩ : syracuseStep 1377977 = 1033483) B1033483
theorem B919227 : Blo 916578 919227 := bstep (se 1 (by rfl) ⟨689420, by rfl⟩ : syracuseStep 919227 = 1378841) B1378841
theorem B2361089 : Blo 916578 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B1378055 : Blo 916578 1378055 := bstep (se 1 (by rfl) ⟨1033541, by rfl⟩ : syracuseStep 1378055 = 2067083) B2067083
theorem B919303 : Blo 916578 919303 := bstep (se 1 (by rfl) ⟨689477, by rfl⟩ : syracuseStep 919303 = 1378955) B1378955
theorem B919311 : Blo 916578 919311 := bstep (se 1 (by rfl) ⟨689483, by rfl⟩ : syracuseStep 919311 = 1378967) B1378967
theorem B2328335 : Blo 916578 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B2066219 : Blo 916578 2066219 := bstep (se 1 (by rfl) ⟨1549664, by rfl⟩ : syracuseStep 2066219 = 3099329) B3099329
theorem B1378091 : Blo 916578 1378091 := bstep (se 1 (by rfl) ⟨1033568, by rfl⟩ : syracuseStep 1378091 = 2067137) B2067137
theorem B919355 : Blo 916578 919355 := bstep (se 1 (by rfl) ⟨689516, by rfl⟩ : syracuseStep 919355 = 1379033) B1379033
theorem B4654907 : Blo 916578 4654907 := bstep (se 1 (by rfl) ⟨3491180, by rfl⟩ : syracuseStep 4654907 = 6982361) B6982361
theorem B1378121 : Blo 916578 1378121 := bstep (se 2 (by rfl) ⟨516795, by rfl⟩ : syracuseStep 1378121 = 1033591) B1033591
theorem B919431 : Blo 916578 919431 := bstep (se 1 (by rfl) ⟨689573, by rfl⟩ : syracuseStep 919431 = 1379147) B1379147
theorem B919439 : Blo 916578 919439 := bstep (se 1 (by rfl) ⟨689579, by rfl⟩ : syracuseStep 919439 = 1379159) B1379159
theorem B11175833 : Blo 916578 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B1378235 : Blo 916578 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B919483 : Blo 916578 919483 := bstep (se 1 (by rfl) ⟨689612, by rfl⟩ : syracuseStep 919483 = 1379225) B1379225
theorem B4655069 : Blo 916578 4655069 := bstep (se 3 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 4655069 = 1745651) B1745651
theorem B1378295 : Blo 916578 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B919559 : Blo 916578 919559 := bstep (se 1 (by rfl) ⟨689669, by rfl⟩ : syracuseStep 919559 = 1379339) B1379339
theorem B1378319 : Blo 916578 1378319 := bstep (se 1 (by rfl) ⟨1033739, by rfl⟩ : syracuseStep 1378319 = 2067479) B2067479
theorem B919567 : Blo 916578 919567 := bstep (se 1 (by rfl) ⟨689675, by rfl⟩ : syracuseStep 919567 = 1379351) B1379351
theorem B7440407 : Blo 916578 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B1378361 : Blo 916578 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B919611 : Blo 916578 919611 := bstep (se 1 (by rfl) ⟨689708, by rfl⟩ : syracuseStep 919611 = 1379417) B1379417
theorem B12585077 : Blo 916578 12585077 := bstep (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) B1179851
theorem B8390789 : Blo 916578 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B1378439 : Blo 916578 1378439 := bstep (se 1 (by rfl) ⟨1033829, by rfl⟩ : syracuseStep 1378439 = 2067659) B2067659
theorem B919687 : Blo 916578 919687 := bstep (se 1 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 919687 = 1379531) B1379531
theorem B919695 : Blo 916578 919695 := bstep (se 1 (by rfl) ⟨689771, by rfl⟩ : syracuseStep 919695 = 1379543) B1379543
theorem B2066579 : Blo 916578 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B1378475 : Blo 916578 1378475 := bstep (se 1 (by rfl) ⟨1033856, by rfl⟩ : syracuseStep 1378475 = 2067713) B2067713
theorem B919739 : Blo 916578 919739 := bstep (se 1 (by rfl) ⟨689804, by rfl⟩ : syracuseStep 919739 = 1379609) B1379609
theorem B2066633 : Blo 916578 2066633 := bstep (se 2 (by rfl) ⟨774987, by rfl⟩ : syracuseStep 2066633 = 1549975) B1549975
theorem B1378505 : Blo 916578 1378505 := bstep (se 2 (by rfl) ⟨516939, by rfl⟩ : syracuseStep 1378505 = 1033879) B1033879
theorem B919815 : Blo 916578 919815 := bstep (se 1 (by rfl) ⟨689861, by rfl⟩ : syracuseStep 919815 = 1379723) B1379723
theorem B919823 : Blo 916578 919823 := bstep (se 1 (by rfl) ⟨689867, by rfl⟩ : syracuseStep 919823 = 1379735) B1379735
theorem B4655393 : Blo 916578 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B1378619 : Blo 916578 1378619 := bstep (se 1 (by rfl) ⟨1033964, by rfl⟩ : syracuseStep 1378619 = 2067929) B2067929
theorem B919867 : Blo 916578 919867 := bstep (se 1 (by rfl) ⟨689900, by rfl⟩ : syracuseStep 919867 = 1379801) B1379801
theorem B1378679 : Blo 916578 1378679 := bstep (se 1 (by rfl) ⟨1034009, by rfl⟩ : syracuseStep 1378679 = 2068019) B2068019
theorem B919943 : Blo 916578 919943 := bstep (se 1 (by rfl) ⟨689957, by rfl⟩ : syracuseStep 919943 = 1379915) B1379915
theorem B1378703 : Blo 916578 1378703 := bstep (se 1 (by rfl) ⟨1034027, by rfl⟩ : syracuseStep 1378703 = 2068055) B2068055
theorem B919951 : Blo 916578 919951 := bstep (se 1 (by rfl) ⟨689963, by rfl⟩ : syracuseStep 919951 = 1379927) B1379927
theorem B1378745 : Blo 916578 1378745 := bstep (se 2 (by rfl) ⟨517029, by rfl⟩ : syracuseStep 1378745 = 1034059) B1034059
theorem B919995 : Blo 916578 919995 := bstep (se 1 (by rfl) ⟨689996, by rfl⟩ : syracuseStep 919995 = 1379993) B1379993
theorem B2329033 : Blo 916578 2329033 := bstep (se 2 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 2329033 = 1746775) B1746775
theorem B13240817 : Blo 916578 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B1378823 : Blo 916578 1378823 := bstep (se 1 (by rfl) ⟨1034117, by rfl⟩ : syracuseStep 1378823 = 2068235) B2068235
theorem B920071 : Blo 916578 920071 := bstep (se 1 (by rfl) ⟨690053, by rfl⟩ : syracuseStep 920071 = 1380107) B1380107
theorem B920079 : Blo 916578 920079 := bstep (se 1 (by rfl) ⟨690059, by rfl⟩ : syracuseStep 920079 = 1380119) B1380119
theorem B1378859 : Blo 916578 1378859 := bstep (se 1 (by rfl) ⟨1034144, by rfl⟩ : syracuseStep 1378859 = 2068289) B2068289
theorem B920123 : Blo 916578 920123 := bstep (se 1 (by rfl) ⟨690092, by rfl⟩ : syracuseStep 920123 = 1380185) B1380185
theorem B1378889 : Blo 916578 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B2329175 : Blo 916578 2329175 := bstep (se 1 (by rfl) ⟨1746881, by rfl⟩ : syracuseStep 2329175 = 3493763) B3493763
theorem B920199 : Blo 916578 920199 := bstep (se 1 (by rfl) ⟨690149, by rfl⟩ : syracuseStep 920199 = 1380299) B1380299
theorem B920207 : Blo 916578 920207 := bstep (se 1 (by rfl) ⟨690155, by rfl⟩ : syracuseStep 920207 = 1380311) B1380311
theorem B1379003 : Blo 916578 1379003 := bstep (se 1 (by rfl) ⟨1034252, by rfl⟩ : syracuseStep 1379003 = 2068505) B2068505
theorem B920251 : Blo 916578 920251 := bstep (se 1 (by rfl) ⟨690188, by rfl⟩ : syracuseStep 920251 = 1380377) B1380377
theorem B1379063 : Blo 916578 1379063 := bstep (se 1 (by rfl) ⟨1034297, by rfl⟩ : syracuseStep 1379063 = 2068595) B2068595
theorem B920327 : Blo 916578 920327 := bstep (se 1 (by rfl) ⟨690245, by rfl⟩ : syracuseStep 920327 = 1380491) B1380491
theorem B1379087 : Blo 916578 1379087 := bstep (se 1 (by rfl) ⟨1034315, by rfl⟩ : syracuseStep 1379087 = 2068631) B2068631
theorem B920335 : Blo 916578 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B1379129 : Blo 916578 1379129 := bstep (se 2 (by rfl) ⟨517173, by rfl⟩ : syracuseStep 1379129 = 1034347) B1034347
theorem B920379 : Blo 916578 920379 := bstep (se 1 (by rfl) ⟨690284, by rfl⟩ : syracuseStep 920379 = 1380569) B1380569
theorem B2067335 : Blo 916578 2067335 := bstep (se 1 (by rfl) ⟨1550501, by rfl⟩ : syracuseStep 2067335 = 3101003) B3101003
theorem B1379207 : Blo 916578 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B920455 : Blo 916578 920455 := bstep (se 1 (by rfl) ⟨690341, by rfl⟩ : syracuseStep 920455 = 1380683) B1380683
theorem B920463 : Blo 916578 920463 := bstep (se 1 (by rfl) ⟨690347, by rfl⟩ : syracuseStep 920463 = 1380695) B1380695
theorem B1379243 : Blo 916578 1379243 := bstep (se 1 (by rfl) ⟨1034432, by rfl⟩ : syracuseStep 1379243 = 2068865) B2068865
theorem B920507 : Blo 916578 920507 := bstep (se 1 (by rfl) ⟨690380, by rfl⟩ : syracuseStep 920507 = 1380761) B1380761
theorem B1379273 : Blo 916578 1379273 := bstep (se 2 (by rfl) ⟨517227, by rfl⟩ : syracuseStep 1379273 = 1034455) B1034455
theorem B2067515 : Blo 916578 2067515 := bstep (se 1 (by rfl) ⟨1550636, by rfl⟩ : syracuseStep 2067515 = 3101273) B3101273
theorem B1379387 : Blo 916578 1379387 := bstep (se 1 (by rfl) ⟨1034540, by rfl⟩ : syracuseStep 1379387 = 2069081) B2069081
theorem B1379447 : Blo 916578 1379447 := bstep (se 1 (by rfl) ⟨1034585, by rfl⟩ : syracuseStep 1379447 = 2069171) B2069171
theorem B7441541 : Blo 916578 7441541 := bstep (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) B1395289
theorem B1379471 : Blo 916578 1379471 := bstep (se 1 (by rfl) ⟨1034603, by rfl⟩ : syracuseStep 1379471 = 2069207) B2069207
theorem B2067641 : Blo 916578 2067641 := bstep (se 2 (by rfl) ⟨775365, by rfl⟩ : syracuseStep 2067641 = 1550731) B1550731
theorem B1379513 : Blo 916578 1379513 := bstep (se 2 (by rfl) ⟨517317, by rfl⟩ : syracuseStep 1379513 = 1034635) B1034635
theorem B4656365 : Blo 916578 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B1379591 : Blo 916578 1379591 := bstep (se 1 (by rfl) ⟨1034693, by rfl⟩ : syracuseStep 1379591 = 2069387) B2069387
theorem B1379627 : Blo 916578 1379627 := bstep (se 1 (by rfl) ⟨1034720, by rfl⟩ : syracuseStep 1379627 = 2069441) B2069441
theorem B1379657 : Blo 916578 1379657 := bstep (se 2 (by rfl) ⟨517371, by rfl⟩ : syracuseStep 1379657 = 1034743) B1034743
theorem B1379771 : Blo 916578 1379771 := bstep (se 1 (by rfl) ⟨1034828, by rfl⟩ : syracuseStep 1379771 = 2069657) B2069657
theorem B1379831 : Blo 916578 1379831 := bstep (se 1 (by rfl) ⟨1034873, by rfl⟩ : syracuseStep 1379831 = 2069747) B2069747
theorem B2067983 : Blo 916578 2067983 := bstep (se 1 (by rfl) ⟨1550987, by rfl⟩ : syracuseStep 2067983 = 3101975) B3101975
theorem B1379855 : Blo 916578 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B2068001 : Blo 916578 2068001 := bstep (se 2 (by rfl) ⟨775500, by rfl⟩ : syracuseStep 2068001 = 1551001) B1551001
theorem B1379897 : Blo 916578 1379897 := bstep (se 2 (by rfl) ⟨517461, by rfl⟩ : syracuseStep 1379897 = 1034923) B1034923
theorem B5312087 : Blo 916578 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B1379975 : Blo 916578 1379975 := bstep (se 1 (by rfl) ⟨1034981, by rfl⟩ : syracuseStep 1379975 = 2069963) B2069963
theorem B1380011 : Blo 916578 1380011 := bstep (se 1 (by rfl) ⟨1035008, by rfl⟩ : syracuseStep 1380011 = 2070017) B2070017
theorem B1380041 : Blo 916578 1380041 := bstep (se 2 (by rfl) ⟨517515, by rfl⟩ : syracuseStep 1380041 = 1035031) B1035031
theorem B7442225 : Blo 916578 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B1380155 : Blo 916578 1380155 := bstep (se 1 (by rfl) ⟨1035116, by rfl⟩ : syracuseStep 1380155 = 2070233) B2070233
theorem B2068343 : Blo 916578 2068343 := bstep (se 1 (by rfl) ⟨1551257, by rfl⟩ : syracuseStep 2068343 = 3102515) B3102515
theorem B1380215 : Blo 916578 1380215 := bstep (se 1 (by rfl) ⟨1035161, by rfl⟩ : syracuseStep 1380215 = 2070323) B2070323
theorem B1380239 : Blo 916578 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B1380281 : Blo 916578 1380281 := bstep (se 2 (by rfl) ⟨517605, by rfl⟩ : syracuseStep 1380281 = 1035211) B1035211
theorem B1380359 : Blo 916578 1380359 := bstep (se 1 (by rfl) ⟨1035269, by rfl⟩ : syracuseStep 1380359 = 2070539) B2070539
theorem B4657175 : Blo 916578 4657175 := bstep (se 1 (by rfl) ⟨3492881, by rfl⟩ : syracuseStep 4657175 = 6985763) B6985763
theorem B2068523 : Blo 916578 2068523 := bstep (se 1 (by rfl) ⟨1551392, by rfl⟩ : syracuseStep 2068523 = 3102785) B3102785
theorem B1380395 : Blo 916578 1380395 := bstep (se 1 (by rfl) ⟨1035296, by rfl⟩ : syracuseStep 1380395 = 2070593) B2070593
theorem B1380425 : Blo 916578 1380425 := bstep (se 2 (by rfl) ⟨517659, by rfl⟩ : syracuseStep 1380425 = 1035319) B1035319
theorem B1380539 : Blo 916578 1380539 := bstep (se 1 (by rfl) ⟨1035404, by rfl⟩ : syracuseStep 1380539 = 2070809) B2070809
theorem B7835885 : Blo 916578 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B1380599 : Blo 916578 1380599 := bstep (se 1 (by rfl) ⟨1035449, by rfl⟩ : syracuseStep 1380599 = 2070899) B2070899
theorem B1380623 : Blo 916578 1380623 := bstep (se 1 (by rfl) ⟨1035467, by rfl⟩ : syracuseStep 1380623 = 2070935) B2070935
theorem B1380665 : Blo 916578 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B1380743 : Blo 916578 1380743 := bstep (se 1 (by rfl) ⟨1035557, by rfl⟩ : syracuseStep 1380743 = 2071115) B2071115
theorem B2068883 : Blo 916578 2068883 := bstep (se 1 (by rfl) ⟨1551662, by rfl⟩ : syracuseStep 2068883 = 3103325) B3103325
theorem B1380779 : Blo 916578 1380779 := bstep (se 1 (by rfl) ⟨1035584, by rfl⟩ : syracuseStep 1380779 = 2071169) B2071169
theorem B2068937 : Blo 916578 2068937 := bstep (se 2 (by rfl) ⟨775851, by rfl⟩ : syracuseStep 2068937 = 1551703) B1551703
theorem B1380809 : Blo 916578 1380809 := bstep (se 2 (by rfl) ⟨517803, by rfl⟩ : syracuseStep 1380809 = 1035607) B1035607
theorem B1741513 : Blo 916578 1741513 := bstep (se 2 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 1741513 = 1306135) B1306135
theorem B2790263 : Blo 916578 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B6984791 : Blo 916578 6984791 := bstep (se 1 (by rfl) ⟨5238593, by rfl⟩ : syracuseStep 6984791 = 10477187) B10477187
theorem B2069639 : Blo 916578 2069639 := bstep (se 1 (by rfl) ⟨1552229, by rfl⟩ : syracuseStep 2069639 = 3104459) B3104459
theorem B2790553 : Blo 916578 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B2069819 : Blo 916578 2069819 := bstep (se 1 (by rfl) ⟨1552364, by rfl⟩ : syracuseStep 2069819 = 3104729) B3104729
theorem B2069945 : Blo 916578 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B9442745 : Blo 916578 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B2070287 : Blo 916578 2070287 := bstep (se 1 (by rfl) ⟨1552715, by rfl⟩ : syracuseStep 2070287 = 3105431) B3105431
theorem B2070305 : Blo 916578 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B2070647 : Blo 916578 2070647 := bstep (se 1 (by rfl) ⟨1552985, by rfl⟩ : syracuseStep 2070647 = 3105971) B3105971
theorem B2070827 : Blo 916578 2070827 := bstep (se 1 (by rfl) ⟨1553120, by rfl⟩ : syracuseStep 2070827 = 3106241) B3106241
theorem B8591761 : Blo 916578 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B10459691 : Blo 916578 10459691 := bstep (se 1 (by rfl) ⟨7844768, by rfl⟩ : syracuseStep 10459691 = 15689537) B15689537
theorem B1743419 : Blo 916578 1743419 := bstep (se 1 (by rfl) ⟨1307564, by rfl⟩ : syracuseStep 1743419 = 2615129) B2615129
theorem B2071187 : Blo 916578 2071187 := bstep (se 1 (by rfl) ⟨1553390, by rfl⟩ : syracuseStep 2071187 = 3106781) B3106781
theorem B2071241 : Blo 916578 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B6626063 : Blo 916578 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B3480353 : Blo 916578 3480353 := bstep (se 2 (by rfl) ⟨1305132, by rfl⟩ : syracuseStep 3480353 = 2610265) B2610265
theorem B4660253 : Blo 916578 4660253 := bstep (se 3 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 4660253 = 1747595) B1747595
theorem B1743905 : Blo 916578 1743905 := bstep (se 2 (by rfl) ⟨653964, by rfl⟩ : syracuseStep 1743905 = 1307929) B1307929
theorem B1547383 : Blo 916578 1547383 := bstep (se 1 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 1547383 = 2321075) B2321075
theorem B1547579 : Blo 916578 1547579 := bstep (se 1 (by rfl) ⟨1160684, by rfl⟩ : syracuseStep 1547579 = 2321369) B2321369
theorem B1744247 : Blo 916578 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B21175987 : Blo 916578 21175987 := bstep (se 1 (by rfl) ⟨15881990, by rfl⟩ : syracuseStep 21175987 = 31763981) B31763981
theorem B1547977 : Blo 916578 1547977 := bstep (se 2 (by rfl) ⟨580491, by rfl⟩ : syracuseStep 1547977 = 1160983) B1160983
theorem B3481325 : Blo 916578 3481325 := bstep (se 3 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 3481325 = 1305497) B1305497
theorem B1417223 : Blo 916578 1417223 := bstep (se 1 (by rfl) ⟨1062917, by rfl⟩ : syracuseStep 1417223 = 2125835) B2125835
theorem B3481643 : Blo 916578 3481643 := bstep (se 1 (by rfl) ⟨2611232, by rfl⟩ : syracuseStep 3481643 = 5222465) B5222465
theorem B17670413 : Blo 916578 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B1548679 : Blo 916578 1548679 := bstep (se 1 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 1548679 = 2323019) B2323019
theorem B7840259 : Blo 916578 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B2204459 : Blo 916578 2204459 := bstep (se 1 (by rfl) ⟨1653344, by rfl⟩ : syracuseStep 2204459 = 3306689) B3306689
theorem B1745849 : Blo 916578 1745849 := bstep (se 2 (by rfl) ⟨654693, by rfl⟩ : syracuseStep 1745849 = 1309387) B1309387
theorem B1549327 : Blo 916578 1549327 := bstep (se 1 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 1549327 = 2323991) B2323991
theorem B2204873 : Blo 916578 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B1746191 : Blo 916578 1746191 := bstep (se 1 (by rfl) ⟨1309643, by rfl⟩ : syracuseStep 1746191 = 2619287) B2619287
theorem B1549867 : Blo 916578 1549867 := bstep (se 1 (by rfl) ⟨1162400, by rfl⟩ : syracuseStep 1549867 = 2324801) B2324801
theorem B1550009 : Blo 916578 1550009 := bstep (se 2 (by rfl) ⟨581253, by rfl⟩ : syracuseStep 1550009 = 1162507) B1162507
theorem B7939889 : Blo 916578 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B1747003 : Blo 916578 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1747079 : Blo 916578 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1550711 : Blo 916578 1550711 := bstep (se 1 (by rfl) ⟨1163033, by rfl⟩ : syracuseStep 1550711 = 2326067) B2326067
theorem B1747489 : Blo 916578 1747489 := bstep (se 2 (by rfl) ⟨655308, by rfl⟩ : syracuseStep 1747489 = 1310617) B1310617
theorem B1551163 : Blo 916578 1551163 := bstep (se 1 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 1551163 = 2326745) B2326745
theorem B2206649 : Blo 916578 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1551305 : Blo 916578 1551305 := bstep (se 2 (by rfl) ⟨581739, by rfl⟩ : syracuseStep 1551305 = 1163479) B1163479
theorem B19868759 : Blo 916578 19868759 := bstep (se 1 (by rfl) ⟨14901569, by rfl⟩ : syracuseStep 19868759 = 29803139) B29803139
theorem B5221691 : Blo 916578 5221691 := bstep (se 1 (by rfl) ⟨3916268, by rfl⟩ : syracuseStep 5221691 = 7832537) B7832537
theorem B8957405 : Blo 916578 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B3485213 : Blo 916578 3485213 := bstep (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) B1306955
theorem B3485227 : Blo 916578 3485227 := bstep (se 1 (by rfl) ⟨2613920, by rfl⟩ : syracuseStep 3485227 = 5227841) B5227841
theorem B1552007 : Blo 916578 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B1552655 : Blo 916578 1552655 := bstep (se 1 (by rfl) ⟨1164491, by rfl⟩ : syracuseStep 1552655 = 2328983) B2328983
theorem B5223149 : Blo 916578 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B1553195 : Blo 916578 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B1160183 : Blo 916578 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B2798621 : Blo 916578 2798621 := bstep (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) B1049483
theorem B5223467 : Blo 916578 5223467 := bstep (se 1 (by rfl) ⟨3917600, by rfl⟩ : syracuseStep 5223467 = 7835201) B7835201
theorem B23540867 : Blo 916578 23540867 := bstep (se 1 (by rfl) ⟨17655650, by rfl⟩ : syracuseStep 23540867 = 35311301) B35311301
theorem B1160335 : Blo 916578 1160335 := bstep (se 1 (by rfl) ⟨870251, by rfl⟩ : syracuseStep 1160335 = 1740503) B1740503
theorem B2209025 : Blo 916578 2209025 := bstep (se 2 (by rfl) ⟨828384, by rfl⟩ : syracuseStep 2209025 = 1656769) B1656769
theorem B1160507 : Blo 916578 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B3093875 : Blo 916578 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B5879249 : Blo 916578 5879249 := bstep (se 2 (by rfl) ⟨2204718, by rfl⟩ : syracuseStep 5879249 = 4409437) B4409437
theorem B1488443 : Blo 916578 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B1324603 : Blo 916578 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B5584787 : Blo 916578 5584787 := bstep (se 1 (by rfl) ⟨4188590, by rfl⟩ : syracuseStep 5584787 = 8377181) B8377181
theorem B1161479 : Blo 916578 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B8370641 : Blo 916578 8370641 := bstep (se 2 (by rfl) ⟨3138990, by rfl⟩ : syracuseStep 8370641 = 6277981) B6277981
theorem B9943505 : Blo 916578 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B5224925 : Blo 916578 5224925 := bstep (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) B1959347
theorem B1653367 : Blo 916578 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B1162127 : Blo 916578 1162127 := bstep (se 1 (by rfl) ⟨871595, by rfl⟩ : syracuseStep 1162127 = 1743191) B1743191
theorem B4537241 : Blo 916578 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B3357649 : Blo 916578 3357649 := bstep (se 2 (by rfl) ⟨1259118, by rfl⟩ : syracuseStep 3357649 = 2518237) B2518237
theorem B10468439 : Blo 916578 10468439 := bstep (se 1 (by rfl) ⟨7851329, by rfl⟩ : syracuseStep 10468439 = 15702659) B15702659
theorem B1031431 : Blo 916578 1031431 := bstep (se 1 (by rfl) ⟨773573, by rfl⟩ : syracuseStep 1031431 = 1547147) B1547147
theorem B1031611 : Blo 916578 1031611 := bstep (se 1 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 1031611 = 1547417) B1547417
theorem B1032079 : Blo 916578 1032079 := bstep (se 1 (by rfl) ⟨774059, by rfl⟩ : syracuseStep 1032079 = 1548119) B1548119
theorem B3096467 : Blo 916578 3096467 := bstep (se 1 (by rfl) ⟨2322350, by rfl⟩ : syracuseStep 3096467 = 4644701) B4644701
theorem B8503319 : Blo 916578 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B17645809 : Blo 916578 17645809 := bstep (se 2 (by rfl) ⟨6617178, by rfl⟩ : syracuseStep 17645809 = 13234357) B13234357
theorem B9421073 : Blo 916578 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B2834731 : Blo 916578 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B1032583 : Blo 916578 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B1032763 : Blo 916578 1032763 := bstep (se 1 (by rfl) ⟨774572, by rfl⟩ : syracuseStep 1032763 = 1549145) B1549145
theorem B3490391 : Blo 916578 3490391 := bstep (se 1 (by rfl) ⟨2617793, by rfl⟩ : syracuseStep 3490391 = 5235587) B5235587
theorem B5653111 : Blo 916578 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B5227523 : Blo 916578 5227523 := bstep (se 1 (by rfl) ⟨3920642, by rfl⟩ : syracuseStep 5227523 = 7841285) B7841285
theorem B1033231 : Blo 916578 1033231 := bstep (se 1 (by rfl) ⟨774923, by rfl⟩ : syracuseStep 1033231 = 1549847) B1549847
theorem B1655867 : Blo 916578 1655867 := bstep (se 1 (by rfl) ⟨1241900, by rfl⟩ : syracuseStep 1655867 = 2483801) B2483801
theorem B3490877 : Blo 916578 3490877 := bstep (se 3 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 3490877 = 1309079) B1309079
theorem B4965569 : Blo 916578 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B3097871 : Blo 916578 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B1033735 : Blo 916578 1033735 := bstep (se 1 (by rfl) ⟨775301, by rfl⟩ : syracuseStep 1033735 = 1550603) B1550603
theorem B3098141 : Blo 916578 3098141 := bstep (se 3 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 3098141 = 1161803) B1161803
theorem B1033915 : Blo 916578 1033915 := bstep (se 1 (by rfl) ⟨775436, by rfl⟩ : syracuseStep 1033915 = 1550873) B1550873
theorem B1165099 : Blo 916578 1165099 := bstep (se 1 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 1165099 = 1747649) B1747649
theorem B4409147 : Blo 916578 4409147 := bstep (se 1 (by rfl) ⟨3306860, by rfl⟩ : syracuseStep 4409147 = 6613721) B6613721
theorem B37668887 : Blo 916578 37668887 := bstep (se 1 (by rfl) ⟨28251665, by rfl⟩ : syracuseStep 37668887 = 56503331) B56503331
theorem B1034383 : Blo 916578 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B4704545 : Blo 916578 4704545 := bstep (se 2 (by rfl) ⟨1764204, by rfl⟩ : syracuseStep 4704545 = 3528409) B3528409
theorem B3492305 : Blo 916578 3492305 := bstep (se 2 (by rfl) ⟨1309614, by rfl⟩ : syracuseStep 3492305 = 2619229) B2619229
theorem B11749931 : Blo 916578 11749931 := bstep (se 1 (by rfl) ⟨8812448, by rfl⟩ : syracuseStep 11749931 = 17624897) B17624897
theorem B6965837 : Blo 916578 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B1034887 : Blo 916578 1034887 := bstep (se 1 (by rfl) ⟨776165, by rfl⟩ : syracuseStep 1034887 = 1552331) B1552331
theorem B5655329 : Blo 916578 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B1035067 : Blo 916578 1035067 := bstep (se 1 (by rfl) ⟨776300, by rfl⟩ : syracuseStep 1035067 = 1552601) B1552601
theorem B3099545 : Blo 916578 3099545 := bstep (se 2 (by rfl) ⟨1162329, by rfl⟩ : syracuseStep 3099545 = 2324659) B2324659
theorem B8834285 : Blo 916578 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B1035535 : Blo 916578 1035535 := bstep (se 1 (by rfl) ⟨776651, by rfl⟩ : syracuseStep 1035535 = 1553303) B1553303
theorem B7556651 : Blo 916578 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B2936407 : Blo 916578 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B3100247 : Blo 916578 3100247 := bstep (se 1 (by rfl) ⟨2325185, by rfl⟩ : syracuseStep 3100247 = 4650371) B4650371
theorem B6606859 : Blo 916578 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B8376331 : Blo 916578 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B3100733 : Blo 916578 3100733 := bstep (se 3 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 3100733 = 1162775) B1162775
theorem B3493975 : Blo 916578 3493975 := bstep (se 1 (by rfl) ⟨2620481, by rfl⟩ : syracuseStep 3493975 = 5240963) B5240963
theorem B7852423 : Blo 916578 7852423 := bstep (se 1 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 7852423 = 11778635) B11778635
theorem B3494279 : Blo 916578 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B3494461 : Blo 916578 3494461 := bstep (se 3 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 3494461 = 1310423) B1310423
theorem B13587011 : Blo 916578 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B1397321 : Blo 916578 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B3920471 : Blo 916578 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B7459447 : Blo 916578 7459447 := bstep (se 1 (by rfl) ⟨5594585, by rfl⟩ : syracuseStep 7459447 = 11189171) B11189171
theorem B54317699 : Blo 916578 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B6968267 : Blo 916578 6968267 := bstep (se 1 (by rfl) ⟨5226200, by rfl⟩ : syracuseStep 6968267 = 10452401) B10452401
theorem B3724355 : Blo 916578 3724355 := bstep (se 1 (by rfl) ⟨2793266, by rfl⟩ : syracuseStep 3724355 = 5586533) B5586533
theorem B11785607 : Blo 916578 11785607 := bstep (se 1 (by rfl) ⟨8839205, by rfl⟩ : syracuseStep 11785607 = 17678411) B17678411
theorem B4412819 : Blo 916578 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B3102137 : Blo 916578 3102137 := bstep (se 2 (by rfl) ⟨1163301, by rfl⟩ : syracuseStep 3102137 = 2326603) B2326603
theorem B2610731 : Blo 916578 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B5232215 : Blo 916578 5232215 := bstep (se 1 (by rfl) ⟨3924161, by rfl⟩ : syracuseStep 5232215 = 7848323) B7848323
theorem B5592979 : Blo 916578 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B1103863 : Blo 916578 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B1398775 : Blo 916578 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B3102731 : Blo 916578 3102731 := bstep (se 1 (by rfl) ⟨2327048, by rfl⟩ : syracuseStep 3102731 = 4654097) B4654097
theorem B22337653 : Blo 916578 22337653 := bstep (se 5 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 22337653 = 2094155) B2094155
theorem B3102839 : Blo 916578 3102839 := bstep (se 1 (by rfl) ⟨2327129, by rfl⟩ : syracuseStep 3102839 = 4654259) B4654259
theorem B2611723 : Blo 916578 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B28269121 : Blo 916578 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B3103433 : Blo 916578 3103433 := bstep (se 2 (by rfl) ⟨1163787, by rfl⟩ : syracuseStep 3103433 = 2327575) B2327575
theorem B15915791 : Blo 916578 15915791 := bstep (se 1 (by rfl) ⟨11936843, by rfl⟩ : syracuseStep 15915791 = 23873687) B23873687
theorem B2611997 : Blo 916578 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B4643729 : Blo 916578 4643729 := bstep (se 2 (by rfl) ⟨1741398, by rfl⟩ : syracuseStep 4643729 = 3482797) B3482797
theorem B21748661 : Blo 916578 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B3104135 : Blo 916578 3104135 := bstep (se 1 (by rfl) ⟨2328101, by rfl⟩ : syracuseStep 3104135 = 4656203) B4656203
theorem B3726739 : Blo 916578 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B5234129 : Blo 916578 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B4185611 : Blo 916578 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B1859105 : Blo 916578 1859105 := bstep (se 2 (by rfl) ⟨697164, by rfl⟩ : syracuseStep 1859105 = 1394329) B1394329
theorem B4972099 : Blo 916578 4972099 := bstep (se 1 (by rfl) ⟨3729074, by rfl⟩ : syracuseStep 4972099 = 7458149) B7458149
theorem B1007239 : Blo 916578 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B3104513 : Blo 916578 3104513 := bstep (se 2 (by rfl) ⟨1164192, by rfl⟩ : syracuseStep 3104513 = 2328385) B2328385
theorem B4415759 : Blo 916578 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2646539 : Blo 916578 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B3105323 : Blo 916578 3105323 := bstep (se 1 (by rfl) ⟨2328992, by rfl⟩ : syracuseStep 3105323 = 4657985) B4657985
theorem B13263425 : Blo 916578 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B1958519 : Blo 916578 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B4842185 : Blo 916578 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B8938291 : Blo 916578 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B2614103 : Blo 916578 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B2351987 : Blo 916578 2351987 := bstep (se 1 (by rfl) ⟨1763990, by rfl⟩ : syracuseStep 2351987 = 3527981) B3527981
theorem B1860499 : Blo 916578 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B4645835 : Blo 916578 4645835 := bstep (se 1 (by rfl) ⟨3484376, by rfl⟩ : syracuseStep 4645835 = 6968753) B6968753
theorem B2614331 : Blo 916578 2614331 := bstep (se 1 (by rfl) ⟨1960748, by rfl⟩ : syracuseStep 2614331 = 3921497) B3921497
theorem B2614457 : Blo 916578 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B4646159 : Blo 916578 4646159 := bstep (se 1 (by rfl) ⟨3484619, by rfl⟩ : syracuseStep 4646159 = 6969239) B6969239
theorem B8381729 : Blo 916578 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B42362297 : Blo 916578 42362297 := bstep (se 2 (by rfl) ⟨15885861, by rfl⟩ : syracuseStep 42362297 = 31771723) B31771723
theorem B6383033 : Blo 916578 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B14116355 : Blo 916578 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B2942507 : Blo 916578 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B3106619 : Blo 916578 3106619 := bstep (se 1 (by rfl) ⟨2329964, by rfl⟩ : syracuseStep 3106619 = 4659929) B4659929
theorem B2484083 : Blo 916578 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B2942905 : Blo 916578 2942905 := bstep (se 2 (by rfl) ⟨1103589, by rfl⟩ : syracuseStep 2942905 = 2207179) B2207179
theorem B2320427 : Blo 916578 2320427 := bstep (se 1 (by rfl) ⟨1740320, by rfl⟩ : syracuseStep 2320427 = 3480641) B3480641
theorem B6973613 : Blo 916578 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B3303661 : Blo 916578 3303661 := bstep (se 3 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 3303661 = 1238873) B1238873
theorem B5892497 : Blo 916578 5892497 := bstep (se 2 (by rfl) ⟨2209686, by rfl⟩ : syracuseStep 5892497 = 4419373) B4419373
theorem B4974995 : Blo 916578 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B3303965 : Blo 916578 3303965 := bstep (se 3 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 3303965 = 1238987) B1238987
theorem B1960595 : Blo 916578 1960595 := bstep (se 1 (by rfl) ⟨1470446, by rfl⟩ : syracuseStep 1960595 = 2940893) B2940893
theorem B4647617 : Blo 916578 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B2616097 : Blo 916578 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B1239943 : Blo 916578 1239943 := bstep (se 1 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 1239943 = 1859915) B1859915
theorem B4779011 : Blo 916578 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B2321419 : Blo 916578 2321419 := bstep (se 1 (by rfl) ⟨1741064, by rfl⟩ : syracuseStep 2321419 = 3482129) B3482129
theorem B2321561 : Blo 916578 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B1436935 : Blo 916578 1436935 := bstep (se 1 (by rfl) ⟨1077701, by rfl⟩ : syracuseStep 1436935 = 2155403) B2155403
theorem B2616587 : Blo 916578 2616587 := bstep (se 1 (by rfl) ⟨1962440, by rfl⟩ : syracuseStep 2616587 = 3924881) B3924881
theorem B2321723 : Blo 916578 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B17493347 : Blo 916578 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B1469831 : Blo 916578 1469831 := bstep (se 1 (by rfl) ⟨1102373, by rfl⟩ : syracuseStep 1469831 = 2204747) B2204747
theorem B5041693 : Blo 916578 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B2322067 : Blo 916578 2322067 := bstep (se 1 (by rfl) ⟨1741550, by rfl⟩ : syracuseStep 2322067 = 3483101) B3483101
theorem B2322209 : Blo 916578 2322209 := bstep (se 2 (by rfl) ⟨870828, by rfl⟩ : syracuseStep 2322209 = 1741657) B1741657
theorem B10481561 : Blo 916578 10481561 := bstep (se 2 (by rfl) ⟨3930585, by rfl⟩ : syracuseStep 10481561 = 7861171) B7861171
theorem B4648913 : Blo 916578 4648913 := bstep (se 2 (by rfl) ⟨1743342, by rfl⟩ : syracuseStep 4648913 = 3486685) B3486685
theorem B2617373 : Blo 916578 2617373 := bstep (se 3 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 2617373 = 981515) B981515
theorem B4255811 : Blo 916578 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B5239187 : Blo 916578 5239187 := bstep (se 1 (by rfl) ⟨3929390, by rfl⟩ : syracuseStep 5239187 = 7858781) B7858781
theorem B6976043 : Blo 916578 6976043 := bstep (se 1 (by rfl) ⟨5232032, by rfl⟩ : syracuseStep 6976043 = 10464065) B10464065
theorem B10449485 : Blo 916578 10449485 := bstep (se 3 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 10449485 = 3918557) B3918557
theorem B1208975 : Blo 916578 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B2323201 : Blo 916578 2323201 := bstep (se 2 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 2323201 = 1742401) B1742401
theorem B6615857 : Blo 916578 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B5239687 : Blo 916578 5239687 := bstep (se 1 (by rfl) ⟨3929765, by rfl⟩ : syracuseStep 5239687 = 7859531) B7859531
theorem B1307593 : Blo 916578 1307593 := bstep (se 2 (by rfl) ⟨490347, by rfl⟩ : syracuseStep 1307593 = 980695) B980695
theorem B3142685 : Blo 916578 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B2094265 : Blo 916578 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B2323799 : Blo 916578 2323799 := bstep (se 1 (by rfl) ⟨1742849, by rfl⟩ : syracuseStep 2323799 = 3485699) B3485699
theorem B2487671 : Blo 916578 2487671 := bstep (se 1 (by rfl) ⟨1865753, by rfl⟩ : syracuseStep 2487671 = 3731507) B3731507
theorem B9434627 : Blo 916578 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B3929629 : Blo 916578 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B2324011 : Blo 916578 2324011 := bstep (se 1 (by rfl) ⟨1743008, by rfl⟩ : syracuseStep 2324011 = 3486017) B3486017
theorem B2324153 : Blo 916578 2324153 := bstep (se 2 (by rfl) ⟨871557, by rfl⟩ : syracuseStep 2324153 = 1743115) B1743115
theorem B1963721 : Blo 916578 1963721 := bstep (se 2 (by rfl) ⟨736395, by rfl⟩ : syracuseStep 1963721 = 1472791) B1472791
theorem B7370585 : Blo 916578 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B3929971 : Blo 916578 3929971 := bstep (se 1 (by rfl) ⟨2947478, by rfl⟩ : syracuseStep 3929971 = 5894957) B5894957
theorem B1472375 : Blo 916578 1472375 := bstep (se 1 (by rfl) ⟨1104281, by rfl⟩ : syracuseStep 1472375 = 2208563) B2208563
theorem B4651019 : Blo 916578 4651019 := bstep (se 1 (by rfl) ⟨3488264, by rfl⟩ : syracuseStep 4651019 = 6976529) B6976529
theorem B2619479 : Blo 916578 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B4651181 : Blo 916578 4651181 := bstep (se 3 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 4651181 = 1744193) B1744193
theorem B2062727 : Blo 916578 2062727 := bstep (se 1 (by rfl) ⟨1547045, by rfl⟩ : syracuseStep 2062727 = 3094091) B3094091
theorem B95451533 : Blo 916578 95451533 := bstep (se 3 (by rfl) ⟨17897162, by rfl⟩ : syracuseStep 95451533 = 35794325) B35794325
theorem B981391 : Blo 916578 981391 := bstep (se 1 (by rfl) ⟨736043, by rfl⟩ : syracuseStep 981391 = 1472087) B1472087
theorem B2062907 : Blo 916578 2062907 := bstep (se 1 (by rfl) ⟨1547180, by rfl⟩ : syracuseStep 2062907 = 3094361) B3094361
theorem B2325145 : Blo 916578 2325145 := bstep (se 2 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 2325145 = 1743859) B1743859
theorem B1374905 : Blo 916578 1374905 := bstep (se 2 (by rfl) ⟨515589, by rfl⟩ : syracuseStep 1374905 = 1031179) B1031179
theorem B2063033 : Blo 916578 2063033 := bstep (se 2 (by rfl) ⟨773637, by rfl⟩ : syracuseStep 2063033 = 1547275) B1547275
theorem B1374983 : Blo 916578 1374983 := bstep (se 1 (by rfl) ⟨1031237, by rfl⟩ : syracuseStep 1374983 = 2062475) B2062475
theorem B981767 : Blo 916578 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B7535375 : Blo 916578 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B14875427 : Blo 916578 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B9927461 : Blo 916578 9927461 := bstep (se 4 (by rfl) ⟨930699, by rfl⟩ : syracuseStep 9927461 = 1861399) B1861399
theorem B1375019 : Blo 916578 1375019 := bstep (se 1 (by rfl) ⟨1031264, by rfl⟩ : syracuseStep 1375019 = 2062529) B2062529
theorem B2325307 : Blo 916578 2325307 := bstep (se 1 (by rfl) ⟨1743980, by rfl⟩ : syracuseStep 2325307 = 3487961) B3487961
theorem B1375049 : Blo 916578 1375049 := bstep (se 2 (by rfl) ⟨515643, by rfl⟩ : syracuseStep 1375049 = 1031287) B1031287
theorem B7863155 : Blo 916578 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B2620345 : Blo 916578 2620345 := bstep (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) B1965259
theorem B1375163 : Blo 916578 1375163 := bstep (se 1 (by rfl) ⟨1031372, by rfl⟩ : syracuseStep 1375163 = 2062745) B2062745
theorem B2325449 : Blo 916578 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B1375223 : Blo 916578 1375223 := bstep (se 1 (by rfl) ⟨1031417, by rfl⟩ : syracuseStep 1375223 = 2062835) B2062835
theorem B1375247 : Blo 916578 1375247 := bstep (se 1 (by rfl) ⟨1031435, by rfl⟩ : syracuseStep 1375247 = 2062871) B2062871
theorem B2063375 : Blo 916578 2063375 := bstep (se 1 (by rfl) ⟨1547531, by rfl⟩ : syracuseStep 2063375 = 3095063) B3095063
theorem B2063393 : Blo 916578 2063393 := bstep (se 2 (by rfl) ⟨773772, by rfl⟩ : syracuseStep 2063393 = 1547545) B1547545
theorem B1375289 : Blo 916578 1375289 := bstep (se 2 (by rfl) ⟨515733, by rfl⟩ : syracuseStep 1375289 = 1031467) B1031467
theorem B916615 : Blo 916578 916615 := bstep (se 1 (by rfl) ⟨687461, by rfl⟩ : syracuseStep 916615 = 1374923) B1374923
theorem B1375367 : Blo 916578 1375367 := bstep (se 1 (by rfl) ⟨1031525, by rfl⟩ : syracuseStep 1375367 = 2063051) B2063051
theorem B916623 : Blo 916578 916623 := bstep (se 1 (by rfl) ⟨687467, by rfl⟩ : syracuseStep 916623 = 1374935) B1374935
theorem B1375403 : Blo 916578 1375403 := bstep (se 1 (by rfl) ⟨1031552, by rfl⟩ : syracuseStep 1375403 = 2063105) B2063105
theorem B916667 : Blo 916578 916667 := bstep (se 1 (by rfl) ⟨687500, by rfl⟩ : syracuseStep 916667 = 1375001) B1375001
theorem B1375433 : Blo 916578 1375433 := bstep (se 2 (by rfl) ⟨515787, by rfl⟩ : syracuseStep 1375433 = 1031575) B1031575
theorem B916743 : Blo 916578 916743 := bstep (se 1 (by rfl) ⟨687557, by rfl⟩ : syracuseStep 916743 = 1375115) B1375115
theorem B916751 : Blo 916578 916751 := bstep (se 1 (by rfl) ⟨687563, by rfl⟩ : syracuseStep 916751 = 1375127) B1375127
theorem B2620687 : Blo 916578 2620687 := bstep (se 1 (by rfl) ⟨1965515, by rfl⟩ : syracuseStep 2620687 = 3931031) B3931031
theorem B2325793 : Blo 916578 2325793 := bstep (se 2 (by rfl) ⟨872172, by rfl⟩ : syracuseStep 2325793 = 1744345) B1744345
theorem B916795 : Blo 916578 916795 := bstep (se 1 (by rfl) ⟨687596, by rfl⟩ : syracuseStep 916795 = 1375193) B1375193
theorem B1375547 : Blo 916578 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B1375607 : Blo 916578 1375607 := bstep (se 1 (by rfl) ⟨1031705, by rfl⟩ : syracuseStep 1375607 = 2063411) B2063411
theorem B2063735 : Blo 916578 2063735 := bstep (se 1 (by rfl) ⟨1547801, by rfl⟩ : syracuseStep 2063735 = 3095603) B3095603
theorem B916871 : Blo 916578 916871 := bstep (se 1 (by rfl) ⟨687653, by rfl⟩ : syracuseStep 916871 = 1375307) B1375307
theorem B916879 : Blo 916578 916879 := bstep (se 1 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 916879 = 1375319) B1375319
theorem B1375631 : Blo 916578 1375631 := bstep (se 1 (by rfl) ⟨1031723, by rfl⟩ : syracuseStep 1375631 = 2063447) B2063447
theorem B1375673 : Blo 916578 1375673 := bstep (se 2 (by rfl) ⟨515877, by rfl⟩ : syracuseStep 1375673 = 1031755) B1031755
theorem B916923 : Blo 916578 916923 := bstep (se 1 (by rfl) ⟨687692, by rfl⟩ : syracuseStep 916923 = 1375385) B1375385
theorem B982459 : Blo 916578 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B916999 : Blo 916578 916999 := bstep (se 1 (by rfl) ⟨687749, by rfl⟩ : syracuseStep 916999 = 1375499) B1375499
theorem B1375751 : Blo 916578 1375751 := bstep (se 1 (by rfl) ⟨1031813, by rfl⟩ : syracuseStep 1375751 = 2063627) B2063627
theorem B917007 : Blo 916578 917007 := bstep (se 1 (by rfl) ⟨687755, by rfl⟩ : syracuseStep 917007 = 1375511) B1375511
theorem B2620961 : Blo 916578 2620961 := bstep (se 2 (by rfl) ⟨982860, by rfl⟩ : syracuseStep 2620961 = 1965721) B1965721
theorem B1375787 : Blo 916578 1375787 := bstep (se 1 (by rfl) ⟨1031840, by rfl⟩ : syracuseStep 1375787 = 2063681) B2063681
theorem B2063915 : Blo 916578 2063915 := bstep (se 1 (by rfl) ⟨1547936, by rfl⟩ : syracuseStep 2063915 = 3095873) B3095873
theorem B917051 : Blo 916578 917051 := bstep (se 1 (by rfl) ⟨687788, by rfl⟩ : syracuseStep 917051 = 1375577) B1375577
theorem B1375817 : Blo 916578 1375817 := bstep (se 2 (by rfl) ⟨515931, by rfl⟩ : syracuseStep 1375817 = 1031863) B1031863
theorem B917127 : Blo 916578 917127 := bstep (se 1 (by rfl) ⟨687845, by rfl⟩ : syracuseStep 917127 = 1375691) B1375691
theorem B1965703 : Blo 916578 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B917135 : Blo 916578 917135 := bstep (se 1 (by rfl) ⟨687851, by rfl⟩ : syracuseStep 917135 = 1375703) B1375703
theorem B917179 : Blo 916578 917179 := bstep (se 1 (by rfl) ⟨687884, by rfl⟩ : syracuseStep 917179 = 1375769) B1375769
theorem B1375931 : Blo 916578 1375931 := bstep (se 1 (by rfl) ⟨1031948, by rfl⟩ : syracuseStep 1375931 = 2063897) B2063897
theorem B1375991 : Blo 916578 1375991 := bstep (se 1 (by rfl) ⟨1031993, by rfl⟩ : syracuseStep 1375991 = 2063987) B2063987
theorem B4652801 : Blo 916578 4652801 := bstep (se 2 (by rfl) ⟨1744800, by rfl⟩ : syracuseStep 4652801 = 3489601) B3489601
theorem B917255 : Blo 916578 917255 := bstep (se 1 (by rfl) ⟨687941, by rfl⟩ : syracuseStep 917255 = 1375883) B1375883
theorem B917263 : Blo 916578 917263 := bstep (se 1 (by rfl) ⟨687947, by rfl⟩ : syracuseStep 917263 = 1375895) B1375895
theorem B1376015 : Blo 916578 1376015 := bstep (se 1 (by rfl) ⟨1032011, by rfl⟩ : syracuseStep 1376015 = 2064023) B2064023
theorem B2096929 : Blo 916578 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B25100081 : Blo 916578 25100081 := bstep (se 2 (by rfl) ⟨9412530, by rfl⟩ : syracuseStep 25100081 = 18825061) B18825061
theorem B1376057 : Blo 916578 1376057 := bstep (se 2 (by rfl) ⟨516021, by rfl⟩ : syracuseStep 1376057 = 1032043) B1032043
theorem B917307 : Blo 916578 917307 := bstep (se 1 (by rfl) ⟨687980, by rfl⟩ : syracuseStep 917307 = 1375961) B1375961
theorem B1310537 : Blo 916578 1310537 := bstep (se 2 (by rfl) ⟨491451, by rfl⟩ : syracuseStep 1310537 = 982903) B982903
theorem B3309427 : Blo 916578 3309427 := bstep (se 1 (by rfl) ⟨2482070, by rfl⟩ : syracuseStep 3309427 = 4964141) B4964141
theorem B2326391 : Blo 916578 2326391 := bstep (se 1 (by rfl) ⟨1744793, by rfl⟩ : syracuseStep 2326391 = 3489587) B3489587
theorem B917383 : Blo 916578 917383 := bstep (se 1 (by rfl) ⟨688037, by rfl⟩ : syracuseStep 917383 = 1376075) B1376075
theorem B1376135 : Blo 916578 1376135 := bstep (se 1 (by rfl) ⟨1032101, by rfl⟩ : syracuseStep 1376135 = 2064203) B2064203
theorem B917391 : Blo 916578 917391 := bstep (se 1 (by rfl) ⟨688043, by rfl⟩ : syracuseStep 917391 = 1376087) B1376087
theorem B2064275 : Blo 916578 2064275 := bstep (se 1 (by rfl) ⟨1548206, by rfl⟩ : syracuseStep 2064275 = 3096413) B3096413
theorem B1376171 : Blo 916578 1376171 := bstep (se 1 (by rfl) ⟨1032128, by rfl⟩ : syracuseStep 1376171 = 2064257) B2064257
theorem B917435 : Blo 916578 917435 := bstep (se 1 (by rfl) ⟨688076, by rfl⟩ : syracuseStep 917435 = 1376153) B1376153
theorem B1376201 : Blo 916578 1376201 := bstep (se 2 (by rfl) ⟨516075, by rfl⟩ : syracuseStep 1376201 = 1032151) B1032151
theorem B2064329 : Blo 916578 2064329 := bstep (se 2 (by rfl) ⟨774123, by rfl⟩ : syracuseStep 2064329 = 1548247) B1548247
theorem B5668879 : Blo 916578 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B917543 : Blo 916578 917543 := bstep (se 1 (by rfl) ⟨688157, by rfl⟩ : syracuseStep 917543 = 1376315) B1376315
theorem B917583 : Blo 916578 917583 := bstep (se 1 (by rfl) ⟨688187, by rfl⟩ : syracuseStep 917583 = 1376375) B1376375
theorem B917599 : Blo 916578 917599 := bstep (se 1 (by rfl) ⟨688199, by rfl⟩ : syracuseStep 917599 = 1376399) B1376399
theorem B917627 : Blo 916578 917627 := bstep (se 1 (by rfl) ⟨688220, by rfl⟩ : syracuseStep 917627 = 1376441) B1376441
theorem B917679 : Blo 916578 917679 := bstep (se 1 (by rfl) ⟨688259, by rfl⟩ : syracuseStep 917679 = 1376519) B1376519
theorem B917703 : Blo 916578 917703 := bstep (se 1 (by rfl) ⟨688277, by rfl⟩ : syracuseStep 917703 = 1376555) B1376555
theorem B917723 : Blo 916578 917723 := bstep (se 1 (by rfl) ⟨688292, by rfl⟩ : syracuseStep 917723 = 1376585) B1376585
theorem B917799 : Blo 916578 917799 := bstep (se 1 (by rfl) ⟨688349, by rfl⟩ : syracuseStep 917799 = 1376699) B1376699
theorem B23527745 : Blo 916578 23527745 := bstep (se 2 (by rfl) ⟨8822904, by rfl⟩ : syracuseStep 23527745 = 17645809) B17645809
theorem B917839 : Blo 916578 917839 := bstep (se 1 (by rfl) ⟨688379, by rfl⟩ : syracuseStep 917839 = 1376759) B1376759
theorem B917855 : Blo 916578 917855 := bstep (se 1 (by rfl) ⟨688391, by rfl⟩ : syracuseStep 917855 = 1376783) B1376783
theorem B917883 : Blo 916578 917883 := bstep (se 1 (by rfl) ⟨688412, by rfl⟩ : syracuseStep 917883 = 1376825) B1376825
theorem B2326927 : Blo 916578 2326927 := bstep (se 1 (by rfl) ⟨1745195, by rfl⟩ : syracuseStep 2326927 = 3490391) B3490391
theorem B1376687 : Blo 916578 1376687 := bstep (se 1 (by rfl) ⟨1032515, by rfl⟩ : syracuseStep 1376687 = 2065031) B2065031
theorem B917935 : Blo 916578 917935 := bstep (se 1 (by rfl) ⟨688451, by rfl⟩ : syracuseStep 917935 = 1376903) B1376903
theorem B917959 : Blo 916578 917959 := bstep (se 1 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 917959 = 1376939) B1376939
theorem B917979 : Blo 916578 917979 := bstep (se 1 (by rfl) ⟨688484, by rfl⟩ : syracuseStep 917979 = 1376969) B1376969
theorem B2064905 : Blo 916578 2064905 := bstep (se 2 (by rfl) ⟨774339, by rfl⟩ : syracuseStep 2064905 = 1548679) B1548679
theorem B1376777 : Blo 916578 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B1376807 : Blo 916578 1376807 := bstep (se 1 (by rfl) ⟨1032605, by rfl⟩ : syracuseStep 1376807 = 2065211) B2065211
theorem B918055 : Blo 916578 918055 := bstep (se 1 (by rfl) ⟨688541, by rfl⟩ : syracuseStep 918055 = 1377083) B1377083
theorem B918095 : Blo 916578 918095 := bstep (se 1 (by rfl) ⟨688571, by rfl⟩ : syracuseStep 918095 = 1377143) B1377143
theorem B918111 : Blo 916578 918111 := bstep (se 1 (by rfl) ⟨688583, by rfl⟩ : syracuseStep 918111 = 1377167) B1377167
theorem B1376891 : Blo 916578 1376891 := bstep (se 1 (by rfl) ⟨1032668, by rfl⟩ : syracuseStep 1376891 = 2065337) B2065337
theorem B918139 : Blo 916578 918139 := bstep (se 1 (by rfl) ⟨688604, by rfl⟩ : syracuseStep 918139 = 1377209) B1377209
theorem B918191 : Blo 916578 918191 := bstep (se 1 (by rfl) ⟨688643, by rfl⟩ : syracuseStep 918191 = 1377287) B1377287
theorem B918215 : Blo 916578 918215 := bstep (se 1 (by rfl) ⟨688661, by rfl⟩ : syracuseStep 918215 = 1377323) B1377323
theorem B2327251 : Blo 916578 2327251 := bstep (se 1 (by rfl) ⟨1745438, by rfl⟩ : syracuseStep 2327251 = 3490877) B3490877
theorem B918235 : Blo 916578 918235 := bstep (se 1 (by rfl) ⟨688676, by rfl⟩ : syracuseStep 918235 = 1377353) B1377353
theorem B1377017 : Blo 916578 1377017 := bstep (se 2 (by rfl) ⟨516381, by rfl⟩ : syracuseStep 1377017 = 1032763) B1032763
theorem B918311 : Blo 916578 918311 := bstep (se 1 (by rfl) ⟨688733, by rfl⟩ : syracuseStep 918311 = 1377467) B1377467
theorem B3310379 : Blo 916578 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B7537481 : Blo 916578 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B918351 : Blo 916578 918351 := bstep (se 1 (by rfl) ⟨688763, by rfl⟩ : syracuseStep 918351 = 1377527) B1377527
theorem B2065247 : Blo 916578 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1377119 : Blo 916578 1377119 := bstep (se 1 (by rfl) ⟨1032839, by rfl⟩ : syracuseStep 1377119 = 2065679) B2065679
theorem B918367 : Blo 916578 918367 := bstep (se 1 (by rfl) ⟨688775, by rfl⟩ : syracuseStep 918367 = 1377551) B1377551
theorem B1377131 : Blo 916578 1377131 := bstep (se 1 (by rfl) ⟨1032848, by rfl⟩ : syracuseStep 1377131 = 2065697) B2065697
theorem B918395 : Blo 916578 918395 := bstep (se 1 (by rfl) ⟨688796, by rfl⟩ : syracuseStep 918395 = 1377593) B1377593
theorem B918447 : Blo 916578 918447 := bstep (se 1 (by rfl) ⟨688835, by rfl⟩ : syracuseStep 918447 = 1377671) B1377671
theorem B918471 : Blo 916578 918471 := bstep (se 1 (by rfl) ⟨688853, by rfl⟩ : syracuseStep 918471 = 1377707) B1377707
theorem B918491 : Blo 916578 918491 := bstep (se 1 (by rfl) ⟨688868, by rfl⟩ : syracuseStep 918491 = 1377737) B1377737
theorem B2065427 : Blo 916578 2065427 := bstep (se 1 (by rfl) ⟨1549070, by rfl⟩ : syracuseStep 2065427 = 3098141) B3098141
theorem B918567 : Blo 916578 918567 := bstep (se 1 (by rfl) ⟨688925, by rfl⟩ : syracuseStep 918567 = 1377851) B1377851
theorem B1377359 : Blo 916578 1377359 := bstep (se 1 (by rfl) ⟨1033019, by rfl⟩ : syracuseStep 1377359 = 2066039) B2066039
theorem B918607 : Blo 916578 918607 := bstep (se 1 (by rfl) ⟨688955, by rfl⟩ : syracuseStep 918607 = 1377911) B1377911
theorem B918623 : Blo 916578 918623 := bstep (se 1 (by rfl) ⟨688967, by rfl⟩ : syracuseStep 918623 = 1377935) B1377935
theorem B918651 : Blo 916578 918651 := bstep (se 1 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 918651 = 1377977) B1377977
theorem B918703 : Blo 916578 918703 := bstep (se 1 (by rfl) ⟨689027, by rfl⟩ : syracuseStep 918703 = 1378055) B1378055
theorem B1377479 : Blo 916578 1377479 := bstep (se 1 (by rfl) ⟨1033109, by rfl⟩ : syracuseStep 1377479 = 2066219) B2066219
theorem B918727 : Blo 916578 918727 := bstep (se 1 (by rfl) ⟨689045, by rfl⟩ : syracuseStep 918727 = 1378091) B1378091
theorem B918747 : Blo 916578 918747 := bstep (se 1 (by rfl) ⟨689060, by rfl⟩ : syracuseStep 918747 = 1378121) B1378121
theorem B918823 : Blo 916578 918823 := bstep (se 1 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 918823 = 1378235) B1378235
theorem B918863 : Blo 916578 918863 := bstep (se 1 (by rfl) ⟨689147, by rfl⟩ : syracuseStep 918863 = 1378295) B1378295
theorem B918879 : Blo 916578 918879 := bstep (se 1 (by rfl) ⟨689159, by rfl⟩ : syracuseStep 918879 = 1378319) B1378319
theorem B2065769 : Blo 916578 2065769 := bstep (se 2 (by rfl) ⟨774663, by rfl⟩ : syracuseStep 2065769 = 1549327) B1549327
theorem B1377641 : Blo 916578 1377641 := bstep (se 2 (by rfl) ⟨516615, by rfl⟩ : syracuseStep 1377641 = 1033231) B1033231
theorem B918907 : Blo 916578 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B8390051 : Blo 916578 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B918959 : Blo 916578 918959 := bstep (se 1 (by rfl) ⟨689219, by rfl⟩ : syracuseStep 918959 = 1378439) B1378439
theorem B1377719 : Blo 916578 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B918983 : Blo 916578 918983 := bstep (se 1 (by rfl) ⟨689237, by rfl⟩ : syracuseStep 918983 = 1378475) B1378475
theorem B1377755 : Blo 916578 1377755 := bstep (se 1 (by rfl) ⟨1033316, by rfl⟩ : syracuseStep 1377755 = 2066633) B2066633
theorem B919003 : Blo 916578 919003 := bstep (se 1 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 919003 = 1378505) B1378505
theorem B919079 : Blo 916578 919079 := bstep (se 1 (by rfl) ⟨689309, by rfl⟩ : syracuseStep 919079 = 1378619) B1378619
theorem B919119 : Blo 916578 919119 := bstep (se 1 (by rfl) ⟨689339, by rfl⟩ : syracuseStep 919119 = 1378679) B1378679
theorem B919135 : Blo 916578 919135 := bstep (se 1 (by rfl) ⟨689351, by rfl⟩ : syracuseStep 919135 = 1378703) B1378703
theorem B919163 : Blo 916578 919163 := bstep (se 1 (by rfl) ⟨689372, by rfl⟩ : syracuseStep 919163 = 1378745) B1378745
theorem B2328203 : Blo 916578 2328203 := bstep (se 1 (by rfl) ⟨1746152, by rfl⟩ : syracuseStep 2328203 = 3492305) B3492305
theorem B919215 : Blo 916578 919215 := bstep (se 1 (by rfl) ⟨689411, by rfl⟩ : syracuseStep 919215 = 1378823) B1378823
theorem B7833287 : Blo 916578 7833287 := bstep (se 1 (by rfl) ⟨5874965, by rfl⟩ : syracuseStep 7833287 = 11749931) B11749931
theorem B919239 : Blo 916578 919239 := bstep (se 1 (by rfl) ⟨689429, by rfl⟩ : syracuseStep 919239 = 1378859) B1378859
theorem B919259 : Blo 916578 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B919335 : Blo 916578 919335 := bstep (se 1 (by rfl) ⟨689501, by rfl⟩ : syracuseStep 919335 = 1379003) B1379003
theorem B919375 : Blo 916578 919375 := bstep (se 1 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 919375 = 1379063) B1379063
theorem B919391 : Blo 916578 919391 := bstep (se 1 (by rfl) ⟨689543, by rfl⟩ : syracuseStep 919391 = 1379087) B1379087
theorem B3770219 : Blo 916578 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B12912493 : Blo 916578 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B919419 : Blo 916578 919419 := bstep (se 1 (by rfl) ⟨689564, by rfl⟩ : syracuseStep 919419 = 1379129) B1379129
theorem B1378223 : Blo 916578 1378223 := bstep (se 1 (by rfl) ⟨1033667, by rfl⟩ : syracuseStep 1378223 = 2067335) B2067335
theorem B919471 : Blo 916578 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B2066363 : Blo 916578 2066363 := bstep (se 1 (by rfl) ⟨1549772, by rfl⟩ : syracuseStep 2066363 = 3099545) B3099545
theorem B919495 : Blo 916578 919495 := bstep (se 1 (by rfl) ⟨689621, by rfl⟩ : syracuseStep 919495 = 1379243) B1379243
theorem B919515 : Blo 916578 919515 := bstep (se 1 (by rfl) ⟨689636, by rfl⟩ : syracuseStep 919515 = 1379273) B1379273
theorem B1378313 : Blo 916578 1378313 := bstep (se 2 (by rfl) ⟨516867, by rfl⟩ : syracuseStep 1378313 = 1033735) B1033735
theorem B1378343 : Blo 916578 1378343 := bstep (se 1 (by rfl) ⟨1033757, by rfl⟩ : syracuseStep 1378343 = 2067515) B2067515
theorem B919591 : Blo 916578 919591 := bstep (se 1 (by rfl) ⟨689693, by rfl⟩ : syracuseStep 919591 = 1379387) B1379387
theorem B2066489 : Blo 916578 2066489 := bstep (se 2 (by rfl) ⟨774933, by rfl⟩ : syracuseStep 2066489 = 1549867) B1549867
theorem B919631 : Blo 916578 919631 := bstep (se 1 (by rfl) ⟨689723, by rfl⟩ : syracuseStep 919631 = 1379447) B1379447
theorem B919647 : Blo 916578 919647 := bstep (se 1 (by rfl) ⟨689735, by rfl⟩ : syracuseStep 919647 = 1379471) B1379471
theorem B1378427 : Blo 916578 1378427 := bstep (se 1 (by rfl) ⟨1033820, by rfl⟩ : syracuseStep 1378427 = 2067641) B2067641
theorem B919675 : Blo 916578 919675 := bstep (se 1 (by rfl) ⟨689756, by rfl⟩ : syracuseStep 919675 = 1379513) B1379513
theorem B919727 : Blo 916578 919727 := bstep (se 1 (by rfl) ⟨689795, by rfl⟩ : syracuseStep 919727 = 1379591) B1379591
theorem B919751 : Blo 916578 919751 := bstep (se 1 (by rfl) ⟨689813, by rfl⟩ : syracuseStep 919751 = 1379627) B1379627
theorem B919771 : Blo 916578 919771 := bstep (se 1 (by rfl) ⟨689828, by rfl⟩ : syracuseStep 919771 = 1379657) B1379657
theorem B1378553 : Blo 916578 1378553 := bstep (se 2 (by rfl) ⟨516957, by rfl⟩ : syracuseStep 1378553 = 1033915) B1033915
theorem B919847 : Blo 916578 919847 := bstep (se 1 (by rfl) ⟨689885, by rfl⟩ : syracuseStep 919847 = 1379771) B1379771
theorem B919887 : Blo 916578 919887 := bstep (se 1 (by rfl) ⟨689915, by rfl⟩ : syracuseStep 919887 = 1379831) B1379831
theorem B1378655 : Blo 916578 1378655 := bstep (se 1 (by rfl) ⟨1033991, by rfl⟩ : syracuseStep 1378655 = 2067983) B2067983
theorem B919903 : Blo 916578 919903 := bstep (se 1 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 919903 = 1379855) B1379855
theorem B1378667 : Blo 916578 1378667 := bstep (se 1 (by rfl) ⟨1034000, by rfl⟩ : syracuseStep 1378667 = 2068001) B2068001
theorem B919931 : Blo 916578 919931 := bstep (se 1 (by rfl) ⟨689948, by rfl⟩ : syracuseStep 919931 = 1379897) B1379897
theorem B2066831 : Blo 916578 2066831 := bstep (se 1 (by rfl) ⟨1550123, by rfl⟩ : syracuseStep 2066831 = 3100247) B3100247
theorem B3541391 : Blo 916578 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B919983 : Blo 916578 919983 := bstep (se 1 (by rfl) ⟨689987, by rfl⟩ : syracuseStep 919983 = 1379975) B1379975
theorem B920007 : Blo 916578 920007 := bstep (se 1 (by rfl) ⟨690005, by rfl⟩ : syracuseStep 920007 = 1380011) B1380011
theorem B920027 : Blo 916578 920027 := bstep (se 1 (by rfl) ⟨690020, by rfl⟩ : syracuseStep 920027 = 1380041) B1380041
theorem B920103 : Blo 916578 920103 := bstep (se 1 (by rfl) ⟨690077, by rfl⟩ : syracuseStep 920103 = 1380155) B1380155
theorem B1378895 : Blo 916578 1378895 := bstep (se 1 (by rfl) ⟨1034171, by rfl⟩ : syracuseStep 1378895 = 2068343) B2068343
theorem B920143 : Blo 916578 920143 := bstep (se 1 (by rfl) ⟨690107, by rfl⟩ : syracuseStep 920143 = 1380215) B1380215
theorem B920159 : Blo 916578 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B920187 : Blo 916578 920187 := bstep (se 1 (by rfl) ⟨690140, by rfl⟩ : syracuseStep 920187 = 1380281) B1380281
theorem B920239 : Blo 916578 920239 := bstep (se 1 (by rfl) ⟨690179, by rfl⟩ : syracuseStep 920239 = 1380359) B1380359
theorem B1379015 : Blo 916578 1379015 := bstep (se 1 (by rfl) ⟨1034261, by rfl⟩ : syracuseStep 1379015 = 2068523) B2068523
theorem B920263 : Blo 916578 920263 := bstep (se 1 (by rfl) ⟨690197, by rfl⟩ : syracuseStep 920263 = 1380395) B1380395
theorem B2067155 : Blo 916578 2067155 := bstep (se 1 (by rfl) ⟨1550366, by rfl⟩ : syracuseStep 2067155 = 3100733) B3100733
theorem B920283 : Blo 916578 920283 := bstep (se 1 (by rfl) ⟨690212, by rfl⟩ : syracuseStep 920283 = 1380425) B1380425
theorem B2329337 : Blo 916578 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B920359 : Blo 916578 920359 := bstep (se 1 (by rfl) ⟨690269, by rfl⟩ : syracuseStep 920359 = 1380539) B1380539
theorem B920399 : Blo 916578 920399 := bstep (se 1 (by rfl) ⟨690299, by rfl⟩ : syracuseStep 920399 = 1380599) B1380599
theorem B920415 : Blo 916578 920415 := bstep (se 1 (by rfl) ⟨690311, by rfl⟩ : syracuseStep 920415 = 1380623) B1380623
theorem B1379177 : Blo 916578 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B920443 : Blo 916578 920443 := bstep (se 1 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 920443 = 1380665) B1380665
theorem B2329519 : Blo 916578 2329519 := bstep (se 1 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 2329519 = 3494279) B3494279
theorem B920495 : Blo 916578 920495 := bstep (se 1 (by rfl) ⟨690371, by rfl⟩ : syracuseStep 920495 = 1380743) B1380743
theorem B1379255 : Blo 916578 1379255 := bstep (se 1 (by rfl) ⟨1034441, by rfl⟩ : syracuseStep 1379255 = 2068883) B2068883
theorem B920519 : Blo 916578 920519 := bstep (se 1 (by rfl) ⟨690389, by rfl⟩ : syracuseStep 920519 = 1380779) B1380779
theorem B1379291 : Blo 916578 1379291 := bstep (se 1 (by rfl) ⟨1034468, by rfl⟩ : syracuseStep 1379291 = 2068937) B2068937
theorem B920539 : Blo 916578 920539 := bstep (se 1 (by rfl) ⟨690404, by rfl⟩ : syracuseStep 920539 = 1380809) B1380809
theorem B36211799 : Blo 916578 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B3149117 : Blo 916578 3149117 := bstep (se 3 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 3149117 = 1180919) B1180919
theorem B2329985 : Blo 916578 2329985 := bstep (se 2 (by rfl) ⟨873744, by rfl⟩ : syracuseStep 2329985 = 1747489) B1747489
theorem B4656527 : Blo 916578 4656527 := bstep (se 1 (by rfl) ⟨3492395, by rfl⟩ : syracuseStep 4656527 = 6984791) B6984791
theorem B22351277 : Blo 916578 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B1379759 : Blo 916578 1379759 := bstep (se 1 (by rfl) ⟨1034819, by rfl⟩ : syracuseStep 1379759 = 2069639) B2069639
theorem B1379849 : Blo 916578 1379849 := bstep (se 2 (by rfl) ⟨517443, by rfl⟩ : syracuseStep 1379849 = 1034887) B1034887
theorem B1379879 : Blo 916578 1379879 := bstep (se 1 (by rfl) ⟨1034909, by rfl⟩ : syracuseStep 1379879 = 2069819) B2069819
theorem B2068091 : Blo 916578 2068091 := bstep (se 1 (by rfl) ⟨1551068, by rfl⟩ : syracuseStep 2068091 = 3102137) B3102137
theorem B1379963 : Blo 916578 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B6295163 : Blo 916578 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B11767517 : Blo 916578 11767517 := bstep (se 3 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 11767517 = 4412819) B4412819
theorem B2068217 : Blo 916578 2068217 := bstep (se 2 (by rfl) ⟨775581, by rfl⟩ : syracuseStep 2068217 = 1551163) B1551163
theorem B1380089 : Blo 916578 1380089 := bstep (se 2 (by rfl) ⟨517533, by rfl⟩ : syracuseStep 1380089 = 1035067) B1035067
theorem B1380191 : Blo 916578 1380191 := bstep (se 1 (by rfl) ⟨1035143, by rfl⟩ : syracuseStep 1380191 = 2070287) B2070287
theorem B1380203 : Blo 916578 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B2068487 : Blo 916578 2068487 := bstep (se 1 (by rfl) ⟨1551365, by rfl⟩ : syracuseStep 2068487 = 3102731) B3102731
theorem B2068559 : Blo 916578 2068559 := bstep (se 1 (by rfl) ⟨1551419, by rfl⟩ : syracuseStep 2068559 = 3102839) B3102839
theorem B1380431 : Blo 916578 1380431 := bstep (se 1 (by rfl) ⟨1035323, by rfl⟩ : syracuseStep 1380431 = 2070647) B2070647
theorem B3969181 : Blo 916578 3969181 := bstep (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) B1488443
theorem B1380551 : Blo 916578 1380551 := bstep (se 1 (by rfl) ⟨1035413, by rfl⟩ : syracuseStep 1380551 = 2070827) B2070827
theorem B1380713 : Blo 916578 1380713 := bstep (se 2 (by rfl) ⟨517767, by rfl⟩ : syracuseStep 1380713 = 1035535) B1035535
theorem B1380791 : Blo 916578 1380791 := bstep (se 1 (by rfl) ⟨1035593, by rfl⟩ : syracuseStep 1380791 = 2071187) B2071187
theorem B2068955 : Blo 916578 2068955 := bstep (se 1 (by rfl) ⟨1551716, by rfl⟩ : syracuseStep 2068955 = 3103433) B3103433
theorem B1380827 : Blo 916578 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1741331 : Blo 916578 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B6296237 : Blo 916578 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B2069423 : Blo 916578 2069423 := bstep (se 1 (by rfl) ⟨1552067, by rfl⟩ : syracuseStep 2069423 = 3104135) B3104135
theorem B2790407 : Blo 916578 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B2069675 : Blo 916578 2069675 := bstep (se 1 (by rfl) ⟨1552256, by rfl⟩ : syracuseStep 2069675 = 3104513) B3104513
theorem B4658633 : Blo 916578 4658633 := bstep (se 2 (by rfl) ⟨1746987, by rfl⟩ : syracuseStep 4658633 = 3493975) B3493975
theorem B6985277 : Blo 916578 6985277 := bstep (se 3 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 6985277 = 2619479) B2619479
theorem B2070215 : Blo 916578 2070215 := bstep (se 1 (by rfl) ⟨1552661, by rfl⟩ : syracuseStep 2070215 = 3105323) B3105323
theorem B1742735 : Blo 916578 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B1742887 : Blo 916578 1742887 := bstep (se 1 (by rfl) ⟨1307165, by rfl⟩ : syracuseStep 1742887 = 2614331) B2614331
theorem B4659281 : Blo 916578 4659281 := bstep (se 2 (by rfl) ⟨1747230, by rfl⟩ : syracuseStep 4659281 = 3494461) B3494461
theorem B1742971 : Blo 916578 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B9410903 : Blo 916578 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B6986249 : Blo 916578 6986249 := bstep (se 2 (by rfl) ⟨2619843, by rfl⟩ : syracuseStep 6986249 = 5239687) B5239687
theorem B2071079 : Blo 916578 2071079 := bstep (se 1 (by rfl) ⟨1553309, by rfl⟩ : syracuseStep 2071079 = 3106619) B3106619
theorem B1743457 : Blo 916578 1743457 := bstep (se 2 (by rfl) ⟨653796, by rfl⟩ : syracuseStep 1743457 = 1307593) B1307593
theorem B1546951 : Blo 916578 1546951 := bstep (se 1 (by rfl) ⟨1160213, by rfl⟩ : syracuseStep 1546951 = 2320427) B2320427
theorem B1547113 : Blo 916578 1547113 := bstep (se 2 (by rfl) ⟨580167, by rfl⟩ : syracuseStep 1547113 = 1160335) B1160335
theorem B3316663 : Blo 916578 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B2202643 : Blo 916578 2202643 := bstep (se 1 (by rfl) ⟨1651982, by rfl⟩ : syracuseStep 2202643 = 3303965) B3303965
theorem B13245839 : Blo 916578 13245839 := bstep (se 1 (by rfl) ⟨9934379, by rfl⟩ : syracuseStep 13245839 = 19868759) B19868759
theorem B1547707 : Blo 916578 1547707 := bstep (se 1 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 1547707 = 2321561) B2321561
theorem B1744391 : Blo 916578 1744391 := bstep (se 1 (by rfl) ⟨1308293, by rfl⟩ : syracuseStep 1744391 = 2616587) B2616587
theorem B3481127 : Blo 916578 3481127 := bstep (se 1 (by rfl) ⟨2610845, by rfl⟩ : syracuseStep 3481127 = 5221691) B5221691
theorem B1547815 : Blo 916578 1547815 := bstep (se 1 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 1547815 = 2321723) B2321723
theorem B5971603 : Blo 916578 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B1548139 : Blo 916578 1548139 := bstep (se 1 (by rfl) ⟨1161104, by rfl⟩ : syracuseStep 1548139 = 2322209) B2322209
theorem B6987707 : Blo 916578 6987707 := bstep (se 1 (by rfl) ⟨5240780, by rfl⟩ : syracuseStep 6987707 = 10481561) B10481561
theorem B1744915 : Blo 916578 1744915 := bstep (se 1 (by rfl) ⟨1308686, by rfl⟩ : syracuseStep 1744915 = 2617373) B2617373
theorem B3482099 : Blo 916578 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B3482297 : Blo 916578 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B3482311 : Blo 916578 3482311 := bstep (se 1 (by rfl) ⟨2611733, by rfl⟩ : syracuseStep 3482311 = 5223467) B5223467
theorem B37692161 : Blo 916578 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B2204489 : Blo 916578 2204489 := bstep (se 2 (by rfl) ⟨826683, by rfl⟩ : syracuseStep 2204489 = 1653367) B1653367
theorem B1549199 : Blo 916578 1549199 := bstep (se 1 (by rfl) ⟨1161899, by rfl⟩ : syracuseStep 1549199 = 2323799) B2323799
theorem B1549435 : Blo 916578 1549435 := bstep (se 1 (by rfl) ⟨1162076, by rfl⟩ : syracuseStep 1549435 = 2324153) B2324153
theorem B5580427 : Blo 916578 5580427 := bstep (se 1 (by rfl) ⟨4185320, by rfl⟩ : syracuseStep 5580427 = 8370641) B8370641
theorem B6629003 : Blo 916578 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B3483283 : Blo 916578 3483283 := bstep (se 1 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 3483283 = 5224925) B5224925
theorem B5023583 : Blo 916578 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B3024827 : Blo 916578 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B1550299 : Blo 916578 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B6629465 : Blo 916578 6629465 := bstep (se 2 (by rfl) ⟨2486049, by rfl⟩ : syracuseStep 6629465 = 4972099) B4972099
theorem B1747307 : Blo 916578 1747307 := bstep (se 1 (by rfl) ⟨1310480, by rfl⟩ : syracuseStep 1747307 = 2620961) B2620961
theorem B2795905 : Blo 916578 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B1550927 : Blo 916578 1550927 := bstep (se 1 (by rfl) ⟨1163195, by rfl⟩ : syracuseStep 1550927 = 2326391) B2326391
theorem B2206727 : Blo 916578 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B3779641 : Blo 916578 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B3485015 : Blo 916578 3485015 := bstep (se 1 (by rfl) ⟨2613761, by rfl⟩ : syracuseStep 3485015 = 5227523) B5227523
theorem B1551791 : Blo 916578 1551791 := bstep (se 1 (by rfl) ⟨1163843, by rfl⟩ : syracuseStep 1551791 = 2327687) B2327687
theorem B1552223 : Blo 916578 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B7450555 : Blo 916578 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B4960271 : Blo 916578 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B25112591 : Blo 916578 25112591 := bstep (se 1 (by rfl) ⟨18834443, by rfl⟩ : syracuseStep 25112591 = 37668887) B37668887
theorem B5222717 : Blo 916578 5222717 := bstep (se 3 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 5222717 = 1958519) B1958519
theorem B8827211 : Blo 916578 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B1552783 : Blo 916578 1552783 := bstep (se 1 (by rfl) ⟨1164587, by rfl⟩ : syracuseStep 1552783 = 2329175) B2329175
theorem B4961027 : Blo 916578 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B1553465 : Blo 916578 1553465 := bstep (se 2 (by rfl) ⟨582549, by rfl⟩ : syracuseStep 1553465 = 1165099) B1165099
theorem B4961483 : Blo 916578 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B3093821 : Blo 916578 3093821 := bstep (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) B1160183
theorem B5223923 : Blo 916578 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B4404881 : Blo 916578 4404881 := bstep (se 2 (by rfl) ⟨1651830, by rfl⟩ : syracuseStep 4404881 = 3303661) B3303661
theorem B9058007 : Blo 916578 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B931547 : Blo 916578 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B3094685 : Blo 916578 3094685 := bstep (se 3 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 3094685 = 1160507) B1160507
theorem B3488129 : Blo 916578 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B3488143 : Blo 916578 3488143 := bstep (se 1 (by rfl) ⟨2616107, by rfl⟩ : syracuseStep 3488143 = 5232215) B5232215
theorem B1653257 : Blo 916578 1653257 := bstep (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) B1239943
theorem B3095225 : Blo 916578 3095225 := bstep (se 2 (by rfl) ⟨1160709, by rfl⟩ : syracuseStep 3095225 = 2321419) B2321419
theorem B6961949 : Blo 916578 6961949 := bstep (se 3 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 6961949 = 2610731) B2610731
theorem B1915913 : Blo 916578 1915913 := bstep (se 2 (by rfl) ⟨718467, by rfl⟩ : syracuseStep 1915913 = 1436935) B1436935
theorem B1162279 : Blo 916578 1162279 := bstep (se 1 (by rfl) ⟨871709, by rfl⟩ : syracuseStep 1162279 = 1743419) B1743419
theorem B3095819 : Blo 916578 3095819 := bstep (se 1 (by rfl) ⟨2321864, by rfl⟩ : syracuseStep 3095819 = 4643729) B4643729
theorem B14499107 : Blo 916578 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B1162603 : Blo 916578 1162603 := bstep (se 1 (by rfl) ⟨871952, by rfl⟩ : syracuseStep 1162603 = 1743905) B1743905
theorem B3915209 : Blo 916578 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B3096089 : Blo 916578 3096089 := bstep (se 2 (by rfl) ⟨1161033, by rfl⟩ : syracuseStep 3096089 = 2322067) B2322067
theorem B1031719 : Blo 916578 1031719 := bstep (se 1 (by rfl) ⟨773789, by rfl⟩ : syracuseStep 1031719 = 1547579) B1547579
theorem B1162831 : Blo 916578 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B3489419 : Blo 916578 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B11780275 : Blo 916578 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B5226839 : Blo 916578 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B10469897 : Blo 916578 10469897 := bstep (se 2 (by rfl) ⟨3926211, by rfl⟩ : syracuseStep 10469897 = 7852423) B7852423
theorem B1163899 : Blo 916578 1163899 := bstep (se 1 (by rfl) ⟨872924, by rfl⟩ : syracuseStep 1163899 = 1745849) B1745849
theorem B3097223 : Blo 916578 3097223 := bstep (se 1 (by rfl) ⟨2322917, by rfl⟩ : syracuseStep 3097223 = 4645835) B4645835
theorem B3097277 : Blo 916578 3097277 := bstep (se 3 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 3097277 = 1161479) B1161479
theorem B9945929 : Blo 916578 9945929 := bstep (se 2 (by rfl) ⟨3729723, by rfl⟩ : syracuseStep 9945929 = 7459447) B7459447
theorem B3097439 : Blo 916578 3097439 := bstep (se 1 (by rfl) ⟨2323079, by rfl⟩ : syracuseStep 3097439 = 4646159) B4646159
theorem B1164127 : Blo 916578 1164127 := bstep (se 1 (by rfl) ⟨873095, by rfl⟩ : syracuseStep 1164127 = 1746191) B1746191
theorem B3097601 : Blo 916578 3097601 := bstep (se 2 (by rfl) ⟨1161600, by rfl⟩ : syracuseStep 3097601 = 2323201) B2323201
theorem B1033339 : Blo 916578 1033339 := bstep (se 1 (by rfl) ⟨775004, by rfl⟩ : syracuseStep 1033339 = 1550009) B1550009
theorem B5293259 : Blo 916578 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B1656055 : Blo 916578 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1164719 : Blo 916578 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B12895733 : Blo 916578 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B3720737 : Blo 916578 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B1033807 : Blo 916578 1033807 := bstep (se 1 (by rfl) ⟨775355, by rfl⟩ : syracuseStep 1033807 = 1550711) B1550711
theorem B3098411 : Blo 916578 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B1034203 : Blo 916578 1034203 := bstep (se 1 (by rfl) ⟨775652, by rfl⟩ : syracuseStep 1034203 = 1551305) B1551305
theorem B3098681 : Blo 916578 3098681 := bstep (se 2 (by rfl) ⟨1162005, by rfl⟩ : syracuseStep 3098681 = 2324011) B2324011
theorem B3099005 : Blo 916578 3099005 := bstep (se 3 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 3099005 = 1162127) B1162127
theorem B1034671 : Blo 916578 1034671 := bstep (se 1 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 1034671 = 1552007) B1552007
theorem B5884397 : Blo 916578 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B7457305 : Blo 916578 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B3099275 : Blo 916578 3099275 := bstep (se 1 (by rfl) ⟨2324456, by rfl⟩ : syracuseStep 3099275 = 4648913) B4648913
theorem B2837207 : Blo 916578 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B26889029 : Blo 916578 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B1035103 : Blo 916578 1035103 := bstep (se 1 (by rfl) ⟨776327, by rfl⟩ : syracuseStep 1035103 = 1552655) B1552655
theorem B3492791 : Blo 916578 3492791 := bstep (se 1 (by rfl) ⟨2619593, by rfl⟩ : syracuseStep 3492791 = 5239187) B5239187
theorem B6966323 : Blo 916578 6966323 := bstep (se 1 (by rfl) ⟨5224742, by rfl⟩ : syracuseStep 6966323 = 10449485) B10449485
theorem B11455681 : Blo 916578 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B1035463 : Blo 916578 1035463 := bstep (se 1 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 1035463 = 1553195) B1553195
theorem B4410571 : Blo 916578 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B3100193 : Blo 916578 3100193 := bstep (se 2 (by rfl) ⟨1162572, by rfl⟩ : syracuseStep 3100193 = 2325145) B2325145
theorem B1658447 : Blo 916578 1658447 := bstep (se 1 (by rfl) ⟨1243835, by rfl⟩ : syracuseStep 1658447 = 2487671) B2487671
theorem B3919499 : Blo 916578 3919499 := bstep (se 1 (by rfl) ⟨2939624, by rfl⟩ : syracuseStep 3919499 = 5879249) B5879249
theorem B3919549 : Blo 916578 3919549 := bstep (se 3 (by rfl) ⟨734915, by rfl⟩ : syracuseStep 3919549 = 1469831) B1469831
theorem B3100409 : Blo 916578 3100409 := bstep (se 2 (by rfl) ⟨1162653, by rfl⟩ : syracuseStep 3100409 = 2325307) B2325307
theorem B3493793 : Blo 916578 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B3723191 : Blo 916578 3723191 := bstep (se 1 (by rfl) ⟨2792393, by rfl⟩ : syracuseStep 3723191 = 5584787) B5584787
theorem B4476865 : Blo 916578 4476865 := bstep (se 2 (by rfl) ⟨1678824, by rfl⟩ : syracuseStep 4476865 = 3357649) B3357649
theorem B3100679 : Blo 916578 3100679 := bstep (se 1 (by rfl) ⟨2325509, by rfl⟩ : syracuseStep 3100679 = 4651019) B4651019
theorem B3100787 : Blo 916578 3100787 := bstep (se 1 (by rfl) ⟨2325590, by rfl⟩ : syracuseStep 3100787 = 4651181) B4651181
theorem B3494249 : Blo 916578 3494249 := bstep (se 2 (by rfl) ⟨1310343, by rfl⟩ : syracuseStep 3494249 = 2620687) B2620687
theorem B3101057 : Blo 916578 3101057 := bstep (se 2 (by rfl) ⟨1162896, by rfl⟩ : syracuseStep 3101057 = 2325793) B2325793
theorem B9916951 : Blo 916578 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B4968985 : Blo 916578 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B3494765 : Blo 916578 3494765 := bstep (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) B1310537
theorem B28234649 : Blo 916578 28234649 := bstep (se 2 (by rfl) ⟨10587993, by rfl⟩ : syracuseStep 28234649 = 21175987) B21175987
theorem B4412569 : Blo 916578 4412569 := bstep (se 2 (by rfl) ⟨1654713, by rfl⟩ : syracuseStep 4412569 = 3309427) B3309427
theorem B3101867 : Blo 916578 3101867 := bstep (se 1 (by rfl) ⟨2326400, by rfl⟩ : syracuseStep 3101867 = 4652801) B4652801
theorem B16733387 : Blo 916578 16733387 := bstep (se 1 (by rfl) ⟨12550040, by rfl⟩ : syracuseStep 16733387 = 25100081) B25100081
theorem B6280715 : Blo 916578 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B3102407 : Blo 916578 3102407 := bstep (se 1 (by rfl) ⟨2326805, by rfl⟩ : syracuseStep 3102407 = 4653611) B4653611
theorem B145446731 : Blo 916578 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B1103911 : Blo 916578 1103911 := bstep (se 1 (by rfl) ⟨827933, by rfl⟩ : syracuseStep 1103911 = 1655867) B1655867
theorem B11917721 : Blo 916578 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2939431 : Blo 916578 2939431 := bstep (se 1 (by rfl) ⟨2204573, by rfl⟩ : syracuseStep 2939431 = 4409147) B4409147
theorem B3103271 : Blo 916578 3103271 := bstep (se 1 (by rfl) ⟨2327453, by rfl⟩ : syracuseStep 3103271 = 4654907) B4654907
theorem B3103379 : Blo 916578 3103379 := bstep (se 1 (by rfl) ⟨2327534, by rfl⟩ : syracuseStep 3103379 = 4655069) B4655069
theorem B5593859 : Blo 916578 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B3136363 : Blo 916578 3136363 := bstep (se 1 (by rfl) ⟨2352272, by rfl⟩ : syracuseStep 3136363 = 4704545) B4704545
theorem B3103595 : Blo 916578 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B3103649 : Blo 916578 3103649 := bstep (se 2 (by rfl) ⟨1163868, by rfl⟩ : syracuseStep 3103649 = 2327737) B2327737
theorem B4643891 : Blo 916578 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B5889523 : Blo 916578 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B3104243 : Blo 916578 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B5037767 : Blo 916578 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B3923873 : Blo 916578 3923873 := bstep (se 2 (by rfl) ⟨1471452, by rfl⟩ : syracuseStep 3923873 = 2942905) B2942905
theorem B3104783 : Blo 916578 3104783 := bstep (se 1 (by rfl) ⟨2328587, by rfl⟩ : syracuseStep 3104783 = 4657175) B4657175
theorem B8380493 : Blo 916578 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B2613647 : Blo 916578 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B1860175 : Blo 916578 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B3105377 : Blo 916578 3105377 := bstep (se 2 (by rfl) ⟨1164516, by rfl⟩ : syracuseStep 3105377 = 2329033) B2329033
theorem B4645511 : Blo 916578 4645511 := bstep (se 1 (by rfl) ⟨3484133, by rfl⟩ : syracuseStep 4645511 = 6968267) B6968267
theorem B2482903 : Blo 916578 2482903 := bstep (se 1 (by rfl) ⟨1862177, by rfl⟩ : syracuseStep 2482903 = 3724355) B3724355
theorem B7857071 : Blo 916578 7857071 := bstep (se 1 (by rfl) ⟨5892803, by rfl⟩ : syracuseStep 7857071 = 11785607) B11785607
theorem B6973127 : Blo 916578 6973127 := bstep (se 1 (by rfl) ⟨5229845, by rfl⟩ : syracuseStep 6973127 = 10459691) B10459691
theorem B10610527 : Blo 916578 10610527 := bstep (se 1 (by rfl) ⟨7957895, by rfl⟩ : syracuseStep 10610527 = 15915791) B15915791
theorem B4417375 : Blo 916578 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B2320235 : Blo 916578 2320235 := bstep (se 1 (by rfl) ⟨1740176, by rfl⟩ : syracuseStep 2320235 = 3480353) B3480353
theorem B5236589 : Blo 916578 5236589 := bstep (se 3 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 5236589 = 1963721) B1963721
theorem B3106835 : Blo 916578 3106835 := bstep (se 1 (by rfl) ⟨2330126, by rfl⟩ : syracuseStep 3106835 = 4660253) B4660253
theorem B4646969 : Blo 916578 4646969 := bstep (se 2 (by rfl) ⟨1742613, by rfl⟩ : syracuseStep 4646969 = 3485227) B3485227
theorem B9922661 : Blo 916578 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B3926333 : Blo 916578 3926333 := bstep (se 3 (by rfl) ⟨736187, by rfl⟩ : syracuseStep 3926333 = 1472375) B1472375
theorem B1239403 : Blo 916578 1239403 := bstep (se 1 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 1239403 = 1859105) B1859105
theorem B2320883 : Blo 916578 2320883 := bstep (se 1 (by rfl) ⟨1740662, by rfl⟩ : syracuseStep 2320883 = 3481325) B3481325
theorem B944815 : Blo 916578 944815 := bstep (se 1 (by rfl) ⟨708611, by rfl⟩ : syracuseStep 944815 = 1417223) B1417223
theorem B8809145 : Blo 916578 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B11168441 : Blo 916578 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B2321095 : Blo 916578 2321095 := bstep (se 1 (by rfl) ⟨1740821, by rfl⟩ : syracuseStep 2321095 = 3481643) B3481643
theorem B2943839 : Blo 916578 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B1764359 : Blo 916578 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B8842283 : Blo 916578 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B1469639 : Blo 916578 1469639 := bstep (se 1 (by rfl) ⟨1102229, by rfl⟩ : syracuseStep 1469639 = 2204459) B2204459
theorem B1567991 : Blo 916578 1567991 := bstep (se 1 (by rfl) ⟨1175993, by rfl⟩ : syracuseStep 1567991 = 2351987) B2351987
theorem B1469915 : Blo 916578 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B2322017 : Blo 916578 2322017 := bstep (se 2 (by rfl) ⟨870756, by rfl⟩ : syracuseStep 2322017 = 1741513) B1741513
theorem B28241531 : Blo 916578 28241531 := bstep (se 1 (by rfl) ⟨21181148, by rfl⟩ : syracuseStep 28241531 = 42362297) B42362297
theorem B4255355 : Blo 916578 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B11169413 : Blo 916578 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B1961671 : Blo 916578 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B4649075 : Blo 916578 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B3928331 : Blo 916578 3928331 := bstep (se 1 (by rfl) ⟨2946248, by rfl⟩ : syracuseStep 3928331 = 5892497) B5892497
theorem B1307063 : Blo 916578 1307063 := bstep (se 1 (by rfl) ⟨980297, by rfl⟩ : syracuseStep 1307063 = 1960595) B1960595
theorem B2618045 : Blo 916578 2618045 := bstep (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) B981767
theorem B5239505 : Blo 916578 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B1766137 : Blo 916578 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B11662231 : Blo 916578 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B2323475 : Blo 916578 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B5239961 : Blo 916578 5239961 := bstep (se 2 (by rfl) ⟨1964985, by rfl⟩ : syracuseStep 5239961 = 3929971) B3929971
theorem B1471817 : Blo 916578 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B1865033 : Blo 916578 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B12744029 : Blo 916578 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B29783537 : Blo 916578 29783537 := bstep (se 2 (by rfl) ⟨11168826, by rfl⟩ : syracuseStep 29783537 = 22337653) B22337653
theorem B4650695 : Blo 916578 4650695 := bstep (se 1 (by rfl) ⟨3488021, by rfl⟩ : syracuseStep 4650695 = 6976043) B6976043
theorem B1308521 : Blo 916578 1308521 := bstep (se 2 (by rfl) ⟨490695, by rfl⟩ : syracuseStep 1308521 = 981391) B981391
theorem B1865747 : Blo 916578 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B15693911 : Blo 916578 15693911 := bstep (se 1 (by rfl) ⟨11770433, by rfl⟩ : syracuseStep 15693911 = 23540867) B23540867
theorem B1472683 : Blo 916578 1472683 := bstep (se 1 (by rfl) ⟨1104512, by rfl⟩ : syracuseStep 1472683 = 2209025) B2209025
theorem B2062583 : Blo 916578 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B6289751 : Blo 916578 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B4913723 : Blo 916578 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B2063177 : Blo 916578 2063177 := bstep (se 2 (by rfl) ⟨773691, by rfl⟩ : syracuseStep 2063177 = 1547383) B1547383
theorem B1375151 : Blo 916578 1375151 := bstep (se 1 (by rfl) ⟨1031363, by rfl⟩ : syracuseStep 1375151 = 2062727) B2062727
theorem B63634355 : Blo 916578 63634355 := bstep (se 1 (by rfl) ⟨47725766, by rfl⟩ : syracuseStep 63634355 = 95451533) B95451533
theorem B1375241 : Blo 916578 1375241 := bstep (se 2 (by rfl) ⟨515715, by rfl⟩ : syracuseStep 1375241 = 1031431) B1031431
theorem B1375271 : Blo 916578 1375271 := bstep (se 1 (by rfl) ⟨1031453, by rfl⟩ : syracuseStep 1375271 = 2062907) B2062907
theorem B916603 : Blo 916578 916603 := bstep (se 1 (by rfl) ⟨687452, by rfl⟩ : syracuseStep 916603 = 1374905) B1374905
theorem B1375355 : Blo 916578 1375355 := bstep (se 1 (by rfl) ⟨1031516, by rfl⟩ : syracuseStep 1375355 = 2063033) B2063033
theorem B916655 : Blo 916578 916655 := bstep (se 1 (by rfl) ⟨687491, by rfl⟩ : syracuseStep 916655 = 1374983) B1374983
theorem B6618307 : Blo 916578 6618307 := bstep (se 1 (by rfl) ⟨4963730, by rfl⟩ : syracuseStep 6618307 = 9927461) B9927461
theorem B916679 : Blo 916578 916679 := bstep (se 1 (by rfl) ⟨687509, by rfl⟩ : syracuseStep 916679 = 1375019) B1375019
theorem B916699 : Blo 916578 916699 := bstep (se 1 (by rfl) ⟨687524, by rfl⟩ : syracuseStep 916699 = 1375049) B1375049
theorem B5242103 : Blo 916578 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B1375481 : Blo 916578 1375481 := bstep (se 2 (by rfl) ⟨515805, by rfl⟩ : syracuseStep 1375481 = 1031611) B1031611
theorem B1309945 : Blo 916578 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B916775 : Blo 916578 916775 := bstep (se 1 (by rfl) ⟨687581, by rfl⟩ : syracuseStep 916775 = 1375163) B1375163
theorem B916815 : Blo 916578 916815 := bstep (se 1 (by rfl) ⟨687611, by rfl⟩ : syracuseStep 916815 = 1375223) B1375223
theorem B916831 : Blo 916578 916831 := bstep (se 1 (by rfl) ⟨687623, by rfl⟩ : syracuseStep 916831 = 1375247) B1375247
theorem B1375583 : Blo 916578 1375583 := bstep (se 1 (by rfl) ⟨1031687, by rfl⟩ : syracuseStep 1375583 = 2063375) B2063375
theorem B1375595 : Blo 916578 1375595 := bstep (se 1 (by rfl) ⟨1031696, by rfl⟩ : syracuseStep 1375595 = 2063393) B2063393
theorem B916859 : Blo 916578 916859 := bstep (se 1 (by rfl) ⟨687644, by rfl⟩ : syracuseStep 916859 = 1375289) B1375289
theorem B6978959 : Blo 916578 6978959 := bstep (se 1 (by rfl) ⟨5234219, by rfl⟩ : syracuseStep 6978959 = 10468439) B10468439
theorem B916911 : Blo 916578 916911 := bstep (se 1 (by rfl) ⟨687683, by rfl⟩ : syracuseStep 916911 = 1375367) B1375367
theorem B916935 : Blo 916578 916935 := bstep (se 1 (by rfl) ⟨687701, by rfl⟩ : syracuseStep 916935 = 1375403) B1375403
theorem B916955 : Blo 916578 916955 := bstep (se 1 (by rfl) ⟨687716, by rfl⟩ : syracuseStep 916955 = 1375433) B1375433
theorem B1342985 : Blo 916578 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B2620937 : Blo 916578 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B917031 : Blo 916578 917031 := bstep (se 1 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 917031 = 1375547) B1375547
theorem B917071 : Blo 916578 917071 := bstep (se 1 (by rfl) ⟨687803, by rfl⟩ : syracuseStep 917071 = 1375607) B1375607
theorem B1375823 : Blo 916578 1375823 := bstep (se 1 (by rfl) ⟨1031867, by rfl⟩ : syracuseStep 1375823 = 2063735) B2063735
theorem B917087 : Blo 916578 917087 := bstep (se 1 (by rfl) ⟨687815, by rfl⟩ : syracuseStep 917087 = 1375631) B1375631
theorem B2063969 : Blo 916578 2063969 := bstep (se 2 (by rfl) ⟨773988, by rfl⟩ : syracuseStep 2063969 = 1547977) B1547977
theorem B917115 : Blo 916578 917115 := bstep (se 1 (by rfl) ⟨687836, by rfl⟩ : syracuseStep 917115 = 1375673) B1375673
theorem B917167 : Blo 916578 917167 := bstep (se 1 (by rfl) ⟨687875, by rfl⟩ : syracuseStep 917167 = 1375751) B1375751
theorem B917191 : Blo 916578 917191 := bstep (se 1 (by rfl) ⟨687893, by rfl⟩ : syracuseStep 917191 = 1375787) B1375787
theorem B1375943 : Blo 916578 1375943 := bstep (se 1 (by rfl) ⟨1031957, by rfl⟩ : syracuseStep 1375943 = 2063915) B2063915
theorem B917211 : Blo 916578 917211 := bstep (se 1 (by rfl) ⟨687908, by rfl⟩ : syracuseStep 917211 = 1375817) B1375817
theorem B917287 : Blo 916578 917287 := bstep (se 1 (by rfl) ⟨687965, by rfl⟩ : syracuseStep 917287 = 1375931) B1375931
theorem B917327 : Blo 916578 917327 := bstep (se 1 (by rfl) ⟨687995, by rfl⟩ : syracuseStep 917327 = 1375991) B1375991
theorem B917343 : Blo 916578 917343 := bstep (se 1 (by rfl) ⟨688007, by rfl⟩ : syracuseStep 917343 = 1376015) B1376015
theorem B1376105 : Blo 916578 1376105 := bstep (se 2 (by rfl) ⟨516039, by rfl⟩ : syracuseStep 1376105 = 1032079) B1032079
theorem B917371 : Blo 916578 917371 := bstep (se 1 (by rfl) ⟨688028, by rfl⟩ : syracuseStep 917371 = 1376057) B1376057
theorem B917423 : Blo 916578 917423 := bstep (se 1 (by rfl) ⟨688067, by rfl⟩ : syracuseStep 917423 = 1376135) B1376135
theorem B1376183 : Blo 916578 1376183 := bstep (se 1 (by rfl) ⟨1032137, by rfl⟩ : syracuseStep 1376183 = 2064275) B2064275
theorem B2064311 : Blo 916578 2064311 := bstep (se 1 (by rfl) ⟨1548233, by rfl⟩ : syracuseStep 2064311 = 3096467) B3096467
theorem B917447 : Blo 916578 917447 := bstep (se 1 (by rfl) ⟨688085, by rfl⟩ : syracuseStep 917447 = 1376171) B1376171
theorem B917467 : Blo 916578 917467 := bstep (se 1 (by rfl) ⟨688100, by rfl⟩ : syracuseStep 917467 = 1376201) B1376201
theorem B1376219 : Blo 916578 1376219 := bstep (se 1 (by rfl) ⟨1032164, by rfl⟩ : syracuseStep 1376219 = 2064329) B2064329
theorem B2326553 : Blo 916578 2326553 := bstep (se 2 (by rfl) ⟨872457, by rfl⟩ : syracuseStep 2326553 = 1744915) B1744915
theorem B917791 : Blo 916578 917791 := bstep (se 1 (by rfl) ⟨688343, by rfl⟩ : syracuseStep 917791 = 1376687) B1376687
theorem B1376603 : Blo 916578 1376603 := bstep (se 1 (by rfl) ⟨1032452, by rfl⟩ : syracuseStep 1376603 = 2064905) B2064905
theorem B917851 : Blo 916578 917851 := bstep (se 1 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 917851 = 1376777) B1376777
theorem B6979931 : Blo 916578 6979931 := bstep (se 1 (by rfl) ⟨5234948, by rfl⟩ : syracuseStep 6979931 = 10469897) B10469897
theorem B917871 : Blo 916578 917871 := bstep (se 1 (by rfl) ⟨688403, by rfl⟩ : syracuseStep 917871 = 1376807) B1376807
theorem B917927 : Blo 916578 917927 := bstep (se 1 (by rfl) ⟨688445, by rfl⟩ : syracuseStep 917927 = 1376891) B1376891
theorem B2064815 : Blo 916578 2064815 := bstep (se 1 (by rfl) ⟨1548611, by rfl⟩ : syracuseStep 2064815 = 3097223) B3097223
theorem B2064851 : Blo 916578 2064851 := bstep (se 1 (by rfl) ⟨1548638, by rfl⟩ : syracuseStep 2064851 = 3097277) B3097277
theorem B918011 : Blo 916578 918011 := bstep (se 1 (by rfl) ⟨688508, by rfl⟩ : syracuseStep 918011 = 1377017) B1377017
theorem B2064959 : Blo 916578 2064959 := bstep (se 1 (by rfl) ⟨1548719, by rfl⟩ : syracuseStep 2064959 = 3097439) B3097439
theorem B1376831 : Blo 916578 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B918079 : Blo 916578 918079 := bstep (se 1 (by rfl) ⟨688559, by rfl⟩ : syracuseStep 918079 = 1377119) B1377119
theorem B918087 : Blo 916578 918087 := bstep (se 1 (by rfl) ⟨688565, by rfl⟩ : syracuseStep 918087 = 1377131) B1377131
theorem B2065067 : Blo 916578 2065067 := bstep (se 1 (by rfl) ⟨1548800, by rfl⟩ : syracuseStep 2065067 = 3097601) B3097601
theorem B1376951 : Blo 916578 1376951 := bstep (se 1 (by rfl) ⟨1032713, by rfl⟩ : syracuseStep 1376951 = 2065427) B2065427
theorem B918239 : Blo 916578 918239 := bstep (se 1 (by rfl) ⟨688679, by rfl⟩ : syracuseStep 918239 = 1377359) B1377359
theorem B918319 : Blo 916578 918319 := bstep (se 1 (by rfl) ⟨688739, by rfl⟩ : syracuseStep 918319 = 1377479) B1377479
theorem B21168965 : Blo 916578 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B1377179 : Blo 916578 1377179 := bstep (se 1 (by rfl) ⟨1032884, by rfl⟩ : syracuseStep 1377179 = 2065769) B2065769
theorem B918427 : Blo 916578 918427 := bstep (se 1 (by rfl) ⟨688820, by rfl⟩ : syracuseStep 918427 = 1377641) B1377641
theorem B918479 : Blo 916578 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B918503 : Blo 916578 918503 := bstep (se 1 (by rfl) ⟨688877, by rfl⟩ : syracuseStep 918503 = 1377755) B1377755
theorem B2065607 : Blo 916578 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B918815 : Blo 916578 918815 := bstep (se 1 (by rfl) ⟨689111, by rfl⟩ : syracuseStep 918815 = 1378223) B1378223
theorem B1377575 : Blo 916578 1377575 := bstep (se 1 (by rfl) ⟨1033181, by rfl⟩ : syracuseStep 1377575 = 2066363) B2066363
theorem B918875 : Blo 916578 918875 := bstep (se 1 (by rfl) ⟨689156, by rfl⟩ : syracuseStep 918875 = 1378313) B1378313
theorem B918895 : Blo 916578 918895 := bstep (se 1 (by rfl) ⟨689171, by rfl⟩ : syracuseStep 918895 = 1378343) B1378343
theorem B2065787 : Blo 916578 2065787 := bstep (se 1 (by rfl) ⟨1549340, by rfl⟩ : syracuseStep 2065787 = 3098681) B3098681
theorem B1377659 : Blo 916578 1377659 := bstep (se 1 (by rfl) ⟨1033244, by rfl⟩ : syracuseStep 1377659 = 2066489) B2066489
theorem B918951 : Blo 916578 918951 := bstep (se 1 (by rfl) ⟨689213, by rfl⟩ : syracuseStep 918951 = 1378427) B1378427
theorem B2065913 : Blo 916578 2065913 := bstep (se 2 (by rfl) ⟨774717, by rfl⟩ : syracuseStep 2065913 = 1549435) B1549435
theorem B1377785 : Blo 916578 1377785 := bstep (se 2 (by rfl) ⟨516669, by rfl⟩ : syracuseStep 1377785 = 1033339) B1033339
theorem B919035 : Blo 916578 919035 := bstep (se 1 (by rfl) ⟨689276, by rfl⟩ : syracuseStep 919035 = 1378553) B1378553
theorem B919103 : Blo 916578 919103 := bstep (se 1 (by rfl) ⟨689327, by rfl⟩ : syracuseStep 919103 = 1378655) B1378655
theorem B919111 : Blo 916578 919111 := bstep (se 1 (by rfl) ⟨689333, by rfl⟩ : syracuseStep 919111 = 1378667) B1378667
theorem B2066003 : Blo 916578 2066003 := bstep (se 1 (by rfl) ⟨1549502, by rfl⟩ : syracuseStep 2066003 = 3099005) B3099005
theorem B1377887 : Blo 916578 1377887 := bstep (se 1 (by rfl) ⟨1033415, by rfl⟩ : syracuseStep 1377887 = 2066831) B2066831
theorem B2360927 : Blo 916578 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B919263 : Blo 916578 919263 := bstep (se 1 (by rfl) ⟨689447, by rfl⟩ : syracuseStep 919263 = 1378895) B1378895
theorem B2066183 : Blo 916578 2066183 := bstep (se 1 (by rfl) ⟨1549637, by rfl⟩ : syracuseStep 2066183 = 3099275) B3099275
theorem B919343 : Blo 916578 919343 := bstep (se 1 (by rfl) ⟨689507, by rfl⟩ : syracuseStep 919343 = 1379015) B1379015
theorem B1378103 : Blo 916578 1378103 := bstep (se 1 (by rfl) ⟨1033577, by rfl⟩ : syracuseStep 1378103 = 2067155) B2067155
theorem B17926019 : Blo 916578 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B919451 : Blo 916578 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B919503 : Blo 916578 919503 := bstep (se 1 (by rfl) ⟨689627, by rfl⟩ : syracuseStep 919503 = 1379255) B1379255
theorem B2328527 : Blo 916578 2328527 := bstep (se 1 (by rfl) ⟨1746395, by rfl⟩ : syracuseStep 2328527 = 3492791) B3492791
theorem B919527 : Blo 916578 919527 := bstep (se 1 (by rfl) ⟨689645, by rfl⟩ : syracuseStep 919527 = 1379291) B1379291
theorem B1378409 : Blo 916578 1378409 := bstep (se 2 (by rfl) ⟨516903, by rfl⟩ : syracuseStep 1378409 = 1033807) B1033807
theorem B7440569 : Blo 916578 7440569 := bstep (se 2 (by rfl) ⟨2790213, by rfl⟩ : syracuseStep 7440569 = 5580427) B5580427
theorem B2099411 : Blo 916578 2099411 := bstep (se 1 (by rfl) ⟨1574558, by rfl⟩ : syracuseStep 2099411 = 3149117) B3149117
theorem B919839 : Blo 916578 919839 := bstep (se 1 (by rfl) ⟨689879, by rfl⟩ : syracuseStep 919839 = 1379759) B1379759
theorem B919899 : Blo 916578 919899 := bstep (se 1 (by rfl) ⟨689924, by rfl⟩ : syracuseStep 919899 = 1379849) B1379849
theorem B2066795 : Blo 916578 2066795 := bstep (se 1 (by rfl) ⟨1550096, by rfl⟩ : syracuseStep 2066795 = 3100193) B3100193
theorem B919919 : Blo 916578 919919 := bstep (se 1 (by rfl) ⟨689939, by rfl⟩ : syracuseStep 919919 = 1379879) B1379879
theorem B1378727 : Blo 916578 1378727 := bstep (se 1 (by rfl) ⟨1034045, by rfl⟩ : syracuseStep 1378727 = 2068091) B2068091
theorem B919975 : Blo 916578 919975 := bstep (se 1 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 919975 = 1379963) B1379963
theorem B2066939 : Blo 916578 2066939 := bstep (se 1 (by rfl) ⟨1550204, by rfl⟩ : syracuseStep 2066939 = 3100409) B3100409
theorem B1378811 : Blo 916578 1378811 := bstep (se 1 (by rfl) ⟨1034108, by rfl⟩ : syracuseStep 1378811 = 2068217) B2068217
theorem B920059 : Blo 916578 920059 := bstep (se 1 (by rfl) ⟨690044, by rfl⟩ : syracuseStep 920059 = 1380089) B1380089
theorem B920127 : Blo 916578 920127 := bstep (se 1 (by rfl) ⟨690095, by rfl⟩ : syracuseStep 920127 = 1380191) B1380191
theorem B920135 : Blo 916578 920135 := bstep (se 1 (by rfl) ⟨690101, by rfl⟩ : syracuseStep 920135 = 1380203) B1380203
theorem B2329195 : Blo 916578 2329195 := bstep (se 1 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 2329195 = 3493793) B3493793
theorem B2067065 : Blo 916578 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B1378937 : Blo 916578 1378937 := bstep (se 2 (by rfl) ⟨517101, by rfl⟩ : syracuseStep 1378937 = 1034203) B1034203
theorem B2067119 : Blo 916578 2067119 := bstep (se 1 (by rfl) ⟨1550339, by rfl⟩ : syracuseStep 2067119 = 3100679) B3100679
theorem B1378991 : Blo 916578 1378991 := bstep (se 1 (by rfl) ⟨1034243, by rfl⟩ : syracuseStep 1378991 = 2068487) B2068487
theorem B7441085 : Blo 916578 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B1379039 : Blo 916578 1379039 := bstep (se 1 (by rfl) ⟨1034279, by rfl⟩ : syracuseStep 1379039 = 2068559) B2068559
theorem B920287 : Blo 916578 920287 := bstep (se 1 (by rfl) ⟨690215, by rfl⟩ : syracuseStep 920287 = 1380431) B1380431
theorem B2067191 : Blo 916578 2067191 := bstep (se 1 (by rfl) ⟨1550393, by rfl⟩ : syracuseStep 2067191 = 3100787) B3100787
theorem B920367 : Blo 916578 920367 := bstep (se 1 (by rfl) ⟨690275, by rfl⟩ : syracuseStep 920367 = 1380551) B1380551
theorem B2329499 : Blo 916578 2329499 := bstep (se 1 (by rfl) ⟨1747124, by rfl⟩ : syracuseStep 2329499 = 3494249) B3494249
theorem B920475 : Blo 916578 920475 := bstep (se 1 (by rfl) ⟨690356, by rfl⟩ : syracuseStep 920475 = 1380713) B1380713
theorem B2067371 : Blo 916578 2067371 := bstep (se 1 (by rfl) ⟨1550528, by rfl⟩ : syracuseStep 2067371 = 3101057) B3101057
theorem B920527 : Blo 916578 920527 := bstep (se 1 (by rfl) ⟨690395, by rfl⟩ : syracuseStep 920527 = 1380791) B1380791
theorem B1379303 : Blo 916578 1379303 := bstep (se 1 (by rfl) ⟨1034477, by rfl⟩ : syracuseStep 1379303 = 2068955) B2068955
theorem B920551 : Blo 916578 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B4197491 : Blo 916578 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B1379561 : Blo 916578 1379561 := bstep (se 2 (by rfl) ⟨517335, by rfl⟩ : syracuseStep 1379561 = 1034671) B1034671
theorem B2329843 : Blo 916578 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B1379615 : Blo 916578 1379615 := bstep (se 1 (by rfl) ⟨1034711, by rfl⟩ : syracuseStep 1379615 = 2069423) B2069423
theorem B2067911 : Blo 916578 2067911 := bstep (se 1 (by rfl) ⟨1550933, by rfl⟩ : syracuseStep 2067911 = 3101867) B3101867
theorem B1379783 : Blo 916578 1379783 := bstep (se 1 (by rfl) ⟨1034837, by rfl⟩ : syracuseStep 1379783 = 2069675) B2069675
theorem B4656851 : Blo 916578 4656851 := bstep (se 1 (by rfl) ⟨3492638, by rfl⟩ : syracuseStep 4656851 = 6985277) B6985277
theorem B13242149 : Blo 916578 13242149 := bstep (se 4 (by rfl) ⟨1241451, by rfl⟩ : syracuseStep 13242149 = 2482903) B2482903
theorem B1380137 : Blo 916578 1380137 := bstep (se 2 (by rfl) ⟨517551, by rfl⟩ : syracuseStep 1380137 = 1035103) B1035103
theorem B2068271 : Blo 916578 2068271 := bstep (se 1 (by rfl) ⟨1551203, by rfl⟩ : syracuseStep 2068271 = 3102407) B3102407
theorem B1380143 : Blo 916578 1380143 := bstep (se 1 (by rfl) ⟨1035107, by rfl⟩ : syracuseStep 1380143 = 2070215) B2070215
theorem B96964487 : Blo 916578 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B15274241 : Blo 916578 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B1380617 : Blo 916578 1380617 := bstep (se 2 (by rfl) ⟨517731, by rfl⟩ : syracuseStep 1380617 = 1035463) B1035463
theorem B4657499 : Blo 916578 4657499 := bstep (se 1 (by rfl) ⟨3493124, by rfl⟩ : syracuseStep 4657499 = 6986249) B6986249
theorem B2068847 : Blo 916578 2068847 := bstep (se 1 (by rfl) ⟨1551635, by rfl⟩ : syracuseStep 2068847 = 3103271) B3103271
theorem B1380719 : Blo 916578 1380719 := bstep (se 1 (by rfl) ⟨1035539, by rfl⟩ : syracuseStep 1380719 = 2071079) B2071079
theorem B2068919 : Blo 916578 2068919 := bstep (se 1 (by rfl) ⟨1551689, by rfl⟩ : syracuseStep 2068919 = 3103379) B3103379
theorem B24154685 : Blo 916578 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B2069063 : Blo 916578 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B2069099 : Blo 916578 2069099 := bstep (se 1 (by rfl) ⟨1551824, by rfl⟩ : syracuseStep 2069099 = 3103649) B3103649
theorem B2069495 : Blo 916578 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B9934073 : Blo 916578 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B5969153 : Blo 916578 5969153 := bstep (se 2 (by rfl) ⟨2238432, by rfl⟩ : syracuseStep 5969153 = 4476865) B4476865
theorem B4658471 : Blo 916578 4658471 := bstep (se 1 (by rfl) ⟨3493853, by rfl⟩ : syracuseStep 4658471 = 6987707) B6987707
theorem B2069855 : Blo 916578 2069855 := bstep (se 1 (by rfl) ⟨1552391, by rfl⟩ : syracuseStep 2069855 = 3104783) B3104783
theorem B20158085 : Blo 916578 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B2070251 : Blo 916578 2070251 := bstep (se 1 (by rfl) ⟨1552688, by rfl⟩ : syracuseStep 2070251 = 3105377) B3105377
theorem B2070377 : Blo 916578 2070377 := bstep (se 2 (by rfl) ⟨776391, by rfl⟩ : syracuseStep 2070377 = 1552783) B1552783
theorem B6625313 : Blo 916578 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B3349055 : Blo 916578 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B1546823 : Blo 916578 1546823 := bstep (se 1 (by rfl) ⟨1160117, by rfl⟩ : syracuseStep 1546823 = 2320235) B2320235
theorem B2071223 : Blo 916578 2071223 := bstep (se 1 (by rfl) ⟨1553417, by rfl⟩ : syracuseStep 2071223 = 3106835) B3106835
theorem B1547255 : Blo 916578 1547255 := bstep (se 1 (by rfl) ⟨1160441, by rfl⟩ : syracuseStep 1547255 = 2320883) B2320883
theorem B5872763 : Blo 916578 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B7445627 : Blo 916578 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B1548011 : Blo 916578 1548011 := bstep (se 1 (by rfl) ⟨1161008, by rfl⟩ : syracuseStep 1548011 = 2322017) B2322017
theorem B7446275 : Blo 916578 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B3481811 : Blo 916578 3481811 := bstep (se 1 (by rfl) ⟨2611358, by rfl⟩ : syracuseStep 3481811 = 5222717) B5222717
theorem B1745363 : Blo 916578 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B1548983 : Blo 916578 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B8496019 : Blo 916578 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B3482615 : Blo 916578 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B3581293 : Blo 916578 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B6989165 : Blo 916578 6989165 := bstep (se 3 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 6989165 = 2620937) B2620937
theorem B1549705 : Blo 916578 1549705 := bstep (se 2 (by rfl) ⟨581139, by rfl⟩ : syracuseStep 1549705 = 1162279) B1162279
theorem B10462607 : Blo 916578 10462607 := bstep (se 1 (by rfl) ⟨7846955, by rfl⟩ : syracuseStep 10462607 = 15693911) B15693911
theorem B8824409 : Blo 916578 8824409 := bstep (se 2 (by rfl) ⟨3309153, by rfl⟩ : syracuseStep 8824409 = 6618307) B6618307
theorem B16787101 : Blo 916578 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B11347613 : Blo 916578 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B1746593 : Blo 916578 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B1550137 : Blo 916578 1550137 := bstep (se 2 (by rfl) ⟨581301, by rfl⟩ : syracuseStep 1550137 = 1162603) B1162603
theorem B1550441 : Blo 916578 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B3484559 : Blo 916578 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B15707033 : Blo 916578 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B2206919 : Blo 916578 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B5024987 : Blo 916578 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B6630619 : Blo 916578 6630619 := bstep (se 1 (by rfl) ⟨4972964, by rfl⟩ : syracuseStep 6630619 = 9945929) B9945929
theorem B1551865 : Blo 916578 1551865 := bstep (se 2 (by rfl) ⟨581949, by rfl⟩ : syracuseStep 1551865 = 1163899) B1163899
theorem B1552135 : Blo 916578 1552135 := bstep (se 1 (by rfl) ⟨1164101, by rfl⟩ : syracuseStep 1552135 = 2328203) B2328203
theorem B1552169 : Blo 916578 1552169 := bstep (se 2 (by rfl) ⟨582063, by rfl⟩ : syracuseStep 1552169 = 1164127) B1164127
theorem B5222191 : Blo 916578 5222191 := bstep (se 1 (by rfl) ⟨3916643, by rfl⟩ : syracuseStep 5222191 = 7833287) B7833287
theorem B3485501 : Blo 916578 3485501 := bstep (se 3 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 3485501 = 1307063) B1307063
theorem B2208073 : Blo 916578 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B1552891 : Blo 916578 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B1553323 : Blo 916578 1553323 := bstep (se 1 (by rfl) ⟨1164992, by rfl⟩ : syracuseStep 1553323 = 2329985) B2329985
theorem B17216657 : Blo 916578 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B7845011 : Blo 916578 7845011 := bstep (se 1 (by rfl) ⟨5883758, by rfl⟩ : syracuseStep 7845011 = 11767517) B11767517
theorem B1160887 : Blo 916578 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B1652537 : Blo 916578 1652537 := bstep (se 2 (by rfl) ⟨619701, by rfl⟩ : syracuseStep 1652537 = 1239403) B1239403
theorem B18823099 : Blo 916578 18823099 := bstep (se 1 (by rfl) ⟨14117324, by rfl⟩ : syracuseStep 18823099 = 28234649) B28234649
theorem B9943073 : Blo 916578 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B11155591 : Blo 916578 11155591 := bstep (se 1 (by rfl) ⟨8366693, by rfl⟩ : syracuseStep 11155591 = 16733387) B16733387
theorem B1259753 : Blo 916578 1259753 := bstep (se 2 (by rfl) ⟨472407, by rfl⟩ : syracuseStep 1259753 = 944815) B944815
theorem B3094793 : Blo 916578 3094793 := bstep (se 2 (by rfl) ⟨1160547, by rfl⟩ : syracuseStep 3094793 = 2321095) B2321095
theorem B34388621 : Blo 916578 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B6273935 : Blo 916578 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B5880761 : Blo 916578 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B7945147 : Blo 916578 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B16727269 : Blo 916578 16727269 := bstep (se 4 (by rfl) ⟨1568181, by rfl⟩ : syracuseStep 16727269 = 3136363) B3136363
theorem B3095927 : Blo 916578 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B5226065 : Blo 916578 5226065 := bstep (se 2 (by rfl) ⟨1959774, by rfl⟩ : syracuseStep 5226065 = 3919549) B3919549
theorem B8830559 : Blo 916578 8830559 := bstep (se 1 (by rfl) ⟨6622919, by rfl⟩ : syracuseStep 8830559 = 13245839) B13245839
theorem B3489389 : Blo 916578 3489389 := bstep (se 3 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 3489389 = 1308521) B1308521
theorem B1162927 : Blo 916578 1162927 := bstep (se 1 (by rfl) ⟨872195, by rfl⟩ : syracuseStep 1162927 = 1744391) B1744391
theorem B3358511 : Blo 916578 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B5586995 : Blo 916578 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B3097007 : Blo 916578 3097007 := bstep (se 1 (by rfl) ⟨2322755, by rfl⟩ : syracuseStep 3097007 = 4645511) B4645511
theorem B1032799 : Blo 916578 1032799 := bstep (se 1 (by rfl) ⟨774599, by rfl⟩ : syracuseStep 1032799 = 1549199) B1549199
theorem B13222601 : Blo 916578 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B15549641 : Blo 916578 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B3491059 : Blo 916578 3491059 := bstep (se 1 (by rfl) ⟨2618294, by rfl⟩ : syracuseStep 3491059 = 5236589) B5236589
theorem B2016551 : Blo 916578 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B4408685 : Blo 916578 4408685 := bstep (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) B1653257
theorem B3097979 : Blo 916578 3097979 := bstep (se 1 (by rfl) ⟨2323484, by rfl⟩ : syracuseStep 3097979 = 4646969) B4646969
theorem B5883425 : Blo 916578 5883425 := bstep (se 2 (by rfl) ⟨2206284, by rfl⟩ : syracuseStep 5883425 = 4412569) B4412569
theorem B1164871 : Blo 916578 1164871 := bstep (se 1 (by rfl) ⟨873653, by rfl⟩ : syracuseStep 1164871 = 1747307) B1747307
theorem B1033951 : Blo 916578 1033951 := bstep (se 1 (by rfl) ⟨775463, by rfl⟩ : syracuseStep 1033951 = 1550927) B1550927
theorem B1034527 : Blo 916578 1034527 := bstep (se 1 (by rfl) ⟨775895, by rfl⟩ : syracuseStep 1034527 = 1551791) B1551791
theorem B18827687 : Blo 916578 18827687 := bstep (se 1 (by rfl) ⟨14120765, by rfl⟩ : syracuseStep 18827687 = 28241531) B28241531
theorem B1034815 : Blo 916578 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B3099383 : Blo 916578 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B5884807 : Blo 916578 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B3493003 : Blo 916578 3493003 := bstep (se 1 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 3493003 = 5239505) B5239505
theorem B1035643 : Blo 916578 1035643 := bstep (se 1 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 1035643 = 1553465) B1553465
theorem B3919241 : Blo 916578 3919241 := bstep (se 2 (by rfl) ⟨1469715, by rfl⟩ : syracuseStep 3919241 = 2939431) B2939431
theorem B3493307 : Blo 916578 3493307 := bstep (se 1 (by rfl) ⟨2619980, by rfl⟩ : syracuseStep 3493307 = 5239961) B5239961
theorem B2936587 : Blo 916578 2936587 := bstep (se 1 (by rfl) ⟨2202440, by rfl⟩ : syracuseStep 2936587 = 4404881) B4404881
theorem B3100463 : Blo 916578 3100463 := bstep (se 1 (by rfl) ⟨2325347, by rfl⟩ : syracuseStep 3100463 = 4650695) B4650695
theorem B2936857 : Blo 916578 2936857 := bstep (se 2 (by rfl) ⟨1101321, by rfl⟩ : syracuseStep 2936857 = 2202643) B2202643
theorem B4641299 : Blo 916578 4641299 := bstep (se 1 (by rfl) ⟨3480974, by rfl⟩ : syracuseStep 4641299 = 6961949) B6961949
theorem B42422903 : Blo 916578 42422903 := bstep (se 1 (by rfl) ⟨31817177, by rfl⟩ : syracuseStep 42422903 = 63634355) B63634355
theorem B7852697 : Blo 916578 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B3494735 : Blo 916578 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B2610139 : Blo 916578 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B7558505 : Blo 916578 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B5887525 : Blo 916578 5887525 := bstep (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) B1103911
theorem B15685163 : Blo 916578 15685163 := bstep (se 1 (by rfl) ⟨11763872, by rfl⟩ : syracuseStep 15685163 = 23527745) B23527745
theorem B3102569 : Blo 916578 3102569 := bstep (se 2 (by rfl) ⟨1163463, by rfl⟩ : syracuseStep 3102569 = 2326927) B2326927
theorem B2480233 : Blo 916578 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B3528839 : Blo 916578 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B4643081 : Blo 916578 4643081 := bstep (se 2 (by rfl) ⟨1741155, by rfl⟩ : syracuseStep 4643081 = 3482311) B3482311
theorem B5593367 : Blo 916578 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B3103001 : Blo 916578 3103001 := bstep (se 2 (by rfl) ⟨1163625, by rfl⟩ : syracuseStep 3103001 = 2327251) B2327251
theorem B2480491 : Blo 916578 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B6969725 : Blo 916578 6969725 := bstep (se 3 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 6969725 = 2613647) B2613647
theorem B2513479 : Blo 916578 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B3922931 : Blo 916578 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B13229405 : Blo 916578 13229405 := bstep (se 3 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 13229405 = 4961027) B4961027
theorem B4644215 : Blo 916578 4644215 := bstep (se 1 (by rfl) ⟨3483161, by rfl⟩ : syracuseStep 4644215 = 6966323) B6966323
theorem B24141199 : Blo 916578 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B4644377 : Blo 916578 4644377 := bstep (se 2 (by rfl) ⟨1741641, by rfl⟩ : syracuseStep 4644377 = 3483283) B3483283
theorem B3104351 : Blo 916578 3104351 := bstep (se 1 (by rfl) ⟨2328263, by rfl⟩ : syracuseStep 3104351 = 4656527) B4656527
theorem B14900851 : Blo 916578 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B1105631 : Blo 916578 1105631 := bstep (se 1 (by rfl) ⟨829223, by rfl⟩ : syracuseStep 1105631 = 1658447) B1658447
theorem B2612999 : Blo 916578 2612999 := bstep (se 1 (by rfl) ⟨1959749, by rfl⟩ : syracuseStep 2612999 = 3919499) B3919499
theorem B5889833 : Blo 916578 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B14147369 : Blo 916578 14147369 := bstep (se 2 (by rfl) ⟨5305263, by rfl⟩ : syracuseStep 14147369 = 10610527) B10610527
theorem B2482127 : Blo 916578 2482127 := bstep (se 1 (by rfl) ⟨1861595, by rfl⟩ : syracuseStep 2482127 = 3723191) B3723191
theorem B3727873 : Blo 916578 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B3924845 : Blo 916578 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B3105755 : Blo 916578 3105755 := bstep (se 1 (by rfl) ⟨2329316, by rfl⟩ : syracuseStep 3105755 = 4658633) B4658633
theorem B4187143 : Blo 916578 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B3105917 : Blo 916578 3105917 := bstep (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) B1164719
theorem B3106025 : Blo 916578 3106025 := bstep (se 2 (by rfl) ⟨1164759, by rfl⟩ : syracuseStep 3106025 = 2329519) B2329519
theorem B3106187 : Blo 916578 3106187 := bstep (se 1 (by rfl) ⟨2329640, by rfl⟩ : syracuseStep 3106187 = 4659281) B4659281
theorem B3729239 : Blo 916578 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B2484125 : Blo 916578 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B2615561 : Blo 916578 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B2320751 : Blo 916578 2320751 := bstep (se 1 (by rfl) ⟨1740563, by rfl⟩ : syracuseStep 2320751 = 3481127) B3481127
theorem B4647293 : Blo 916578 4647293 := bstep (se 3 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 4647293 = 1742735) B1742735
theorem B2615915 : Blo 916578 2615915 := bstep (se 1 (by rfl) ⟨1961936, by rfl⟩ : syracuseStep 2615915 = 3923873) B3923873
theorem B2321399 : Blo 916578 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B2321531 : Blo 916578 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B25128107 : Blo 916578 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B1469659 : Blo 916578 1469659 := bstep (se 1 (by rfl) ⟨1102244, by rfl⟩ : syracuseStep 1469659 = 2204489) B2204489
theorem B5238047 : Blo 916578 5238047 := bstep (se 1 (by rfl) ⟨3928535, by rfl⟩ : syracuseStep 5238047 = 7857071) B7857071
theorem B2354849 : Blo 916578 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B4419335 : Blo 916578 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B4648751 : Blo 916578 4648751 := bstep (se 1 (by rfl) ⟨3486563, by rfl⟩ : syracuseStep 4648751 = 6973127) B6973127
theorem B4419643 : Blo 916578 4419643 := bstep (se 1 (by rfl) ⟨3314732, by rfl⟩ : syracuseStep 4419643 = 6629465) B6629465
theorem B6615107 : Blo 916578 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B2617555 : Blo 916578 2617555 := bstep (se 1 (by rfl) ⟨1963166, by rfl⟩ : syracuseStep 2617555 = 3926333) B3926333
theorem B7565885 : Blo 916578 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1962559 : Blo 916578 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B1176239 : Blo 916578 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B1471151 : Blo 916578 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B5894855 : Blo 916578 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B979759 : Blo 916578 979759 := bstep (se 1 (by rfl) ⟨734819, by rfl⟩ : syracuseStep 979759 = 1469639) B1469639
theorem B1045327 : Blo 916578 1045327 := bstep (se 1 (by rfl) ⟨783995, by rfl⟩ : syracuseStep 1045327 = 1567991) B1567991
theorem B2323343 : Blo 916578 2323343 := bstep (se 1 (by rfl) ⟨1742507, by rfl⟩ : syracuseStep 2323343 = 3485015) B3485015
theorem B979943 : Blo 916578 979943 := bstep (se 1 (by rfl) ⟨734957, by rfl⟩ : syracuseStep 979943 = 1469915) B1469915
theorem B3306847 : Blo 916578 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B16741727 : Blo 916578 16741727 := bstep (se 1 (by rfl) ⟨12556295, by rfl⟩ : syracuseStep 16741727 = 25112591) B25112591
theorem B2323849 : Blo 916578 2323849 := bstep (se 2 (by rfl) ⟨871443, by rfl⟩ : syracuseStep 2323849 = 1742887) B1742887
theorem B2323961 : Blo 916578 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B2618887 : Blo 916578 2618887 := bstep (se 1 (by rfl) ⟨1964165, by rfl⟩ : syracuseStep 2618887 = 3928331) B3928331
theorem B1963577 : Blo 916578 1963577 := bstep (se 2 (by rfl) ⟨736341, by rfl⟩ : syracuseStep 1963577 = 1472683) B1472683
theorem B4650857 : Blo 916578 4650857 := bstep (se 2 (by rfl) ⟨1744071, by rfl⟩ : syracuseStep 4650857 = 3488143) B3488143
theorem B2324609 : Blo 916578 2324609 := bstep (se 2 (by rfl) ⟨871728, by rfl⟩ : syracuseStep 2324609 = 1743457) B1743457
theorem B3307655 : Blo 916578 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B2062547 : Blo 916578 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B1243355 : Blo 916578 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B2062601 : Blo 916578 2062601 := bstep (se 2 (by rfl) ⟨773475, by rfl⟩ : syracuseStep 2062601 = 1546951) B1546951
theorem B19855691 : Blo 916578 19855691 := bstep (se 1 (by rfl) ⟨14891768, by rfl⟩ : syracuseStep 19855691 = 29783537) B29783537
theorem B2062817 : Blo 916578 2062817 := bstep (se 2 (by rfl) ⟨773556, by rfl⟩ : syracuseStep 2062817 = 1547113) B1547113
theorem B4422217 : Blo 916578 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B1243831 : Blo 916578 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B2063123 : Blo 916578 2063123 := bstep (se 1 (by rfl) ⟨1547342, by rfl⟩ : syracuseStep 2063123 = 3094685) B3094685
theorem B1375055 : Blo 916578 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B4193167 : Blo 916578 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B2325419 : Blo 916578 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B3275815 : Blo 916578 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B2063483 : Blo 916578 2063483 := bstep (se 1 (by rfl) ⟨1547612, by rfl⟩ : syracuseStep 2063483 = 3095225) B3095225
theorem B1375451 : Blo 916578 1375451 := bstep (se 1 (by rfl) ⟨1031588, by rfl⟩ : syracuseStep 1375451 = 2063177) B2063177
theorem B2063609 : Blo 916578 2063609 := bstep (se 2 (by rfl) ⟨773853, by rfl⟩ : syracuseStep 2063609 = 1547707) B1547707
theorem B916767 : Blo 916578 916767 := bstep (se 1 (by rfl) ⟨687575, by rfl⟩ : syracuseStep 916767 = 1375151) B1375151
theorem B916827 : Blo 916578 916827 := bstep (se 1 (by rfl) ⟨687620, by rfl⟩ : syracuseStep 916827 = 1375241) B1375241
theorem B1277275 : Blo 916578 1277275 := bstep (se 1 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 1277275 = 1915913) B1915913
theorem B916847 : Blo 916578 916847 := bstep (se 1 (by rfl) ⟨687635, by rfl⟩ : syracuseStep 916847 = 1375271) B1375271
theorem B1375625 : Blo 916578 1375625 := bstep (se 2 (by rfl) ⟨515859, by rfl⟩ : syracuseStep 1375625 = 1031719) B1031719
theorem B2063753 : Blo 916578 2063753 := bstep (se 2 (by rfl) ⟨773907, by rfl⟩ : syracuseStep 2063753 = 1547815) B1547815
theorem B916903 : Blo 916578 916903 := bstep (se 1 (by rfl) ⟨687677, by rfl⟩ : syracuseStep 916903 = 1375355) B1375355
theorem B916987 : Blo 916578 916987 := bstep (se 1 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 916987 = 1375481) B1375481
theorem B2063879 : Blo 916578 2063879 := bstep (se 1 (by rfl) ⟨1547909, by rfl⟩ : syracuseStep 2063879 = 3095819) B3095819
theorem B9666071 : Blo 916578 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B7962137 : Blo 916578 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B917055 : Blo 916578 917055 := bstep (se 1 (by rfl) ⟨687791, by rfl⟩ : syracuseStep 917055 = 1375583) B1375583
theorem B917063 : Blo 916578 917063 := bstep (se 1 (by rfl) ⟨687797, by rfl⟩ : syracuseStep 917063 = 1375595) B1375595
theorem B4652639 : Blo 916578 4652639 := bstep (se 1 (by rfl) ⟨3489479, by rfl⟩ : syracuseStep 4652639 = 6978959) B6978959
theorem B2064059 : Blo 916578 2064059 := bstep (se 1 (by rfl) ⟨1548044, by rfl⟩ : syracuseStep 2064059 = 3096089) B3096089
theorem B917215 : Blo 916578 917215 := bstep (se 1 (by rfl) ⟨687911, by rfl⟩ : syracuseStep 917215 = 1375823) B1375823
theorem B1375979 : Blo 916578 1375979 := bstep (se 1 (by rfl) ⟨1031984, by rfl⟩ : syracuseStep 1375979 = 2063969) B2063969
theorem B2326279 : Blo 916578 2326279 := bstep (se 1 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 2326279 = 3489419) B3489419
theorem B917295 : Blo 916578 917295 := bstep (se 1 (by rfl) ⟨687971, by rfl⟩ : syracuseStep 917295 = 1375943) B1375943
theorem B2064185 : Blo 916578 2064185 := bstep (se 2 (by rfl) ⟨774069, by rfl⟩ : syracuseStep 2064185 = 1548139) B1548139
theorem B917403 : Blo 916578 917403 := bstep (se 1 (by rfl) ⟨688052, by rfl⟩ : syracuseStep 917403 = 1376105) B1376105
theorem B917455 : Blo 916578 917455 := bstep (se 1 (by rfl) ⟨688091, by rfl⟩ : syracuseStep 917455 = 1376183) B1376183
theorem B1376207 : Blo 916578 1376207 := bstep (se 1 (by rfl) ⟨1032155, by rfl⟩ : syracuseStep 1376207 = 2064311) B2064311
theorem B917479 : Blo 916578 917479 := bstep (se 1 (by rfl) ⟨688109, by rfl⟩ : syracuseStep 917479 = 1376219) B1376219
theorem B917735 : Blo 916578 917735 := bstep (se 1 (by rfl) ⟨688301, by rfl⟩ : syracuseStep 917735 = 1376603) B1376603
theorem B4653287 : Blo 916578 4653287 := bstep (se 1 (by rfl) ⟨3489965, by rfl⟩ : syracuseStep 4653287 = 6979931) B6979931
theorem B2064671 : Blo 916578 2064671 := bstep (se 1 (by rfl) ⟨1548503, by rfl⟩ : syracuseStep 2064671 = 3097007) B3097007
theorem B1376543 : Blo 916578 1376543 := bstep (se 1 (by rfl) ⟨1032407, by rfl⟩ : syracuseStep 1376543 = 2064815) B2064815
theorem B1376567 : Blo 916578 1376567 := bstep (se 1 (by rfl) ⟨1032425, by rfl⟩ : syracuseStep 1376567 = 2064851) B2064851
theorem B1376639 : Blo 916578 1376639 := bstep (se 1 (by rfl) ⟨1032479, by rfl⟩ : syracuseStep 1376639 = 2064959) B2064959
theorem B917887 : Blo 916578 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B1376711 : Blo 916578 1376711 := bstep (se 1 (by rfl) ⟨1032533, by rfl⟩ : syracuseStep 1376711 = 2065067) B2065067
theorem B917967 : Blo 916578 917967 := bstep (se 1 (by rfl) ⟨688475, by rfl⟩ : syracuseStep 917967 = 1376951) B1376951
theorem B8815067 : Blo 916578 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B918119 : Blo 916578 918119 := bstep (se 1 (by rfl) ⟨688589, by rfl⟩ : syracuseStep 918119 = 1377179) B1377179
theorem B1377065 : Blo 916578 1377065 := bstep (se 2 (by rfl) ⟨516399, by rfl⟩ : syracuseStep 1377065 = 1032799) B1032799
theorem B1377071 : Blo 916578 1377071 := bstep (se 1 (by rfl) ⟨1032803, by rfl⟩ : syracuseStep 1377071 = 2065607) B2065607
theorem B918383 : Blo 916578 918383 := bstep (se 1 (by rfl) ⟨688787, by rfl⟩ : syracuseStep 918383 = 1377575) B1377575
theorem B1344367 : Blo 916578 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B2065319 : Blo 916578 2065319 := bstep (se 1 (by rfl) ⟨1548989, by rfl⟩ : syracuseStep 2065319 = 3097979) B3097979
theorem B1377191 : Blo 916578 1377191 := bstep (se 1 (by rfl) ⟨1032893, by rfl⟩ : syracuseStep 1377191 = 2065787) B2065787
theorem B918439 : Blo 916578 918439 := bstep (se 1 (by rfl) ⟨688829, by rfl⟩ : syracuseStep 918439 = 1377659) B1377659
theorem B1377275 : Blo 916578 1377275 := bstep (se 1 (by rfl) ⟨1032956, by rfl⟩ : syracuseStep 1377275 = 2065913) B2065913
theorem B918523 : Blo 916578 918523 := bstep (se 1 (by rfl) ⟨688892, by rfl⟩ : syracuseStep 918523 = 1377785) B1377785
theorem B1377335 : Blo 916578 1377335 := bstep (se 1 (by rfl) ⟨1033001, by rfl⟩ : syracuseStep 1377335 = 2066003) B2066003
theorem B918591 : Blo 916578 918591 := bstep (se 1 (by rfl) ⟨688943, by rfl⟩ : syracuseStep 918591 = 1377887) B1377887
theorem B1377455 : Blo 916578 1377455 := bstep (se 1 (by rfl) ⟨1033091, by rfl⟩ : syracuseStep 1377455 = 2066183) B2066183
theorem B918735 : Blo 916578 918735 := bstep (se 1 (by rfl) ⟨689051, by rfl⟩ : syracuseStep 918735 = 1378103) B1378103
theorem B918939 : Blo 916578 918939 := bstep (se 1 (by rfl) ⟨689204, by rfl⟩ : syracuseStep 918939 = 1378409) B1378409
theorem B1377863 : Blo 916578 1377863 := bstep (se 1 (by rfl) ⟨1033397, by rfl⟩ : syracuseStep 1377863 = 2066795) B2066795
theorem B919151 : Blo 916578 919151 := bstep (se 1 (by rfl) ⟨689363, by rfl⟩ : syracuseStep 919151 = 1378727) B1378727
theorem B4654745 : Blo 916578 4654745 := bstep (se 2 (by rfl) ⟨1745529, by rfl⟩ : syracuseStep 4654745 = 3491059) B3491059
theorem B1377959 : Blo 916578 1377959 := bstep (se 1 (by rfl) ⟨1033469, by rfl⟩ : syracuseStep 1377959 = 2066939) B2066939
theorem B919207 : Blo 916578 919207 := bstep (se 1 (by rfl) ⟨689405, by rfl⟩ : syracuseStep 919207 = 1378811) B1378811
theorem B1378043 : Blo 916578 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B919291 : Blo 916578 919291 := bstep (se 1 (by rfl) ⟨689468, by rfl⟩ : syracuseStep 919291 = 1378937) B1378937
theorem B1378079 : Blo 916578 1378079 := bstep (se 1 (by rfl) ⟨1033559, by rfl⟩ : syracuseStep 1378079 = 2067119) B2067119
theorem B919327 : Blo 916578 919327 := bstep (se 1 (by rfl) ⟨689495, by rfl⟩ : syracuseStep 919327 = 1378991) B1378991
theorem B919359 : Blo 916578 919359 := bstep (se 1 (by rfl) ⟨689519, by rfl⟩ : syracuseStep 919359 = 1379039) B1379039
theorem B2066255 : Blo 916578 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B1378127 : Blo 916578 1378127 := bstep (se 1 (by rfl) ⟨1033595, by rfl⟩ : syracuseStep 1378127 = 2067191) B2067191
theorem B2066273 : Blo 916578 2066273 := bstep (se 2 (by rfl) ⟨774852, by rfl⟩ : syracuseStep 2066273 = 1549705) B1549705
theorem B1378247 : Blo 916578 1378247 := bstep (se 1 (by rfl) ⟨1033685, by rfl⟩ : syracuseStep 1378247 = 2067371) B2067371
theorem B919535 : Blo 916578 919535 := bstep (se 1 (by rfl) ⟨689651, by rfl⟩ : syracuseStep 919535 = 1379303) B1379303
theorem B919707 : Blo 916578 919707 := bstep (se 1 (by rfl) ⟨689780, by rfl⟩ : syracuseStep 919707 = 1379561) B1379561
theorem B919743 : Blo 916578 919743 := bstep (se 1 (by rfl) ⟨689807, by rfl⟩ : syracuseStep 919743 = 1379615) B1379615
theorem B22382801 : Blo 916578 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B2328871 : Blo 916578 2328871 := bstep (se 1 (by rfl) ⟨1746653, by rfl⟩ : syracuseStep 2328871 = 3493307) B3493307
theorem B1378601 : Blo 916578 1378601 := bstep (se 2 (by rfl) ⟨516975, by rfl⟩ : syracuseStep 1378601 = 1033951) B1033951
theorem B1378607 : Blo 916578 1378607 := bstep (se 1 (by rfl) ⟨1033955, by rfl⟩ : syracuseStep 1378607 = 2067911) B2067911
theorem B919855 : Blo 916578 919855 := bstep (se 1 (by rfl) ⟨689891, by rfl⟩ : syracuseStep 919855 = 1379783) B1379783
theorem B2066849 : Blo 916578 2066849 := bstep (se 2 (by rfl) ⟨775068, by rfl⟩ : syracuseStep 2066849 = 1550137) B1550137
theorem B920091 : Blo 916578 920091 := bstep (se 1 (by rfl) ⟨690068, by rfl⟩ : syracuseStep 920091 = 1380137) B1380137
theorem B2066975 : Blo 916578 2066975 := bstep (se 1 (by rfl) ⟨1550231, by rfl⟩ : syracuseStep 2066975 = 3100463) B3100463
theorem B1378847 : Blo 916578 1378847 := bstep (se 1 (by rfl) ⟨1034135, by rfl⟩ : syracuseStep 1378847 = 2068271) B2068271
theorem B920095 : Blo 916578 920095 := bstep (se 1 (by rfl) ⟨690071, by rfl⟩ : syracuseStep 920095 = 1380143) B1380143
theorem B920411 : Blo 916578 920411 := bstep (se 1 (by rfl) ⟨690308, by rfl⟩ : syracuseStep 920411 = 1380617) B1380617
theorem B1379231 : Blo 916578 1379231 := bstep (se 1 (by rfl) ⟨1034423, by rfl⟩ : syracuseStep 1379231 = 2068847) B2068847
theorem B920479 : Blo 916578 920479 := bstep (se 1 (by rfl) ⟨690359, by rfl⟩ : syracuseStep 920479 = 1380719) B1380719
theorem B1379279 : Blo 916578 1379279 := bstep (se 1 (by rfl) ⟨1034459, by rfl⟩ : syracuseStep 1379279 = 2068919) B2068919
theorem B1379369 : Blo 916578 1379369 := bstep (se 2 (by rfl) ⟨517263, by rfl⟩ : syracuseStep 1379369 = 1034527) B1034527
theorem B1379375 : Blo 916578 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B1379399 : Blo 916578 1379399 := bstep (se 1 (by rfl) ⟨1034549, by rfl⟩ : syracuseStep 1379399 = 2069099) B2069099
theorem B28281935 : Blo 916578 28281935 := bstep (se 1 (by rfl) ⟨21211451, by rfl⟩ : syracuseStep 28281935 = 42422903) B42422903
theorem B2329823 : Blo 916578 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1379663 : Blo 916578 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B1379753 : Blo 916578 1379753 := bstep (se 2 (by rfl) ⟨517407, by rfl⟩ : syracuseStep 1379753 = 1034815) B1034815
theorem B6622715 : Blo 916578 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B1379903 : Blo 916578 1379903 := bstep (se 1 (by rfl) ⟨1034927, by rfl⟩ : syracuseStep 1379903 = 2069855) B2069855
theorem B10456775 : Blo 916578 10456775 := bstep (se 1 (by rfl) ⟨7842581, by rfl⟩ : syracuseStep 10456775 = 15685163) B15685163
theorem B13438723 : Blo 916578 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B1380167 : Blo 916578 1380167 := bstep (se 1 (by rfl) ⟨1035125, by rfl⟩ : syracuseStep 1380167 = 2070251) B2070251
theorem B2068379 : Blo 916578 2068379 := bstep (se 1 (by rfl) ⟨1551284, by rfl⟩ : syracuseStep 2068379 = 3102569) B3102569
theorem B1380251 : Blo 916578 1380251 := bstep (se 1 (by rfl) ⟨1035188, by rfl⟩ : syracuseStep 1380251 = 2070377) B2070377
theorem B4657337 : Blo 916578 4657337 := bstep (se 2 (by rfl) ⟨1746501, by rfl⟩ : syracuseStep 4657337 = 3493003) B3493003
theorem B2068667 : Blo 916578 2068667 := bstep (se 1 (by rfl) ⟨1551500, by rfl⟩ : syracuseStep 2068667 = 3103001) B3103001
theorem B6295805 : Blo 916578 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B2232703 : Blo 916578 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B1380815 : Blo 916578 1380815 := bstep (se 1 (by rfl) ⟨1035611, by rfl⟩ : syracuseStep 1380815 = 2071223) B2071223
theorem B1380857 : Blo 916578 1380857 := bstep (se 2 (by rfl) ⟨517821, by rfl⟩ : syracuseStep 1380857 = 1035643) B1035643
theorem B2069153 : Blo 916578 2069153 := bstep (se 2 (by rfl) ⟨775932, by rfl⟩ : syracuseStep 2069153 = 1551865) B1551865
theorem B8819603 : Blo 916578 8819603 := bstep (se 1 (by rfl) ⟨6614702, by rfl⟩ : syracuseStep 8819603 = 13229405) B13229405
theorem B2069513 : Blo 916578 2069513 := bstep (se 2 (by rfl) ⟨776067, by rfl⟩ : syracuseStep 2069513 = 1552135) B1552135
theorem B2069567 : Blo 916578 2069567 := bstep (se 1 (by rfl) ⟨1552175, by rfl⟩ : syracuseStep 2069567 = 3104351) B3104351
theorem B1741999 : Blo 916578 1741999 := bstep (se 1 (by rfl) ⟨1306499, by rfl⟩ : syracuseStep 1741999 = 2612999) B2612999
theorem B8820413 : Blo 916578 8820413 := bstep (se 3 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 8820413 = 3307655) B3307655
theorem B3315613 : Blo 916578 3315613 := bstep (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) B1243355
theorem B2070503 : Blo 916578 2070503 := bstep (se 1 (by rfl) ⟨1552877, by rfl⟩ : syracuseStep 2070503 = 3105755) B3105755
theorem B2070521 : Blo 916578 2070521 := bstep (se 2 (by rfl) ⟨776445, by rfl⟩ : syracuseStep 2070521 = 1552891) B1552891
theorem B2070611 : Blo 916578 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B2070683 : Blo 916578 2070683 := bstep (se 1 (by rfl) ⟨1553012, by rfl⟩ : syracuseStep 2070683 = 3106025) B3106025
theorem B4659443 : Blo 916578 4659443 := bstep (se 1 (by rfl) ⟨3494582, by rfl⟩ : syracuseStep 4659443 = 6989165) B6989165
theorem B2070791 : Blo 916578 2070791 := bstep (se 1 (by rfl) ⟨1553093, by rfl⟩ : syracuseStep 2070791 = 3106187) B3106187
theorem B50207165 : Blo 916578 50207165 := bstep (se 3 (by rfl) ⟨9413843, by rfl⟩ : syracuseStep 50207165 = 18827687) B18827687
theorem B2071097 : Blo 916578 2071097 := bstep (se 2 (by rfl) ⟨776661, by rfl⟩ : syracuseStep 2071097 = 1553323) B1553323
theorem B3480185 : Blo 916578 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B1743707 : Blo 916578 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B1547167 : Blo 916578 1547167 := bstep (se 1 (by rfl) ⟨1160375, by rfl⟩ : syracuseStep 1547167 = 2320751) B2320751
theorem B1743943 : Blo 916578 1743943 := bstep (se 1 (by rfl) ⟨1307957, by rfl⟩ : syracuseStep 1743943 = 2615915) B2615915
theorem B1547599 : Blo 916578 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B1547687 : Blo 916578 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B16752071 : Blo 916578 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B3349991 : Blo 916578 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1547849 : Blo 916578 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B10461149 : Blo 916578 10461149 := bstep (se 3 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 10461149 = 3922931) B3922931
theorem B1548895 : Blo 916578 1548895 := bstep (se 1 (by rfl) ⟨1161671, by rfl⟩ : syracuseStep 1548895 = 2323343) B2323343
theorem B3351305 : Blo 916578 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B11477771 : Blo 916578 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B1549307 : Blo 916578 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B10593529 : Blo 916578 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B6628715 : Blo 916578 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B4367753 : Blo 916578 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B1549739 : Blo 916578 1549739 := bstep (se 1 (by rfl) ⟨1162304, by rfl⟩ : syracuseStep 1549739 = 2324609) B2324609
theorem B32188265 : Blo 916578 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1550279 : Blo 916578 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B19867801 : Blo 916578 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B1550569 : Blo 916578 1550569 := bstep (se 2 (by rfl) ⟨581463, by rfl⟩ : syracuseStep 1550569 = 1162927) B1162927
theorem B3484043 : Blo 916578 3484043 := bstep (se 1 (by rfl) ⟨2613032, by rfl⟩ : syracuseStep 3484043 = 5226065) B5226065
theorem B2239007 : Blo 916578 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B1551035 : Blo 916578 1551035 := bstep (se 1 (by rfl) ⟨1163276, by rfl⟩ : syracuseStep 1551035 = 2326553) B2326553
theorem B10366427 : Blo 916578 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B1552351 : Blo 916578 1552351 := bstep (se 1 (by rfl) ⟨1164263, by rfl⟩ : syracuseStep 1552351 = 2328527) B2328527
theorem B5582857 : Blo 916578 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B4960379 : Blo 916578 4960379 := bstep (se 1 (by rfl) ⟨3720284, by rfl⟩ : syracuseStep 4960379 = 7440569) B7440569
theorem B1552999 : Blo 916578 1552999 := bstep (se 1 (by rfl) ⟨1164749, by rfl⟩ : syracuseStep 1552999 = 2329499) B2329499
theorem B2798327 : Blo 916578 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1553161 : Blo 916578 1553161 := bstep (se 2 (by rfl) ⟨582435, by rfl⟩ : syracuseStep 1553161 = 1164871) B1164871
theorem B8828099 : Blo 916578 8828099 := bstep (se 1 (by rfl) ⟨6621074, by rfl⟩ : syracuseStep 8828099 = 13242149) B13242149
theorem B10466981 : Blo 916578 10466981 := bstep (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) B1962559
theorem B3094199 : Blo 916578 3094199 := bstep (se 1 (by rfl) ⟨2320649, by rfl⟩ : syracuseStep 3094199 = 4641299) B4641299
theorem B16103123 : Blo 916578 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B3979435 : Blo 916578 3979435 := bstep (se 1 (by rfl) ⟨2984576, by rfl⟩ : syracuseStep 3979435 = 5969153) B5969153
theorem B7846409 : Blo 916578 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B3095387 : Blo 916578 3095387 := bstep (se 1 (by rfl) ⟨2321540, by rfl⟩ : syracuseStep 3095387 = 4643081) B4643081
theorem B5225381 : Blo 916578 5225381 := bstep (se 4 (by rfl) ⟨489879, by rfl⟩ : syracuseStep 5225381 = 979759) B979759
theorem B1031215 : Blo 916578 1031215 := bstep (se 1 (by rfl) ⟨773411, by rfl⟩ : syracuseStep 1031215 = 1546823) B1546823
theorem B1031503 : Blo 916578 1031503 := bstep (se 1 (by rfl) ⟨773627, by rfl⟩ : syracuseStep 1031503 = 1547255) B1547255
theorem B4963751 : Blo 916578 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B3915175 : Blo 916578 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B3096143 : Blo 916578 3096143 := bstep (se 1 (by rfl) ⟨2322107, by rfl⟩ : syracuseStep 3096143 = 4644215) B4644215
theorem B3915449 : Blo 916578 3915449 := bstep (se 2 (by rfl) ⟨1468293, by rfl⟩ : syracuseStep 3915449 = 2936587) B2936587
theorem B3096251 : Blo 916578 3096251 := bstep (se 1 (by rfl) ⟨2322188, by rfl⟩ : syracuseStep 3096251 = 4644377) B4644377
theorem B6962921 : Blo 916578 6962921 := bstep (se 2 (by rfl) ⟨2611095, by rfl⟩ : syracuseStep 6962921 = 5222191) B5222191
theorem B1032007 : Blo 916578 1032007 := bstep (se 1 (by rfl) ⟨774005, by rfl⟩ : syracuseStep 1032007 = 1548011) B1548011
theorem B4964183 : Blo 916578 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B1654751 : Blo 916578 1654751 := bstep (se 1 (by rfl) ⟨1241063, by rfl⟩ : syracuseStep 1654751 = 2482127) B2482127
theorem B3915809 : Blo 916578 3915809 := bstep (se 2 (by rfl) ⟨1468428, by rfl⟩ : syracuseStep 3915809 = 2936857) B2936857
theorem B3490073 : Blo 916578 3490073 := bstep (se 2 (by rfl) ⟨1308777, by rfl⟩ : syracuseStep 3490073 = 2617555) B2617555
theorem B1163575 : Blo 916578 1163575 := bstep (se 1 (by rfl) ⟨872681, by rfl⟩ : syracuseStep 1163575 = 1745363) B1745363
theorem B1032655 : Blo 916578 1032655 := bstep (se 1 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 1032655 = 1548983) B1548983
theorem B3359341 : Blo 916578 3359341 := bstep (se 3 (by rfl) ⟨629876, by rfl⟩ : syracuseStep 3359341 = 1259753) B1259753
theorem B5882939 : Blo 916578 5882939 := bstep (se 1 (by rfl) ⟨4412204, by rfl⟩ : syracuseStep 5882939 = 8824409) B8824409
theorem B1393769 : Blo 916578 1393769 := bstep (se 2 (by rfl) ⟨522663, by rfl⟩ : syracuseStep 1393769 = 1045327) B1045327
theorem B1164395 : Blo 916578 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1656083 : Blo 916578 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B1033627 : Blo 916578 1033627 := bstep (se 1 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 1033627 = 1550441) B1550441
theorem B3098195 : Blo 916578 3098195 := bstep (se 1 (by rfl) ⟨2323646, by rfl⟩ : syracuseStep 3098195 = 4647293) B4647293
theorem B4409129 : Blo 916578 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B19842893 : Blo 916578 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B3098465 : Blo 916578 3098465 := bstep (se 2 (by rfl) ⟨1161924, by rfl⟩ : syracuseStep 3098465 = 2323849) B2323849
theorem B10471355 : Blo 916578 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B3491849 : Blo 916578 3491849 := bstep (se 2 (by rfl) ⟨1309443, by rfl⟩ : syracuseStep 3491849 = 2618887) B2618887
theorem B7850033 : Blo 916578 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B3492031 : Blo 916578 3492031 := bstep (se 1 (by rfl) ⟨2619023, by rfl⟩ : syracuseStep 3492031 = 5238047) B5238047
theorem B1034779 : Blo 916578 1034779 := bstep (se 1 (by rfl) ⟨776084, by rfl⟩ : syracuseStep 1034779 = 1552169) B1552169
theorem B3099167 : Blo 916578 3099167 := bstep (se 1 (by rfl) ⟨2324375, by rfl⟩ : syracuseStep 3099167 = 4648751) B4648751
theorem B4410071 : Blo 916578 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B5230007 : Blo 916578 5230007 := bstep (se 1 (by rfl) ⟨3922505, by rfl⟩ : syracuseStep 5230007 = 7845011) B7845011
theorem B11161151 : Blo 916578 11161151 := bstep (se 1 (by rfl) ⟨8370863, by rfl⟩ : syracuseStep 11161151 = 16741727) B16741727
theorem B1658441 : Blo 916578 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B5590889 : Blo 916578 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B1101691 : Blo 916578 1101691 := bstep (se 1 (by rfl) ⟨826268, by rfl⟩ : syracuseStep 1101691 = 1652537) B1652537
theorem B3100571 : Blo 916578 3100571 := bstep (se 1 (by rfl) ⟨2325428, by rfl⟩ : syracuseStep 3100571 = 4650857) B4650857
theorem B22303025 : Blo 916578 22303025 := bstep (se 2 (by rfl) ⟨8363634, by rfl⟩ : syracuseStep 22303025 = 16727269) B16727269
theorem B22925747 : Blo 916578 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B4182623 : Blo 916578 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B3920507 : Blo 916578 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B3101705 : Blo 916578 3101705 := bstep (se 2 (by rfl) ⟨1163139, by rfl⟩ : syracuseStep 3101705 = 2326279) B2326279
theorem B6444047 : Blo 916578 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B5887039 : Blo 916578 5887039 := bstep (se 1 (by rfl) ⟨4415279, by rfl⟩ : syracuseStep 5887039 = 8830559) B8830559
theorem B3101759 : Blo 916578 3101759 := bstep (se 1 (by rfl) ⟨2326319, by rfl⟩ : syracuseStep 3101759 = 4652639) B4652639
theorem B3724663 : Blo 916578 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B14112643 : Blo 916578 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B4970497 : Blo 916578 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B2939123 : Blo 916578 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B3922283 : Blo 916578 3922283 := bstep (se 1 (by rfl) ⟨2941712, by rfl⟩ : syracuseStep 3922283 = 5883425) B5883425
theorem B11328025 : Blo 916578 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B11950679 : Blo 916578 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B1399607 : Blo 916578 1399607 := bstep (se 1 (by rfl) ⟨1049705, by rfl⟩ : syracuseStep 1399607 = 2099411) B2099411
theorem B3136637 : Blo 916578 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B4775057 : Blo 916578 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B2612827 : Blo 916578 2612827 := bstep (se 1 (by rfl) ⟨1959620, by rfl⟩ : syracuseStep 2612827 = 3919241) B3919241
theorem B3104567 : Blo 916578 3104567 := bstep (se 1 (by rfl) ⟨2328425, by rfl⟩ : syracuseStep 3104567 = 4656851) B4656851
theorem B64642991 : Blo 916578 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B2613181 : Blo 916578 2613181 := bstep (se 3 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 2613181 = 979943) B979943
theorem B10182827 : Blo 916578 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B3104999 : Blo 916578 3104999 := bstep (se 1 (by rfl) ⟨2328749, by rfl⟩ : syracuseStep 3104999 = 4657499) B4657499
theorem B5235131 : Blo 916578 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B3105593 : Blo 916578 3105593 := bstep (se 2 (by rfl) ⟨1164597, by rfl⟩ : syracuseStep 3105593 = 2329195) B2329195
theorem B3105647 : Blo 916578 3105647 := bstep (se 1 (by rfl) ⟨2329235, by rfl⟩ : syracuseStep 3105647 = 4658471) B4658471
theorem B5039003 : Blo 916578 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B4416875 : Blo 916578 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B2352559 : Blo 916578 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3728911 : Blo 916578 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B4646483 : Blo 916578 4646483 := bstep (se 1 (by rfl) ⟨3484862, by rfl⟩ : syracuseStep 4646483 = 6969725) B6969725
theorem B1959545 : Blo 916578 1959545 := bstep (se 2 (by rfl) ⟨734829, by rfl⟩ : syracuseStep 1959545 = 1469659) B1469659
theorem B8840825 : Blo 916578 8840825 := bstep (se 2 (by rfl) ⟨3315309, by rfl⟩ : syracuseStep 8840825 = 6630619) B6630619
theorem B3106457 : Blo 916578 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B9431579 : Blo 916578 9431579 := bstep (se 1 (by rfl) ⟨7073684, by rfl⟩ : syracuseStep 9431579 = 14147369) B14147369
theorem B3926555 : Blo 916578 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B5892857 : Blo 916578 5892857 := bstep (se 2 (by rfl) ⟨2209821, by rfl⟩ : syracuseStep 5892857 = 4419643) B4419643
theorem B2321207 : Blo 916578 2321207 := bstep (se 1 (by rfl) ⟨1740905, by rfl⟩ : syracuseStep 2321207 = 3481811) B3481811
theorem B2944097 : Blo 916578 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B2616563 : Blo 916578 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B2321743 : Blo 916578 2321743 := bstep (se 1 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 2321743 = 3482615) B3482615
theorem B6975071 : Blo 916578 6975071 := bstep (se 1 (by rfl) ⟨5231303, by rfl⟩ : syracuseStep 6975071 = 10462607) B10462607
theorem B7565075 : Blo 916578 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B2486159 : Blo 916578 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B2323039 : Blo 916578 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B1471279 : Blo 916578 1471279 := bstep (se 1 (by rfl) ⟨1103459, by rfl⟩ : syracuseStep 1471279 = 2206919) B2206919
theorem B11793397 : Blo 916578 11793397 := bstep (se 5 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 11793397 = 1105631) B1105631
theorem B1569899 : Blo 916578 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B2946223 : Blo 916578 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B2323667 : Blo 916578 2323667 := bstep (se 1 (by rfl) ⟨1742750, by rfl⟩ : syracuseStep 2323667 = 3485501) B3485501
theorem B25097465 : Blo 916578 25097465 := bstep (se 2 (by rfl) ⟨9411549, by rfl⟩ : syracuseStep 25097465 = 18823099) B18823099
theorem B3306977 : Blo 916578 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B14874121 : Blo 916578 14874121 := bstep (se 2 (by rfl) ⟨5577795, by rfl⟩ : syracuseStep 14874121 = 11155591) B11155591
theorem B5043923 : Blo 916578 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B980767 : Blo 916578 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B3929903 : Blo 916578 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B3307321 : Blo 916578 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B5896289 : Blo 916578 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B1309051 : Blo 916578 1309051 := bstep (se 1 (by rfl) ⟨981788, by rfl⟩ : syracuseStep 1309051 = 1963577) B1963577
theorem B1375031 : Blo 916578 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B1375067 : Blo 916578 1375067 := bstep (se 1 (by rfl) ⟨1031300, by rfl⟩ : syracuseStep 1375067 = 2062601) B2062601
theorem B2063195 : Blo 916578 2063195 := bstep (se 1 (by rfl) ⟨1547396, by rfl⟩ : syracuseStep 2063195 = 3094793) B3094793
theorem B13237127 : Blo 916578 13237127 := bstep (se 1 (by rfl) ⟨9927845, by rfl⟩ : syracuseStep 13237127 = 19855691) B19855691
theorem B1375211 : Blo 916578 1375211 := bstep (se 1 (by rfl) ⟨1031408, by rfl⟩ : syracuseStep 1375211 = 2062817) B2062817
theorem B1703033 : Blo 916578 1703033 := bstep (se 2 (by rfl) ⟨638637, by rfl⟩ : syracuseStep 1703033 = 1277275) B1277275
theorem B1375415 : Blo 916578 1375415 := bstep (se 1 (by rfl) ⟨1031561, by rfl⟩ : syracuseStep 1375415 = 2063123) B2063123
theorem B916703 : Blo 916578 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B1375655 : Blo 916578 1375655 := bstep (se 1 (by rfl) ⟨1031741, by rfl⟩ : syracuseStep 1375655 = 2063483) B2063483
theorem B916967 : Blo 916578 916967 := bstep (se 1 (by rfl) ⟨687725, by rfl⟩ : syracuseStep 916967 = 1375451) B1375451
theorem B1375739 : Blo 916578 1375739 := bstep (se 1 (by rfl) ⟨1031804, by rfl⟩ : syracuseStep 1375739 = 2063609) B2063609
theorem B2063951 : Blo 916578 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B917083 : Blo 916578 917083 := bstep (se 1 (by rfl) ⟨687812, by rfl⟩ : syracuseStep 917083 = 1375625) B1375625
theorem B1375835 : Blo 916578 1375835 := bstep (se 1 (by rfl) ⟨1031876, by rfl⟩ : syracuseStep 1375835 = 2063753) B2063753
theorem B1375919 : Blo 916578 1375919 := bstep (se 1 (by rfl) ⟨1031939, by rfl⟩ : syracuseStep 1375919 = 2063879) B2063879
theorem B5308091 : Blo 916578 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B2326259 : Blo 916578 2326259 := bstep (se 1 (by rfl) ⟨1744694, by rfl⟩ : syracuseStep 2326259 = 3489389) B3489389
theorem B1376039 : Blo 916578 1376039 := bstep (se 1 (by rfl) ⟨1032029, by rfl⟩ : syracuseStep 1376039 = 2064059) B2064059
theorem B917319 : Blo 916578 917319 := bstep (se 1 (by rfl) ⟨687989, by rfl⟩ : syracuseStep 917319 = 1375979) B1375979
theorem B1376123 : Blo 916578 1376123 := bstep (se 1 (by rfl) ⟨1032092, by rfl⟩ : syracuseStep 1376123 = 2064185) B2064185
theorem B917471 : Blo 916578 917471 := bstep (se 1 (by rfl) ⟨688103, by rfl⟩ : syracuseStep 917471 = 1376207) B1376207
theorem B2326715 : Blo 916578 2326715 := bstep (se 1 (by rfl) ⟨1745036, by rfl⟩ : syracuseStep 2326715 = 3490073) B3490073
theorem B1376447 : Blo 916578 1376447 := bstep (se 1 (by rfl) ⟨1032335, by rfl⟩ : syracuseStep 1376447 = 2064671) B2064671
theorem B917695 : Blo 916578 917695 := bstep (se 1 (by rfl) ⟨688271, by rfl⟩ : syracuseStep 917695 = 1376543) B1376543
theorem B917711 : Blo 916578 917711 := bstep (se 1 (by rfl) ⟨688283, by rfl⟩ : syracuseStep 917711 = 1376567) B1376567
theorem B917759 : Blo 916578 917759 := bstep (se 1 (by rfl) ⟨688319, by rfl⟩ : syracuseStep 917759 = 1376639) B1376639
theorem B917807 : Blo 916578 917807 := bstep (se 1 (by rfl) ⟨688355, by rfl⟩ : syracuseStep 917807 = 1376711) B1376711
theorem B918043 : Blo 916578 918043 := bstep (se 1 (by rfl) ⟨688532, by rfl⟩ : syracuseStep 918043 = 1377065) B1377065
theorem B918047 : Blo 916578 918047 := bstep (se 1 (by rfl) ⟨688535, by rfl⟩ : syracuseStep 918047 = 1377071) B1377071
theorem B1376873 : Blo 916578 1376873 := bstep (se 2 (by rfl) ⟨516327, by rfl⟩ : syracuseStep 1376873 = 1032655) B1032655
theorem B1376879 : Blo 916578 1376879 := bstep (se 1 (by rfl) ⟨1032659, by rfl⟩ : syracuseStep 1376879 = 2065319) B2065319
theorem B918127 : Blo 916578 918127 := bstep (se 1 (by rfl) ⟨688595, by rfl⟩ : syracuseStep 918127 = 1377191) B1377191
theorem B918183 : Blo 916578 918183 := bstep (se 1 (by rfl) ⟨688637, by rfl⟩ : syracuseStep 918183 = 1377275) B1377275
theorem B918223 : Blo 916578 918223 := bstep (se 1 (by rfl) ⟨688667, by rfl⟩ : syracuseStep 918223 = 1377335) B1377335
theorem B918303 : Blo 916578 918303 := bstep (se 1 (by rfl) ⟨688727, by rfl⟩ : syracuseStep 918303 = 1377455) B1377455
theorem B2065193 : Blo 916578 2065193 := bstep (se 2 (by rfl) ⟨774447, by rfl⟩ : syracuseStep 2065193 = 1548895) B1548895
theorem B918575 : Blo 916578 918575 := bstep (se 1 (by rfl) ⟨688931, by rfl⟩ : syracuseStep 918575 = 1377863) B1377863
theorem B2065463 : Blo 916578 2065463 := bstep (se 1 (by rfl) ⟨1549097, by rfl⟩ : syracuseStep 2065463 = 3098195) B3098195
theorem B918639 : Blo 916578 918639 := bstep (se 1 (by rfl) ⟨688979, by rfl⟩ : syracuseStep 918639 = 1377959) B1377959
theorem B918695 : Blo 916578 918695 := bstep (se 1 (by rfl) ⟨689021, by rfl⟩ : syracuseStep 918695 = 1378043) B1378043
theorem B918719 : Blo 916578 918719 := bstep (se 1 (by rfl) ⟨689039, by rfl⟩ : syracuseStep 918719 = 1378079) B1378079
theorem B1377503 : Blo 916578 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B918751 : Blo 916578 918751 := bstep (se 1 (by rfl) ⟨689063, by rfl⟩ : syracuseStep 918751 = 1378127) B1378127
theorem B2065643 : Blo 916578 2065643 := bstep (se 1 (by rfl) ⟨1549232, by rfl⟩ : syracuseStep 2065643 = 3098465) B3098465
theorem B1377515 : Blo 916578 1377515 := bstep (se 1 (by rfl) ⟨1033136, by rfl⟩ : syracuseStep 1377515 = 2066273) B2066273
theorem B6980903 : Blo 916578 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B918831 : Blo 916578 918831 := bstep (se 1 (by rfl) ⟨689123, by rfl⟩ : syracuseStep 918831 = 1378247) B1378247
theorem B2327899 : Blo 916578 2327899 := bstep (se 1 (by rfl) ⟨1745924, by rfl⟩ : syracuseStep 2327899 = 3491849) B3491849
theorem B919067 : Blo 916578 919067 := bstep (se 1 (by rfl) ⟨689300, by rfl⟩ : syracuseStep 919067 = 1378601) B1378601
theorem B919071 : Blo 916578 919071 := bstep (se 1 (by rfl) ⟨689303, by rfl⟩ : syracuseStep 919071 = 1378607) B1378607
theorem B1377899 : Blo 916578 1377899 := bstep (se 1 (by rfl) ⟨1033424, by rfl⟩ : syracuseStep 1377899 = 2066849) B2066849
theorem B2066111 : Blo 916578 2066111 := bstep (se 1 (by rfl) ⟨1549583, by rfl⟩ : syracuseStep 2066111 = 3099167) B3099167
theorem B1377983 : Blo 916578 1377983 := bstep (se 1 (by rfl) ⟨1033487, by rfl⟩ : syracuseStep 1377983 = 2066975) B2066975
theorem B919231 : Blo 916578 919231 := bstep (se 1 (by rfl) ⟨689423, by rfl⟩ : syracuseStep 919231 = 1378847) B1378847
theorem B1378169 : Blo 916578 1378169 := bstep (se 2 (by rfl) ⟨516813, by rfl⟩ : syracuseStep 1378169 = 1033627) B1033627
theorem B919487 : Blo 916578 919487 := bstep (se 1 (by rfl) ⟨689615, by rfl⟩ : syracuseStep 919487 = 1379231) B1379231
theorem B919519 : Blo 916578 919519 := bstep (se 1 (by rfl) ⟨689639, by rfl⟩ : syracuseStep 919519 = 1379279) B1379279
theorem B919579 : Blo 916578 919579 := bstep (se 1 (by rfl) ⟨689684, by rfl⟩ : syracuseStep 919579 = 1379369) B1379369
theorem B919583 : Blo 916578 919583 := bstep (se 1 (by rfl) ⟨689687, by rfl⟩ : syracuseStep 919583 = 1379375) B1379375
theorem B919599 : Blo 916578 919599 := bstep (se 1 (by rfl) ⟨689699, by rfl⟩ : syracuseStep 919599 = 1379399) B1379399
theorem B919775 : Blo 916578 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B919835 : Blo 916578 919835 := bstep (se 1 (by rfl) ⟨689876, by rfl⟩ : syracuseStep 919835 = 1379753) B1379753
theorem B7440767 : Blo 916578 7440767 := bstep (se 1 (by rfl) ⟨5580575, by rfl⟩ : syracuseStep 7440767 = 11161151) B11161151
theorem B919935 : Blo 916578 919935 := bstep (se 1 (by rfl) ⟨689951, by rfl⟩ : syracuseStep 919935 = 1379903) B1379903
theorem B920111 : Blo 916578 920111 := bstep (se 1 (by rfl) ⟨690083, by rfl⟩ : syracuseStep 920111 = 1380167) B1380167
theorem B2067047 : Blo 916578 2067047 := bstep (se 1 (by rfl) ⟨1550285, by rfl⟩ : syracuseStep 2067047 = 3100571) B3100571
theorem B1378919 : Blo 916578 1378919 := bstep (se 1 (by rfl) ⟨1034189, by rfl⟩ : syracuseStep 1378919 = 2068379) B2068379
theorem B920167 : Blo 916578 920167 := bstep (se 1 (by rfl) ⟨690125, by rfl⟩ : syracuseStep 920167 = 1380251) B1380251
theorem B1379111 : Blo 916578 1379111 := bstep (se 1 (by rfl) ⟨1034333, by rfl⟩ : syracuseStep 1379111 = 2068667) B2068667
theorem B4197203 : Blo 916578 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B4656041 : Blo 916578 4656041 := bstep (se 2 (by rfl) ⟨1746015, by rfl⟩ : syracuseStep 4656041 = 3492031) B3492031
theorem B920543 : Blo 916578 920543 := bstep (se 1 (by rfl) ⟨690407, by rfl⟩ : syracuseStep 920543 = 1380815) B1380815
theorem B2067425 : Blo 916578 2067425 := bstep (se 2 (by rfl) ⟨775284, by rfl⟩ : syracuseStep 2067425 = 1550569) B1550569
theorem B920571 : Blo 916578 920571 := bstep (se 1 (by rfl) ⟨690428, by rfl⟩ : syracuseStep 920571 = 1380857) B1380857
theorem B2788415 : Blo 916578 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B1379435 : Blo 916578 1379435 := bstep (se 1 (by rfl) ⟨1034576, by rfl⟩ : syracuseStep 1379435 = 2069153) B2069153
theorem B2067803 : Blo 916578 2067803 := bstep (se 1 (by rfl) ⟨1550852, by rfl⟩ : syracuseStep 2067803 = 3101705) B3101705
theorem B1379675 : Blo 916578 1379675 := bstep (se 1 (by rfl) ⟨1034756, by rfl⟩ : syracuseStep 1379675 = 2069513) B2069513
theorem B1379705 : Blo 916578 1379705 := bstep (se 2 (by rfl) ⟨517389, by rfl⟩ : syracuseStep 1379705 = 1034779) B1034779
theorem B2067839 : Blo 916578 2067839 := bstep (se 1 (by rfl) ⟨1550879, by rfl⟩ : syracuseStep 2067839 = 3101759) B3101759
theorem B1379711 : Blo 916578 1379711 := bstep (se 1 (by rfl) ⟨1034783, by rfl⟩ : syracuseStep 1379711 = 2069567) B2069567
theorem B1380335 : Blo 916578 1380335 := bstep (se 1 (by rfl) ⟨1035251, by rfl⟩ : syracuseStep 1380335 = 2070503) B2070503
theorem B1380347 : Blo 916578 1380347 := bstep (se 1 (by rfl) ⟨1035260, by rfl⟩ : syracuseStep 1380347 = 2070521) B2070521
theorem B1380407 : Blo 916578 1380407 := bstep (se 1 (by rfl) ⟨1035305, by rfl⟩ : syracuseStep 1380407 = 2070611) B2070611
theorem B1380455 : Blo 916578 1380455 := bstep (se 1 (by rfl) ⟨1035341, by rfl⟩ : syracuseStep 1380455 = 2070683) B2070683
theorem B1380527 : Blo 916578 1380527 := bstep (se 1 (by rfl) ⟨1035395, by rfl⟩ : syracuseStep 1380527 = 2070791) B2070791
theorem B1380731 : Blo 916578 1380731 := bstep (se 1 (by rfl) ⟨1035548, by rfl⟩ : syracuseStep 1380731 = 2071097) B2071097
theorem B7967119 : Blo 916578 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B3183371 : Blo 916578 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B2233327 : Blo 916578 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2069711 : Blo 916578 2069711 := bstep (se 1 (by rfl) ⟨1552283, by rfl⟩ : syracuseStep 2069711 = 3104567) B3104567
theorem B2069801 : Blo 916578 2069801 := bstep (se 2 (by rfl) ⟨776175, by rfl⟩ : syracuseStep 2069801 = 1552351) B1552351
theorem B7443809 : Blo 916578 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B6788551 : Blo 916578 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B2069999 : Blo 916578 2069999 := bstep (se 1 (by rfl) ⟨1552499, by rfl⟩ : syracuseStep 2069999 = 3104999) B3104999
theorem B2070395 : Blo 916578 2070395 := bstep (se 1 (by rfl) ⟨1552796, by rfl⟩ : syracuseStep 2070395 = 3105593) B3105593
theorem B2070431 : Blo 916578 2070431 := bstep (se 1 (by rfl) ⟨1552823, by rfl⟩ : syracuseStep 2070431 = 3105647) B3105647
theorem B7837661 : Blo 916578 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B2070665 : Blo 916578 2070665 := bstep (se 2 (by rfl) ⟨776499, by rfl⟩ : syracuseStep 2070665 = 1552999) B1552999
theorem B2070881 : Blo 916578 2070881 := bstep (se 2 (by rfl) ⟨776580, by rfl⟩ : syracuseStep 2070881 = 1553161) B1553161
theorem B2070971 : Blo 916578 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B5970685 : Blo 916578 5970685 := bstep (se 3 (by rfl) ⟨1119503, by rfl⟩ : syracuseStep 5970685 = 2239007) B2239007
theorem B1547471 : Blo 916578 1547471 := bstep (se 1 (by rfl) ⟨1160603, by rfl⟩ : syracuseStep 1547471 = 2321207) B2321207
theorem B19832161 : Blo 916578 19832161 := bstep (se 2 (by rfl) ⟨7437060, by rfl⟩ : syracuseStep 19832161 = 14874121) B14874121
theorem B18816857 : Blo 916578 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B6627329 : Blo 916578 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B1745401 : Blo 916578 1745401 := bstep (se 2 (by rfl) ⟨654525, by rfl⟩ : syracuseStep 1745401 = 1309051) B1309051
theorem B1549111 : Blo 916578 1549111 := bstep (se 1 (by rfl) ⟨1161833, by rfl⟩ : syracuseStep 1549111 = 2323667) B2323667
theorem B2204651 : Blo 916578 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B17639045 : Blo 916578 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B5220233 : Blo 916578 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B8824751 : Blo 916578 8824751 := bstep (se 1 (by rfl) ⟨6618563, by rfl⟩ : syracuseStep 8824751 = 13237127) B13237127
theorem B3483587 : Blo 916578 3483587 := bstep (se 1 (by rfl) ⟨2612690, by rfl⟩ : syracuseStep 3483587 = 5225381) B5225381
theorem B5875685 : Blo 916578 5875685 := bstep (se 4 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 5875685 = 1101691) B1101691
theorem B3483769 : Blo 916578 3483769 := bstep (se 2 (by rfl) ⟨1306413, by rfl⟩ : syracuseStep 3483769 = 2612827) B2612827
theorem B1550839 : Blo 916578 1550839 := bstep (se 1 (by rfl) ⟨1163129, by rfl⟩ : syracuseStep 1550839 = 2326259) B2326259
theorem B3484241 : Blo 916578 3484241 := bstep (se 2 (by rfl) ⟨1306590, by rfl⟩ : syracuseStep 3484241 = 2613181) B2613181
theorem B5876711 : Blo 916578 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B1551433 : Blo 916578 1551433 := bstep (se 2 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 1551433 = 1163575) B1163575
theorem B929179 : Blo 916578 929179 := bstep (se 1 (by rfl) ⟨696884, by rfl⟩ : syracuseStep 929179 = 1393769) B1393769
theorem B14921867 : Blo 916578 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B11907749 : Blo 916578 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B18854623 : Blo 916578 18854623 := bstep (se 1 (by rfl) ⟨14140967, by rfl⟩ : syracuseStep 18854623 = 28281935) B28281935
theorem B1553215 : Blo 916578 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B3486671 : Blo 916578 3486671 := bstep (se 1 (by rfl) ⟨2615003, by rfl⟩ : syracuseStep 3486671 = 5230007) B5230007
theorem B17184125 : Blo 916578 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B26490401 : Blo 916578 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B15283831 : Blo 916578 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B5879735 : Blo 916578 5879735 := bstep (se 1 (by rfl) ⟨4409801, by rfl⟩ : syracuseStep 5879735 = 8819603) B8819603
theorem B5880275 : Blo 916578 5880275 := bstep (se 1 (by rfl) ⟨4410206, by rfl⟩ : syracuseStep 5880275 = 8820413) B8820413
theorem B33471443 : Blo 916578 33471443 := bstep (se 1 (by rfl) ⟨25103582, by rfl⟩ : syracuseStep 33471443 = 50207165) B50207165
theorem B3095657 : Blo 916578 3095657 := bstep (se 2 (by rfl) ⟨1160871, by rfl⟩ : syracuseStep 3095657 = 2321743) B2321743
theorem B933071 : Blo 916578 933071 := bstep (se 1 (by rfl) ⟨699803, by rfl⟩ : syracuseStep 933071 = 1399607) B1399607
theorem B1031791 : Blo 916578 1031791 := bstep (se 1 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 1031791 = 1547687) B1547687
theorem B1031899 : Blo 916578 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B3490087 : Blo 916578 3490087 := bstep (se 1 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 3490087 = 5235131) B5235131
theorem B7651847 : Blo 916578 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B3359335 : Blo 916578 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1032871 : Blo 916578 1032871 := bstep (se 1 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 1032871 = 1549307) B1549307
theorem B3097385 : Blo 916578 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B1033159 : Blo 916578 1033159 := bstep (se 1 (by rfl) ⟨774869, by rfl⟩ : syracuseStep 1033159 = 1549739) B1549739
theorem B3097655 : Blo 916578 3097655 := bstep (se 1 (by rfl) ⟨2323241, by rfl⟩ : syracuseStep 3097655 = 4646483) B4646483
theorem B1033519 : Blo 916578 1033519 := bstep (se 1 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 1033519 = 1550279) B1550279
theorem B25150877 : Blo 916578 25150877 := bstep (se 3 (by rfl) ⟨4715789, by rfl⟩ : syracuseStep 25150877 = 9431579) B9431579
theorem B7849385 : Blo 916578 7849385 := bstep (se 2 (by rfl) ⟨2943519, by rfl⟩ : syracuseStep 7849385 = 5887039) B5887039
theorem B1034023 : Blo 916578 1034023 := bstep (se 1 (by rfl) ⟨775517, by rfl⟩ : syracuseStep 1034023 = 1551035) B1551035
theorem B4966217 : Blo 916578 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B1657439 : Blo 916578 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B5885399 : Blo 916578 5885399 := bstep (se 1 (by rfl) ⟨4414049, by rfl⟩ : syracuseStep 5885399 = 8828099) B8828099
theorem B16731643 : Blo 916578 16731643 := bstep (se 1 (by rfl) ⟨12548732, by rfl⟩ : syracuseStep 16731643 = 25097465) B25097465
theorem B10735415 : Blo 916578 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B3362615 : Blo 916578 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B5230757 : Blo 916578 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B5230939 : Blo 916578 5230939 := bstep (se 1 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 5230939 = 7846409) B7846409
theorem B689525237 : Blo 916578 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B1135355 : Blo 916578 1135355 := bstep (se 1 (by rfl) ⟨851516, by rfl⟩ : syracuseStep 1135355 = 1703033) B1703033
theorem B2610299 : Blo 916578 2610299 := bstep (se 1 (by rfl) ⟨1957724, by rfl⟩ : syracuseStep 2610299 = 3915449) B3915449
theorem B4641947 : Blo 916578 4641947 := bstep (se 1 (by rfl) ⟨3481460, by rfl⟩ : syracuseStep 4641947 = 6962921) B6962921
theorem B1103167 : Blo 916578 1103167 := bstep (se 1 (by rfl) ⟨827375, by rfl⟩ : syracuseStep 1103167 = 1654751) B1654751
theorem B2610539 : Blo 916578 2610539 := bstep (se 1 (by rfl) ⟨1957904, by rfl⟩ : syracuseStep 2610539 = 3915809) B3915809
theorem B3102191 : Blo 916578 3102191 := bstep (se 1 (by rfl) ⟨2326643, by rfl⟩ : syracuseStep 3102191 = 4653287) B4653287
theorem B3921959 : Blo 916578 3921959 := bstep (se 1 (by rfl) ⟨2941469, by rfl⟩ : syracuseStep 3921959 = 5882939) B5882939
theorem B3103163 : Blo 916578 3103163 := bstep (se 1 (by rfl) ⟨2327372, by rfl⟩ : syracuseStep 3103163 = 4654745) B4654745
theorem B2939419 : Blo 916578 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B13228595 : Blo 916578 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B5233355 : Blo 916578 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B2940047 : Blo 916578 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B3136745 : Blo 916578 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B7462205 : Blo 916578 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B4971881 : Blo 916578 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B8936813 : Blo 916578 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B4415143 : Blo 916578 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B6971183 : Blo 916578 6971183 := bstep (se 1 (by rfl) ⟨5228387, by rfl⟩ : syracuseStep 6971183 = 10456775) B10456775
theorem B3727259 : Blo 916578 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B3104891 : Blo 916578 3104891 := bstep (se 1 (by rfl) ⟨2328668, by rfl⟩ : syracuseStep 3104891 = 4657337) B4657337
theorem B14868683 : Blo 916578 14868683 := bstep (se 1 (by rfl) ⟨11151512, by rfl⟩ : syracuseStep 14868683 = 22303025) B22303025
theorem B4186397 : Blo 916578 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B3105053 : Blo 916578 3105053 := bstep (se 3 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 3105053 = 1164395) B1164395
theorem B3105161 : Blo 916578 3105161 := bstep (se 2 (by rfl) ⟨1164435, by rfl⟩ : syracuseStep 3105161 = 2328871) B2328871
theorem B2613671 : Blo 916578 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B17916485 : Blo 916578 17916485 := bstep (se 4 (by rfl) ⟨1679670, by rfl⟩ : syracuseStep 17916485 = 3359341) B3359341
theorem B4416221 : Blo 916578 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B3106295 : Blo 916578 3106295 := bstep (se 1 (by rfl) ⟨2329721, by rfl⟩ : syracuseStep 3106295 = 4659443) B4659443
theorem B2614855 : Blo 916578 2614855 := bstep (se 1 (by rfl) ⟨1961141, by rfl⟩ : syracuseStep 2614855 = 3922283) B3922283
theorem B2320123 : Blo 916578 2320123 := bstep (se 1 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 2320123 = 3480185) B3480185
theorem B7169957 : Blo 916578 7169957 := bstep (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) B1344367
theorem B2091091 : Blo 916578 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B11168047 : Blo 916578 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B17918297 : Blo 916578 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B225995285 : Blo 916578 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B6974099 : Blo 916578 6974099 := bstep (se 1 (by rfl) ⟨5230574, by rfl⟩ : syracuseStep 6974099 = 10461149) B10461149
theorem B2944583 : Blo 916578 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B4419143 : Blo 916578 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B2911835 : Blo 916578 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B1961705 : Blo 916578 1961705 := bstep (se 2 (by rfl) ⟨735639, by rfl⟩ : syracuseStep 1961705 = 1471279) B1471279
theorem B1306363 : Blo 916578 1306363 := bstep (se 1 (by rfl) ⟨979772, by rfl⟩ : syracuseStep 1306363 = 1959545) B1959545
theorem B5893883 : Blo 916578 5893883 := bstep (se 1 (by rfl) ⟨4420412, by rfl⟩ : syracuseStep 5893883 = 8840825) B8840825
theorem B21458843 : Blo 916578 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B15724529 : Blo 916578 15724529 := bstep (se 2 (by rfl) ⟨5896698, by rfl⟩ : syracuseStep 15724529 = 11793397) B11793397
theorem B2322665 : Blo 916578 2322665 := bstep (se 2 (by rfl) ⟨870999, by rfl⟩ : syracuseStep 2322665 = 1741999) B1741999
theorem B3928297 : Blo 916578 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B2322695 : Blo 916578 2322695 := bstep (se 1 (by rfl) ⟨1742021, by rfl⟩ : syracuseStep 2322695 = 3484043) B3484043
theorem B2617703 : Blo 916578 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B3928571 : Blo 916578 3928571 := bstep (se 1 (by rfl) ⟨2946428, by rfl⟩ : syracuseStep 3928571 = 5892857) B5892857
theorem B1962731 : Blo 916578 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B4649885 : Blo 916578 4649885 := bstep (se 3 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 4649885 = 1743707) B1743707
theorem B6910951 : Blo 916578 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B4650047 : Blo 916578 4650047 := bstep (se 1 (by rfl) ⟨3487535, by rfl⟩ : syracuseStep 4650047 = 6975071) B6975071
theorem B5043383 : Blo 916578 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B4420817 : Blo 916578 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B3306919 : Blo 916578 3306919 := bstep (se 1 (by rfl) ⟨2480189, by rfl⟩ : syracuseStep 3306919 = 4960379) B4960379
theorem B5305913 : Blo 916578 5305913 := bstep (se 2 (by rfl) ⟨1989717, by rfl⟩ : syracuseStep 5305913 = 3979435) B3979435
theorem B6977501 : Blo 916578 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B15104033 : Blo 916578 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B6977987 : Blo 916578 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B2062799 : Blo 916578 2062799 := bstep (se 1 (by rfl) ⟨1547099, by rfl⟩ : syracuseStep 2062799 = 3094199) B3094199
theorem B2619935 : Blo 916578 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B2062889 : Blo 916578 2062889 := bstep (se 2 (by rfl) ⟨773583, by rfl⟩ : syracuseStep 2062889 = 1547167) B1547167
theorem B1374953 : Blo 916578 1374953 := bstep (se 2 (by rfl) ⟨515607, by rfl⟩ : syracuseStep 1374953 = 1031215) B1031215
theorem B3930859 : Blo 916578 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B2325257 : Blo 916578 2325257 := bstep (se 2 (by rfl) ⟨871971, by rfl⟩ : syracuseStep 2325257 = 1743943) B1743943
theorem B4422509 : Blo 916578 4422509 := bstep (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) B1658441
theorem B1375337 : Blo 916578 1375337 := bstep (se 2 (by rfl) ⟨515751, by rfl⟩ : syracuseStep 1375337 = 1031503) B1031503
theorem B2063465 : Blo 916578 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B916687 : Blo 916578 916687 := bstep (se 1 (by rfl) ⟨687515, by rfl⟩ : syracuseStep 916687 = 1375031) B1375031
theorem B916711 : Blo 916578 916711 := bstep (se 1 (by rfl) ⟨687533, by rfl⟩ : syracuseStep 916711 = 1375067) B1375067
theorem B1375463 : Blo 916578 1375463 := bstep (se 1 (by rfl) ⟨1031597, by rfl⟩ : syracuseStep 1375463 = 2063195) B2063195
theorem B2063591 : Blo 916578 2063591 := bstep (se 1 (by rfl) ⟨1547693, by rfl⟩ : syracuseStep 2063591 = 3095387) B3095387
theorem B916807 : Blo 916578 916807 := bstep (se 1 (by rfl) ⟨687605, by rfl⟩ : syracuseStep 916807 = 1375211) B1375211
theorem B916943 : Blo 916578 916943 := bstep (se 1 (by rfl) ⟨687707, by rfl⟩ : syracuseStep 916943 = 1375415) B1375415
theorem B917103 : Blo 916578 917103 := bstep (se 1 (by rfl) ⟨687827, by rfl⟩ : syracuseStep 917103 = 1375655) B1375655
theorem B3309167 : Blo 916578 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B917159 : Blo 916578 917159 := bstep (se 1 (by rfl) ⟨687869, by rfl⟩ : syracuseStep 917159 = 1375739) B1375739
theorem B1375967 : Blo 916578 1375967 := bstep (se 1 (by rfl) ⟨1031975, by rfl⟩ : syracuseStep 1375967 = 2063951) B2063951
theorem B2064095 : Blo 916578 2064095 := bstep (se 1 (by rfl) ⟨1548071, by rfl⟩ : syracuseStep 2064095 = 3096143) B3096143
theorem B917223 : Blo 916578 917223 := bstep (se 1 (by rfl) ⟨687917, by rfl⟩ : syracuseStep 917223 = 1375835) B1375835
theorem B1376009 : Blo 916578 1376009 := bstep (se 2 (by rfl) ⟨516003, by rfl⟩ : syracuseStep 1376009 = 1032007) B1032007
theorem B917279 : Blo 916578 917279 := bstep (se 1 (by rfl) ⟨687959, by rfl⟩ : syracuseStep 917279 = 1375919) B1375919
theorem B3538727 : Blo 916578 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B2064167 : Blo 916578 2064167 := bstep (se 1 (by rfl) ⟨1548125, by rfl⟩ : syracuseStep 2064167 = 3096251) B3096251
theorem B917359 : Blo 916578 917359 := bstep (se 1 (by rfl) ⟨688019, by rfl⟩ : syracuseStep 917359 = 1376039) B1376039
theorem B3309455 : Blo 916578 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B917415 : Blo 916578 917415 := bstep (se 1 (by rfl) ⟨688061, by rfl⟩ : syracuseStep 917415 = 1376123) B1376123
theorem B917631 : Blo 916578 917631 := bstep (se 1 (by rfl) ⟨688223, by rfl⟩ : syracuseStep 917631 = 1376447) B1376447
theorem B4653449 : Blo 916578 4653449 := bstep (se 2 (by rfl) ⟨1745043, by rfl⟩ : syracuseStep 4653449 = 3490087) B3490087
theorem B917915 : Blo 916578 917915 := bstep (se 1 (by rfl) ⟨688436, by rfl⟩ : syracuseStep 917915 = 1376873) B1376873
theorem B917919 : Blo 916578 917919 := bstep (se 1 (by rfl) ⟨688439, by rfl⟩ : syracuseStep 917919 = 1376879) B1376879
theorem B2064923 : Blo 916578 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B1376795 : Blo 916578 1376795 := bstep (se 1 (by rfl) ⟨1032596, by rfl⟩ : syracuseStep 1376795 = 2065193) B2065193
theorem B2327201 : Blo 916578 2327201 := bstep (se 2 (by rfl) ⟨872700, by rfl⟩ : syracuseStep 2327201 = 1745401) B1745401
theorem B2065103 : Blo 916578 2065103 := bstep (se 1 (by rfl) ⟨1548827, by rfl⟩ : syracuseStep 2065103 = 3097655) B3097655
theorem B1376975 : Blo 916578 1376975 := bstep (se 1 (by rfl) ⟨1032731, by rfl⟩ : syracuseStep 1376975 = 2065463) B2065463
theorem B918335 : Blo 916578 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B1377095 : Blo 916578 1377095 := bstep (se 1 (by rfl) ⟨1032821, by rfl⟩ : syracuseStep 1377095 = 2065643) B2065643
theorem B918343 : Blo 916578 918343 := bstep (se 1 (by rfl) ⟨688757, by rfl⟩ : syracuseStep 918343 = 1377515) B1377515
theorem B4653935 : Blo 916578 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B1377161 : Blo 916578 1377161 := bstep (se 2 (by rfl) ⟨516435, by rfl⟩ : syracuseStep 1377161 = 1032871) B1032871
theorem B918599 : Blo 916578 918599 := bstep (se 1 (by rfl) ⟨688949, by rfl⟩ : syracuseStep 918599 = 1377899) B1377899
theorem B2065481 : Blo 916578 2065481 := bstep (se 2 (by rfl) ⟨774555, by rfl⟩ : syracuseStep 2065481 = 1549111) B1549111
theorem B1377407 : Blo 916578 1377407 := bstep (se 1 (by rfl) ⟨1033055, by rfl⟩ : syracuseStep 1377407 = 2066111) B2066111
theorem B918655 : Blo 916578 918655 := bstep (se 1 (by rfl) ⟨688991, by rfl⟩ : syracuseStep 918655 = 1377983) B1377983
theorem B3310811 : Blo 916578 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B918779 : Blo 916578 918779 := bstep (se 1 (by rfl) ⟨689084, by rfl⟩ : syracuseStep 918779 = 1378169) B1378169
theorem B1377545 : Blo 916578 1377545 := bstep (se 2 (by rfl) ⟨516579, by rfl⟩ : syracuseStep 1377545 = 1033159) B1033159
theorem B47777293 : Blo 916578 47777293 := bstep (se 3 (by rfl) ⟨8958242, by rfl⟩ : syracuseStep 47777293 = 17916485) B17916485
theorem B1378025 : Blo 916578 1378025 := bstep (se 2 (by rfl) ⟨516759, by rfl⟩ : syracuseStep 1378025 = 1033519) B1033519
theorem B1378031 : Blo 916578 1378031 := bstep (se 1 (by rfl) ⟨1033523, by rfl⟩ : syracuseStep 1378031 = 2067047) B2067047
theorem B919279 : Blo 916578 919279 := bstep (se 1 (by rfl) ⟨689459, by rfl⟩ : syracuseStep 919279 = 1378919) B1378919
theorem B919407 : Blo 916578 919407 := bstep (se 1 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 919407 = 1379111) B1379111
theorem B1378283 : Blo 916578 1378283 := bstep (se 1 (by rfl) ⟨1033712, by rfl⟩ : syracuseStep 1378283 = 2067425) B2067425
theorem B919623 : Blo 916578 919623 := bstep (se 1 (by rfl) ⟨689717, by rfl⟩ : syracuseStep 919623 = 1379435) B1379435
theorem B1378535 : Blo 916578 1378535 := bstep (se 1 (by rfl) ⟨1033901, by rfl⟩ : syracuseStep 1378535 = 2067803) B2067803
theorem B919783 : Blo 916578 919783 := bstep (se 1 (by rfl) ⟨689837, by rfl⟩ : syracuseStep 919783 = 1379675) B1379675
theorem B919803 : Blo 916578 919803 := bstep (se 1 (by rfl) ⟨689852, by rfl⟩ : syracuseStep 919803 = 1379705) B1379705
theorem B1378559 : Blo 916578 1378559 := bstep (se 1 (by rfl) ⟨1033919, by rfl⟩ : syracuseStep 1378559 = 2067839) B2067839
theorem B919807 : Blo 916578 919807 := bstep (se 1 (by rfl) ⟨689855, by rfl⟩ : syracuseStep 919807 = 1379711) B1379711
theorem B1378697 : Blo 916578 1378697 := bstep (se 2 (by rfl) ⟨517011, by rfl⟩ : syracuseStep 1378697 = 1034023) B1034023
theorem B920223 : Blo 916578 920223 := bstep (se 1 (by rfl) ⟨690167, by rfl⟩ : syracuseStep 920223 = 1380335) B1380335
theorem B920231 : Blo 916578 920231 := bstep (se 1 (by rfl) ⟨690173, by rfl⟩ : syracuseStep 920231 = 1380347) B1380347
theorem B920271 : Blo 916578 920271 := bstep (se 1 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 920271 = 1380407) B1380407
theorem B920303 : Blo 916578 920303 := bstep (se 1 (by rfl) ⟨690227, by rfl⟩ : syracuseStep 920303 = 1380455) B1380455
theorem B2788121 : Blo 916578 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B920351 : Blo 916578 920351 := bstep (se 1 (by rfl) ⟨690263, by rfl⟩ : syracuseStep 920351 = 1380527) B1380527
theorem B920487 : Blo 916578 920487 := bstep (se 1 (by rfl) ⟨690365, by rfl⟩ : syracuseStep 920487 = 1380731) B1380731
theorem B2067785 : Blo 916578 2067785 := bstep (se 2 (by rfl) ⟨775419, by rfl⟩ : syracuseStep 2067785 = 1550839) B1550839
theorem B1740199 : Blo 916578 1740199 := bstep (se 1 (by rfl) ⟨1305149, by rfl⟩ : syracuseStep 1740199 = 2610299) B2610299
theorem B1379807 : Blo 916578 1379807 := bstep (se 1 (by rfl) ⟨1034855, by rfl⟩ : syracuseStep 1379807 = 2069711) B2069711
theorem B1379867 : Blo 916578 1379867 := bstep (se 1 (by rfl) ⟨1034900, by rfl⟩ : syracuseStep 1379867 = 2069801) B2069801
theorem B1740359 : Blo 916578 1740359 := bstep (se 1 (by rfl) ⟨1305269, by rfl⟩ : syracuseStep 1740359 = 2610539) B2610539
theorem B2068127 : Blo 916578 2068127 := bstep (se 1 (by rfl) ⟨1551095, by rfl⟩ : syracuseStep 2068127 = 3102191) B3102191
theorem B1379999 : Blo 916578 1379999 := bstep (se 1 (by rfl) ⟨1034999, by rfl⟩ : syracuseStep 1379999 = 2069999) B2069999
theorem B1380263 : Blo 916578 1380263 := bstep (se 1 (by rfl) ⟨1035197, by rfl⟩ : syracuseStep 1380263 = 2070395) B2070395
theorem B1380287 : Blo 916578 1380287 := bstep (se 1 (by rfl) ⟨1035215, by rfl⟩ : syracuseStep 1380287 = 2070431) B2070431
theorem B1380443 : Blo 916578 1380443 := bstep (se 1 (by rfl) ⟨1035332, by rfl⟩ : syracuseStep 1380443 = 2070665) B2070665
theorem B2068577 : Blo 916578 2068577 := bstep (se 2 (by rfl) ⟨775716, by rfl⟩ : syracuseStep 2068577 = 1551433) B1551433
theorem B1380587 : Blo 916578 1380587 := bstep (se 1 (by rfl) ⟨1035440, by rfl⟩ : syracuseStep 1380587 = 2070881) B2070881
theorem B2068775 : Blo 916578 2068775 := bstep (se 1 (by rfl) ⟨1551581, by rfl⟩ : syracuseStep 2068775 = 3103163) B3103163
theorem B1380647 : Blo 916578 1380647 := bstep (se 1 (by rfl) ⟨1035485, by rfl⟩ : syracuseStep 1380647 = 2070971) B2070971
theorem B8819063 : Blo 916578 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B3314587 : Blo 916578 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B1741817 : Blo 916578 1741817 := bstep (se 2 (by rfl) ⟨653181, by rfl⟩ : syracuseStep 1741817 = 1306363) B1306363
theorem B2069927 : Blo 916578 2069927 := bstep (se 1 (by rfl) ⟨1552445, by rfl⟩ : syracuseStep 2069927 = 3104891) B3104891
theorem B2790931 : Blo 916578 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2070035 : Blo 916578 2070035 := bstep (se 1 (by rfl) ⟨1552526, by rfl⟩ : syracuseStep 2070035 = 3105053) B3105053
theorem B2070107 : Blo 916578 2070107 := bstep (se 1 (by rfl) ⟨1552580, by rfl⟩ : syracuseStep 2070107 = 3105161) B3105161
theorem B1742447 : Blo 916578 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B10622825 : Blo 916578 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B25139497 : Blo 916578 25139497 := bstep (se 2 (by rfl) ⟨9427311, by rfl⟩ : syracuseStep 25139497 = 18854623) B18854623
theorem B2070863 : Blo 916578 2070863 := bstep (se 1 (by rfl) ⟨1553147, by rfl⟩ : syracuseStep 2070863 = 3106295) B3106295
theorem B2070953 : Blo 916578 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B3480155 : Blo 916578 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B9051401 : Blo 916578 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B1941223 : Blo 916578 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B1548443 : Blo 916578 1548443 := bstep (se 1 (by rfl) ⟨1161332, by rfl⟩ : syracuseStep 1548443 = 2322665) B2322665
theorem B1548463 : Blo 916578 1548463 := bstep (se 1 (by rfl) ⟨1161347, by rfl⟩ : syracuseStep 1548463 = 2322695) B2322695
theorem B1745135 : Blo 916578 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B7938499 : Blo 916578 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B8364653 : Blo 916578 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B10069355 : Blo 916578 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B1746623 : Blo 916578 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B1550171 : Blo 916578 1550171 := bstep (se 1 (by rfl) ⟨1162628, by rfl⟩ : syracuseStep 1550171 = 2325257) B2325257
theorem B147433621 : Blo 916578 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B8825213 : Blo 916578 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B2206111 : Blo 916578 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B1551143 : Blo 916578 1551143 := bstep (se 1 (by rfl) ⟨1163357, by rfl⟩ : syracuseStep 1551143 = 2326715) B2326715
theorem B39791645 : Blo 916578 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B4960511 : Blo 916578 4960511 := bstep (se 1 (by rfl) ⟨3720383, by rfl⟩ : syracuseStep 4960511 = 7440767) B7440767
theorem B2798135 : Blo 916578 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B3027613 : Blo 916578 3027613 := bstep (se 3 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 3027613 = 1135355) B1135355
theorem B3486473 : Blo 916578 3486473 := bstep (se 2 (by rfl) ⟨1307427, by rfl⟩ : syracuseStep 3486473 = 2614855) B2614855
theorem B143471573 : Blo 916578 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B3093497 : Blo 916578 3093497 := bstep (se 2 (by rfl) ⟨1160061, by rfl⟩ : syracuseStep 3093497 = 2320123) B2320123
theorem B7156943 : Blo 916578 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B3487171 : Blo 916578 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B14890729 : Blo 916578 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B3094631 : Blo 916578 3094631 := bstep (se 1 (by rfl) ⟨2320973, by rfl⟩ : syracuseStep 3094631 = 4641947) B4641947
theorem B4962539 : Blo 916578 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B5225107 : Blo 916578 5225107 := bstep (se 1 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 5225107 = 7837661) B7837661
theorem B3488903 : Blo 916578 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B1031647 : Blo 916578 1031647 := bstep (se 1 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 1031647 = 1547471) B1547471
theorem B9912455 : Blo 916578 9912455 := bstep (se 1 (by rfl) ⟨7434341, by rfl⟩ : syracuseStep 9912455 = 14868683) B14868683
theorem B5883167 : Blo 916578 5883167 := bstep (se 1 (by rfl) ⟨4412375, by rfl⟩ : syracuseStep 5883167 = 8824751) B8824751
theorem B3917123 : Blo 916578 3917123 := bstep (se 1 (by rfl) ⟨2937842, by rfl⟩ : syracuseStep 3917123 = 5875685) B5875685
theorem B602654093 : Blo 916578 602654093 := bstep (se 3 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 602654093 = 225995285) B225995285
theorem B11945531 : Blo 916578 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B4409225 : Blo 916578 4409225 := bstep (se 2 (by rfl) ⟨1653459, by rfl⟩ : syracuseStep 4409225 = 3306919) B3306919
theorem B3917807 : Blo 916578 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B14305895 : Blo 916578 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B3099923 : Blo 916578 3099923 := bstep (se 1 (by rfl) ⟨2324942, by rfl⟩ : syracuseStep 3099923 = 4649885) B4649885
theorem B3919225 : Blo 916578 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B3100031 : Blo 916578 3100031 := bstep (se 1 (by rfl) ⟨2325023, by rfl⟩ : syracuseStep 3100031 = 4650047) B4650047
theorem B3362255 : Blo 916578 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B11456083 : Blo 916578 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B3919823 : Blo 916578 3919823 := bstep (se 1 (by rfl) ⟨2939867, by rfl⟩ : syracuseStep 3919823 = 5879735) B5879735
theorem B3920183 : Blo 916578 3920183 := bstep (se 1 (by rfl) ⟨2940137, by rfl⟩ : syracuseStep 3920183 = 5880275) B5880275
theorem B5231213 : Blo 916578 5231213 := bstep (se 3 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 5231213 = 1961705) B1961705
theorem B5886857 : Blo 916578 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B5101231 : Blo 916578 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B4479113 : Blo 916578 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B16767251 : Blo 916578 16767251 := bstep (se 1 (by rfl) ⟨12575438, by rfl⟩ : syracuseStep 16767251 = 25150877) B25150877
theorem B5232923 : Blo 916578 5232923 := bstep (se 1 (by rfl) ⟨3924692, by rfl⟩ : syracuseStep 5232923 = 7849385) B7849385
theorem B1838733965 : Blo 916578 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B1104959 : Blo 916578 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B3103865 : Blo 916578 3103865 := bstep (se 2 (by rfl) ⟨1163949, by rfl⟩ : syracuseStep 3103865 = 2327899) B2327899
theorem B3104027 : Blo 916578 3104027 := bstep (se 1 (by rfl) ⟨2328020, by rfl⟩ : syracuseStep 3104027 = 4656041) B4656041
theorem B1858943 : Blo 916578 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B9952757 : Blo 916578 9952757 := bstep (se 5 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 9952757 = 933071) B933071
theorem B3923599 : Blo 916578 3923599 := bstep (se 1 (by rfl) ⟨2942699, by rfl⟩ : syracuseStep 3923599 = 5885399) B5885399
theorem B4645025 : Blo 916578 4645025 := bstep (se 2 (by rfl) ⟨1741884, by rfl⟩ : syracuseStep 4645025 = 3483769) B3483769
theorem B2122247 : Blo 916578 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2614639 : Blo 916578 2614639 := bstep (se 1 (by rfl) ⟨1960979, by rfl⟩ : syracuseStep 2614639 = 3921959) B3921959
theorem B1238905 : Blo 916578 1238905 := bstep (se 2 (by rfl) ⟨464589, by rfl⟩ : syracuseStep 1238905 = 929179) B929179
theorem B22308857 : Blo 916578 22308857 := bstep (se 2 (by rfl) ⟨8365821, by rfl⟩ : syracuseStep 22308857 = 16731643) B16731643
theorem B1960031 : Blo 916578 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B4974803 : Blo 916578 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B5957875 : Blo 916578 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B4647455 : Blo 916578 4647455 := bstep (se 1 (by rfl) ⟨3485591, by rfl⟩ : syracuseStep 4647455 = 6971183) B6971183
theorem B12544571 : Blo 916578 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B2484839 : Blo 916578 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B4418219 : Blo 916578 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B5237729 : Blo 916578 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B6974585 : Blo 916578 6974585 := bstep (se 2 (by rfl) ⟨2615469, by rfl⟩ : syracuseStep 6974585 = 5230939) B5230939
theorem B2944147 : Blo 916578 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B1469767 : Blo 916578 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B11759363 : Blo 916578 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B4779971 : Blo 916578 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B2322391 : Blo 916578 2322391 := bstep (se 1 (by rfl) ⟨1741793, by rfl⟩ : syracuseStep 2322391 = 3483587) B3483587
theorem B2977769 : Blo 916578 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B2322827 : Blo 916578 2322827 := bstep (se 1 (by rfl) ⟨1742120, by rfl⟩ : syracuseStep 2322827 = 3484241) B3484241
theorem B1470889 : Blo 916578 1470889 := bstep (se 2 (by rfl) ⟨551583, by rfl⟩ : syracuseStep 1470889 = 1103167) B1103167
theorem B4649399 : Blo 916578 4649399 := bstep (se 1 (by rfl) ⟨3487049, by rfl⟩ : syracuseStep 4649399 = 6974099) B6974099
theorem B20378441 : Blo 916578 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B1963055 : Blo 916578 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B2946095 : Blo 916578 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B3929255 : Blo 916578 3929255 := bstep (se 1 (by rfl) ⟨2946941, by rfl⟩ : syracuseStep 3929255 = 5893883) B5893883
theorem B10483019 : Blo 916578 10483019 := bstep (se 1 (by rfl) ⟨7862264, by rfl⟩ : syracuseStep 10483019 = 15724529) B15724529
theorem B2619047 : Blo 916578 2619047 := bstep (se 1 (by rfl) ⟨1964285, by rfl⟩ : syracuseStep 2619047 = 3928571) B3928571
theorem B1308487 : Blo 916578 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B2324447 : Blo 916578 2324447 := bstep (se 1 (by rfl) ⟨1743335, by rfl⟩ : syracuseStep 2324447 = 3486671) B3486671
theorem B2947211 : Blo 916578 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B5241145 : Blo 916578 5241145 := bstep (se 2 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 5241145 = 3930859) B3930859
theorem B7960913 : Blo 916578 7960913 := bstep (se 2 (by rfl) ⟨2985342, by rfl⟩ : syracuseStep 7960913 = 5970685) B5970685
theorem B17660267 : Blo 916578 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B3537275 : Blo 916578 3537275 := bstep (se 1 (by rfl) ⟨2652956, by rfl⟩ : syracuseStep 3537275 = 5305913) B5305913
theorem B4651667 : Blo 916578 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B4651991 : Blo 916578 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B1375199 : Blo 916578 1375199 := bstep (se 1 (by rfl) ⟨1031399, by rfl⟩ : syracuseStep 1375199 = 2062799) B2062799
theorem B1375259 : Blo 916578 1375259 := bstep (se 1 (by rfl) ⟨1031444, by rfl⟩ : syracuseStep 1375259 = 2062889) B2062889
theorem B26442881 : Blo 916578 26442881 := bstep (se 2 (by rfl) ⟨9916080, by rfl⟩ : syracuseStep 26442881 = 19832161) B19832161
theorem B916635 : Blo 916578 916635 := bstep (se 1 (by rfl) ⟨687476, by rfl⟩ : syracuseStep 916635 = 1374953) B1374953
theorem B2948339 : Blo 916578 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B22314295 : Blo 916578 22314295 := bstep (se 1 (by rfl) ⟨16735721, by rfl⟩ : syracuseStep 22314295 = 33471443) B33471443
theorem B916891 : Blo 916578 916891 := bstep (se 1 (by rfl) ⟨687668, by rfl⟩ : syracuseStep 916891 = 1375337) B1375337
theorem B1375643 : Blo 916578 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B2063771 : Blo 916578 2063771 := bstep (se 1 (by rfl) ⟨1547828, by rfl⟩ : syracuseStep 2063771 = 3095657) B3095657
theorem B1375721 : Blo 916578 1375721 := bstep (se 2 (by rfl) ⟨515895, by rfl⟩ : syracuseStep 1375721 = 1031791) B1031791
theorem B916975 : Blo 916578 916975 := bstep (se 1 (by rfl) ⟨687731, by rfl⟩ : syracuseStep 916975 = 1375463) B1375463
theorem B1375727 : Blo 916578 1375727 := bstep (se 1 (by rfl) ⟨1031795, by rfl⟩ : syracuseStep 1375727 = 2063591) B2063591
theorem B1375865 : Blo 916578 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B917311 : Blo 916578 917311 := bstep (se 1 (by rfl) ⟨687983, by rfl⟩ : syracuseStep 917311 = 1375967) B1375967
theorem B1376063 : Blo 916578 1376063 := bstep (se 1 (by rfl) ⟨1032047, by rfl⟩ : syracuseStep 1376063 = 2064095) B2064095
theorem B917339 : Blo 916578 917339 := bstep (se 1 (by rfl) ⟨688004, by rfl⟩ : syracuseStep 917339 = 1376009) B1376009
theorem B1376111 : Blo 916578 1376111 := bstep (se 1 (by rfl) ⟨1032083, by rfl⟩ : syracuseStep 1376111 = 2064167) B2064167
theorem B2359151 : Blo 916578 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B2064617 : Blo 916578 2064617 := bstep (se 2 (by rfl) ⟨774231, by rfl⟩ : syracuseStep 2064617 = 1548463) B1548463
theorem B1376615 : Blo 916578 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B917863 : Blo 916578 917863 := bstep (se 1 (by rfl) ⟨688397, by rfl⟩ : syracuseStep 917863 = 1376795) B1376795
theorem B1376735 : Blo 916578 1376735 := bstep (se 1 (by rfl) ⟨1032551, by rfl⟩ : syracuseStep 1376735 = 2065103) B2065103
theorem B917983 : Blo 916578 917983 := bstep (se 1 (by rfl) ⟨688487, by rfl⟩ : syracuseStep 917983 = 1376975) B1376975
theorem B918063 : Blo 916578 918063 := bstep (se 1 (by rfl) ⟨688547, by rfl⟩ : syracuseStep 918063 = 1377095) B1377095
theorem B10584665 : Blo 916578 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B918107 : Blo 916578 918107 := bstep (se 1 (by rfl) ⟨688580, by rfl⟩ : syracuseStep 918107 = 1377161) B1377161
theorem B1376987 : Blo 916578 1376987 := bstep (se 1 (by rfl) ⟨1032740, by rfl⟩ : syracuseStep 1376987 = 2065481) B2065481
theorem B918271 : Blo 916578 918271 := bstep (se 1 (by rfl) ⟨688703, by rfl⟩ : syracuseStep 918271 = 1377407) B1377407
theorem B918363 : Blo 916578 918363 := bstep (se 1 (by rfl) ⟨688772, by rfl⟩ : syracuseStep 918363 = 1377545) B1377545
theorem B401769395 : Blo 916578 401769395 := bstep (se 1 (by rfl) ⟨301327046, by rfl⟩ : syracuseStep 401769395 = 602654093) B602654093
theorem B7963687 : Blo 916578 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B918683 : Blo 916578 918683 := bstep (se 1 (by rfl) ⟨689012, by rfl⟩ : syracuseStep 918683 = 1378025) B1378025
theorem B918687 : Blo 916578 918687 := bstep (se 1 (by rfl) ⟨689015, by rfl⟩ : syracuseStep 918687 = 1378031) B1378031
theorem B918855 : Blo 916578 918855 := bstep (se 1 (by rfl) ⟨689141, by rfl⟩ : syracuseStep 918855 = 1378283) B1378283
theorem B919023 : Blo 916578 919023 := bstep (se 1 (by rfl) ⟨689267, by rfl⟩ : syracuseStep 919023 = 1378535) B1378535
theorem B919039 : Blo 916578 919039 := bstep (se 1 (by rfl) ⟨689279, by rfl⟩ : syracuseStep 919039 = 1378559) B1378559
theorem B919131 : Blo 916578 919131 := bstep (se 1 (by rfl) ⟨689348, by rfl⟩ : syracuseStep 919131 = 1378697) B1378697
theorem B9537263 : Blo 916578 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B63703057 : Blo 916578 63703057 := bstep (se 2 (by rfl) ⟨23888646, by rfl⟩ : syracuseStep 63703057 = 47777293) B47777293
theorem B2066615 : Blo 916578 2066615 := bstep (se 1 (by rfl) ⟨1549961, by rfl⟩ : syracuseStep 2066615 = 3099923) B3099923
theorem B1378523 : Blo 916578 1378523 := bstep (se 1 (by rfl) ⟨1033892, by rfl⟩ : syracuseStep 1378523 = 2067785) B2067785
theorem B2066687 : Blo 916578 2066687 := bstep (se 1 (by rfl) ⟨1550015, by rfl⟩ : syracuseStep 2066687 = 3100031) B3100031
theorem B919871 : Blo 916578 919871 := bstep (se 1 (by rfl) ⟨689903, by rfl⟩ : syracuseStep 919871 = 1379807) B1379807
theorem B919911 : Blo 916578 919911 := bstep (se 1 (by rfl) ⟨689933, by rfl⟩ : syracuseStep 919911 = 1379867) B1379867
theorem B15698285 : Blo 916578 15698285 := bstep (se 3 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 15698285 = 5886857) B5886857
theorem B1378751 : Blo 916578 1378751 := bstep (se 1 (by rfl) ⟨1034063, by rfl⟩ : syracuseStep 1378751 = 2068127) B2068127
theorem B919999 : Blo 916578 919999 := bstep (se 1 (by rfl) ⟨689999, by rfl⟩ : syracuseStep 919999 = 1379999) B1379999
theorem B920175 : Blo 916578 920175 := bstep (se 1 (by rfl) ⟨690131, by rfl⟩ : syracuseStep 920175 = 1380263) B1380263
theorem B920191 : Blo 916578 920191 := bstep (se 1 (by rfl) ⟨690143, by rfl⟩ : syracuseStep 920191 = 1380287) B1380287
theorem B920295 : Blo 916578 920295 := bstep (se 1 (by rfl) ⟨690221, by rfl⟩ : syracuseStep 920295 = 1380443) B1380443
theorem B1379051 : Blo 916578 1379051 := bstep (se 1 (by rfl) ⟨1034288, by rfl⟩ : syracuseStep 1379051 = 2068577) B2068577
theorem B920391 : Blo 916578 920391 := bstep (se 1 (by rfl) ⟨690293, by rfl⟩ : syracuseStep 920391 = 1380587) B1380587
theorem B1379183 : Blo 916578 1379183 := bstep (se 1 (by rfl) ⟨1034387, by rfl⟩ : syracuseStep 1379183 = 2068775) B2068775
theorem B920431 : Blo 916578 920431 := bstep (se 1 (by rfl) ⟨690323, by rfl⟩ : syracuseStep 920431 = 1380647) B1380647
theorem B196578161 : Blo 916578 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B1379951 : Blo 916578 1379951 := bstep (se 1 (by rfl) ⟨1034963, by rfl⟩ : syracuseStep 1379951 = 2069927) B2069927
theorem B1380023 : Blo 916578 1380023 := bstep (se 1 (by rfl) ⟨1035017, by rfl⟩ : syracuseStep 1380023 = 2070035) B2070035
theorem B1380071 : Blo 916578 1380071 := bstep (se 1 (by rfl) ⟨1035053, by rfl⟩ : syracuseStep 1380071 = 2070107) B2070107
theorem B7081883 : Blo 916578 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B2986075 : Blo 916578 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B11178167 : Blo 916578 11178167 := bstep (se 1 (by rfl) ⟨8383625, by rfl⟩ : syracuseStep 11178167 = 16767251) B16767251
theorem B1380575 : Blo 916578 1380575 := bstep (se 1 (by rfl) ⟨1035431, by rfl⟩ : syracuseStep 1380575 = 2070863) B2070863
theorem B1380635 : Blo 916578 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B1225822643 : Blo 916578 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B4657661 : Blo 916578 4657661 := bstep (se 3 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 4657661 = 1746623) B1746623
theorem B2069243 : Blo 916578 2069243 := bstep (se 1 (by rfl) ⟨1551932, by rfl⟩ : syracuseStep 2069243 = 3103865) B3103865
theorem B6034267 : Blo 916578 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B2069351 : Blo 916578 2069351 := bstep (se 1 (by rfl) ⟨1552013, by rfl⟩ : syracuseStep 2069351 = 3104027) B3104027
theorem B1414831 : Blo 916578 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B5576435 : Blo 916578 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B4036817 : Blo 916578 4036817 := bstep (se 2 (by rfl) ⟨1513806, by rfl⟩ : syracuseStep 4036817 = 3027613) B3027613
theorem B3316535 : Blo 916578 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B8363047 : Blo 916578 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B1744649 : Blo 916578 1744649 := bstep (se 2 (by rfl) ⟨654243, by rfl⟩ : syracuseStep 1744649 = 1308487) B1308487
theorem B7839575 : Blo 916578 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B3186647 : Blo 916578 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B1548551 : Blo 916578 1548551 := bstep (se 1 (by rfl) ⟨1161413, by rfl⟩ : syracuseStep 1548551 = 2322827) B2322827
theorem B6988193 : Blo 916578 6988193 := bstep (se 2 (by rfl) ⟨2620572, by rfl⟩ : syracuseStep 6988193 = 5241145) B5241145
theorem B6988679 : Blo 916578 6988679 := bstep (se 1 (by rfl) ⟨5241509, by rfl⟩ : syracuseStep 6988679 = 10483019) B10483019
theorem B1746031 : Blo 916578 1746031 := bstep (se 1 (by rfl) ⟨1309523, by rfl⟩ : syracuseStep 1746031 = 2619047) B2619047
theorem B1549631 : Blo 916578 1549631 := bstep (se 1 (by rfl) ⟨1162223, by rfl⟩ : syracuseStep 1549631 = 2324447) B2324447
theorem B11773511 : Blo 916578 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B7940717 : Blo 916578 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B1551467 : Blo 916578 1551467 := bstep (se 1 (by rfl) ⟨1163600, by rfl⟩ : syracuseStep 1551467 = 2327201) B2327201
theorem B2207207 : Blo 916578 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B3486185 : Blo 916578 3486185 := bstep (se 2 (by rfl) ⟨1307319, by rfl⟩ : syracuseStep 3486185 = 2614639) B2614639
theorem B2241503 : Blo 916578 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B1160239 : Blo 916578 1160239 := bstep (se 1 (by rfl) ⟨870179, by rfl⟩ : syracuseStep 1160239 = 1740359) B1740359
theorem B5879375 : Blo 916578 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B3487475 : Blo 916578 3487475 := bstep (se 1 (by rfl) ⟨2615606, by rfl⟩ : syracuseStep 3487475 = 5231213) B5231213
theorem B1161211 : Blo 916578 1161211 := bstep (se 1 (by rfl) ⟨870908, by rfl⟩ : syracuseStep 1161211 = 1741817) B1741817
theorem B1161631 : Blo 916578 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B3488615 : Blo 916578 3488615 := bstep (se 1 (by rfl) ⟨2616461, by rfl⟩ : syracuseStep 3488615 = 5232923) B5232923
theorem B5225633 : Blo 916578 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B6635171 : Blo 916578 6635171 := bstep (se 1 (by rfl) ⟨4976378, by rfl⟩ : syracuseStep 6635171 = 9952757) B9952757
theorem B3096521 : Blo 916578 3096521 := bstep (se 2 (by rfl) ⟨1161195, by rfl⟩ : syracuseStep 3096521 = 2322391) B2322391
theorem B1032295 : Blo 916578 1032295 := bstep (se 1 (by rfl) ⟨774221, by rfl⟩ : syracuseStep 1032295 = 1548443) B1548443
theorem B3096683 : Blo 916578 3096683 := bstep (se 1 (by rfl) ⟨2322512, by rfl⟩ : syracuseStep 3096683 = 4645025) B4645025
theorem B1163423 : Blo 916578 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B1033447 : Blo 916578 1033447 := bstep (se 1 (by rfl) ⟨775085, by rfl⟩ : syracuseStep 1033447 = 1550171) B1550171
theorem B5883475 : Blo 916578 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B3098303 : Blo 916578 3098303 := bstep (se 1 (by rfl) ⟨2323727, by rfl⟩ : syracuseStep 3098303 = 4647455) B4647455
theorem B1656559 : Blo 916578 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B1034095 : Blo 916578 1034095 := bstep (se 1 (by rfl) ⟨775571, by rfl⟩ : syracuseStep 1034095 = 1551143) B1551143
theorem B3491819 : Blo 916578 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B26527763 : Blo 916578 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B3721241 : Blo 916578 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B6801641 : Blo 916578 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B3099599 : Blo 916578 3099599 := bstep (se 1 (by rfl) ⟨2324699, by rfl⟩ : syracuseStep 3099599 = 4649399) B4649399
theorem B61099109 : Blo 916578 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B13585627 : Blo 916578 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B4771295 : Blo 916578 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B6966809 : Blo 916578 6966809 := bstep (se 2 (by rfl) ⟨2612553, by rfl⟩ : syracuseStep 6966809 = 5225107) B5225107
theorem B3101111 : Blo 916578 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B6607493 : Blo 916578 6607493 := bstep (se 4 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 6607493 = 1238905) B1238905
theorem B3101327 : Blo 916578 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B5231465 : Blo 916578 5231465 := bstep (se 2 (by rfl) ⟨1961799, by rfl⟩ : syracuseStep 5231465 = 3923599) B3923599
theorem B6608303 : Blo 916578 6608303 := bstep (se 1 (by rfl) ⟨4956227, by rfl⟩ : syracuseStep 6608303 = 9912455) B9912455
theorem B3102299 : Blo 916578 3102299 := bstep (se 1 (by rfl) ⟨2326724, by rfl⟩ : syracuseStep 3102299 = 4653449) B4653449
theorem B3102623 : Blo 916578 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B3922111 : Blo 916578 3922111 := bstep (se 1 (by rfl) ⟨2941583, by rfl⟩ : syracuseStep 3922111 = 5883167) B5883167
theorem B2611415 : Blo 916578 2611415 := bstep (se 1 (by rfl) ⟨1958561, by rfl⟩ : syracuseStep 2611415 = 3917123) B3917123
theorem B2939483 : Blo 916578 2939483 := bstep (se 1 (by rfl) ⟨2204612, by rfl⟩ : syracuseStep 2939483 = 4409225) B4409225
theorem B31775333 : Blo 916578 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B2611871 : Blo 916578 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B2613215 : Blo 916578 2613215 := bstep (se 1 (by rfl) ⟨1959911, by rfl⟩ : syracuseStep 2613215 = 3919823) B3919823
theorem B5234813 : Blo 916578 5234813 := bstep (se 3 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 5234813 = 1963055) B1963055
theorem B2613455 : Blo 916578 2613455 := bstep (se 1 (by rfl) ⟨1960091, by rfl⟩ : syracuseStep 2613455 = 3920183) B3920183
theorem B2941481 : Blo 916578 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B3925529 : Blo 916578 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B2320103 : Blo 916578 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B1959689 : Blo 916578 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B2320265 : Blo 916578 2320265 := bstep (se 2 (by rfl) ⟨870099, by rfl⟩ : syracuseStep 2320265 = 1740199) B1740199
theorem B1239295 : Blo 916578 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B1961185 : Blo 916578 1961185 := bstep (se 2 (by rfl) ⟨735444, by rfl⟩ : syracuseStep 1961185 = 1470889) B1470889
theorem B6712903 : Blo 916578 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B9432733 : Blo 916578 9432733 := bstep (se 3 (by rfl) ⟨1768637, by rfl⟩ : syracuseStep 9432733 = 3537275) B3537275
theorem B4419449 : Blo 916578 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B14872571 : Blo 916578 14872571 := bstep (se 1 (by rfl) ⟨11154428, by rfl⟩ : syracuseStep 14872571 = 22308857) B22308857
theorem B1306687 : Blo 916578 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B2945479 : Blo 916578 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B4649561 : Blo 916578 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B7434989 : Blo 916578 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B4649723 : Blo 916578 4649723 := bstep (se 1 (by rfl) ⟨3487292, by rfl⟩ : syracuseStep 4649723 = 6974585) B6974585
theorem B19854305 : Blo 916578 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B2946557 : Blo 916578 2946557 := bstep (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) B1104959
theorem B3307007 : Blo 916578 3307007 := bstep (se 1 (by rfl) ⟨2480255, by rfl⟩ : syracuseStep 3307007 = 4960511) B4960511
theorem B1865423 : Blo 916578 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B33519329 : Blo 916578 33519329 := bstep (se 2 (by rfl) ⟨12569748, by rfl⟩ : syracuseStep 33519329 = 25139497) B25139497
theorem B2324315 : Blo 916578 2324315 := bstep (se 1 (by rfl) ⟨1743236, by rfl⟩ : syracuseStep 2324315 = 3486473) B3486473
theorem B95647715 : Blo 916578 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B2062331 : Blo 916578 2062331 := bstep (se 1 (by rfl) ⟨1546748, by rfl⟩ : syracuseStep 2062331 = 3093497) B3093497
theorem B1964063 : Blo 916578 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B2619503 : Blo 916578 2619503 := bstep (se 1 (by rfl) ⟨1964627, by rfl⟩ : syracuseStep 2619503 = 3929255) B3929255
theorem B2063087 : Blo 916578 2063087 := bstep (se 1 (by rfl) ⟨1547315, by rfl⟩ : syracuseStep 2063087 = 3094631) B3094631
theorem B1964807 : Blo 916578 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B3308359 : Blo 916578 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B5307275 : Blo 916578 5307275 := bstep (se 1 (by rfl) ⟨3980456, by rfl⟩ : syracuseStep 5307275 = 7960913) B7960913
theorem B29752393 : Blo 916578 29752393 := bstep (se 2 (by rfl) ⟨11157147, by rfl⟩ : syracuseStep 29752393 = 22314295) B22314295
theorem B1375529 : Blo 916578 1375529 := bstep (se 2 (by rfl) ⟨515823, by rfl⟩ : syracuseStep 1375529 = 1031647) B1031647
theorem B916799 : Blo 916578 916799 := bstep (se 1 (by rfl) ⟨687599, by rfl⟩ : syracuseStep 916799 = 1375199) B1375199
theorem B916839 : Blo 916578 916839 := bstep (se 1 (by rfl) ⟨687629, by rfl⟩ : syracuseStep 916839 = 1375259) B1375259
theorem B17628587 : Blo 916578 17628587 := bstep (se 1 (by rfl) ⟨13221440, by rfl⟩ : syracuseStep 17628587 = 26442881) B26442881
theorem B2325935 : Blo 916578 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B1965559 : Blo 916578 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B917095 : Blo 916578 917095 := bstep (se 1 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 917095 = 1375643) B1375643
theorem B1375847 : Blo 916578 1375847 := bstep (se 1 (by rfl) ⟨1031885, by rfl⟩ : syracuseStep 1375847 = 2063771) B2063771
theorem B2588297 : Blo 916578 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B917147 : Blo 916578 917147 := bstep (se 1 (by rfl) ⟨687860, by rfl⟩ : syracuseStep 917147 = 1375721) B1375721
theorem B917151 : Blo 916578 917151 := bstep (se 1 (by rfl) ⟨687863, by rfl⟩ : syracuseStep 917151 = 1375727) B1375727
theorem B917243 : Blo 916578 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B917375 : Blo 916578 917375 := bstep (se 1 (by rfl) ⟨688031, by rfl⟩ : syracuseStep 917375 = 1376063) B1376063
theorem B1572767 : Blo 916578 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B917407 : Blo 916578 917407 := bstep (se 1 (by rfl) ⟨688055, by rfl⟩ : syracuseStep 917407 = 1376111) B1376111
theorem B2064455 : Blo 916578 2064455 := bstep (se 1 (by rfl) ⟨1548341, by rfl⟩ : syracuseStep 2064455 = 3096683) B3096683
theorem B1376393 : Blo 916578 1376393 := bstep (se 2 (by rfl) ⟨516147, by rfl⟩ : syracuseStep 1376393 = 1032295) B1032295
theorem B1376411 : Blo 916578 1376411 := bstep (se 1 (by rfl) ⟨1032308, by rfl⟩ : syracuseStep 1376411 = 2064617) B2064617
theorem B917743 : Blo 916578 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B917823 : Blo 916578 917823 := bstep (se 1 (by rfl) ⟨688367, by rfl⟩ : syracuseStep 917823 = 1376735) B1376735
theorem B917991 : Blo 916578 917991 := bstep (se 1 (by rfl) ⟨688493, by rfl⟩ : syracuseStep 917991 = 1376987) B1376987
theorem B15925733 : Blo 916578 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B267846263 : Blo 916578 267846263 := bstep (se 1 (by rfl) ⟨200884697, by rfl⟩ : syracuseStep 267846263 = 401769395) B401769395
theorem B2065535 : Blo 916578 2065535 := bstep (se 1 (by rfl) ⟨1549151, by rfl⟩ : syracuseStep 2065535 = 3098303) B3098303
theorem B6358175 : Blo 916578 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B2327879 : Blo 916578 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1377743 : Blo 916578 1377743 := bstep (se 1 (by rfl) ⟨1033307, by rfl⟩ : syracuseStep 1377743 = 2066615) B2066615
theorem B919015 : Blo 916578 919015 := bstep (se 1 (by rfl) ⟨689261, by rfl⟩ : syracuseStep 919015 = 1378523) B1378523
theorem B2328041 : Blo 916578 2328041 := bstep (se 2 (by rfl) ⟨873015, by rfl⟩ : syracuseStep 2328041 = 1746031) B1746031
theorem B1377791 : Blo 916578 1377791 := bstep (se 1 (by rfl) ⟨1033343, by rfl⟩ : syracuseStep 1377791 = 2066687) B2066687
theorem B919167 : Blo 916578 919167 := bstep (se 1 (by rfl) ⟨689375, by rfl⟩ : syracuseStep 919167 = 1378751) B1378751
theorem B1377929 : Blo 916578 1377929 := bstep (se 2 (by rfl) ⟨516723, by rfl⟩ : syracuseStep 1377929 = 1033447) B1033447
theorem B919367 : Blo 916578 919367 := bstep (se 1 (by rfl) ⟨689525, by rfl⟩ : syracuseStep 919367 = 1379051) B1379051
theorem B919455 : Blo 916578 919455 := bstep (se 1 (by rfl) ⟨689591, by rfl⟩ : syracuseStep 919455 = 1379183) B1379183
theorem B2066399 : Blo 916578 2066399 := bstep (se 1 (by rfl) ⟨1549799, by rfl⟩ : syracuseStep 2066399 = 3099599) B3099599
theorem B40732739 : Blo 916578 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B3180863 : Blo 916578 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B919967 : Blo 916578 919967 := bstep (se 1 (by rfl) ⟨689975, by rfl⟩ : syracuseStep 919967 = 1379951) B1379951
theorem B920015 : Blo 916578 920015 := bstep (se 1 (by rfl) ⟨690011, by rfl⟩ : syracuseStep 920015 = 1380023) B1380023
theorem B1378793 : Blo 916578 1378793 := bstep (se 2 (by rfl) ⟨517047, by rfl⟩ : syracuseStep 1378793 = 1034095) B1034095
theorem B920047 : Blo 916578 920047 := bstep (se 1 (by rfl) ⟨690035, by rfl⟩ : syracuseStep 920047 = 1380071) B1380071
theorem B4721255 : Blo 916578 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B84937409 : Blo 916578 84937409 := bstep (se 2 (by rfl) ⟨31851528, by rfl⟩ : syracuseStep 84937409 = 63703057) B63703057
theorem B920383 : Blo 916578 920383 := bstep (se 1 (by rfl) ⟨690287, by rfl⟩ : syracuseStep 920383 = 1380575) B1380575
theorem B920423 : Blo 916578 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B2067407 : Blo 916578 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B2067551 : Blo 916578 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B1379495 : Blo 916578 1379495 := bstep (se 1 (by rfl) ⟨1034621, by rfl⟩ : syracuseStep 1379495 = 2069243) B2069243
theorem B1379567 : Blo 916578 1379567 := bstep (se 1 (by rfl) ⟨1034675, by rfl⟩ : syracuseStep 1379567 = 2069351) B2069351
theorem B2068199 : Blo 916578 2068199 := bstep (se 1 (by rfl) ⟨1551149, by rfl⟩ : syracuseStep 2068199 = 3102299) B3102299
theorem B2068415 : Blo 916578 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B1740943 : Blo 916578 1740943 := bstep (se 1 (by rfl) ⟨1305707, by rfl⟩ : syracuseStep 1740943 = 2611415) B2611415
theorem B1741247 : Blo 916578 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B8950537 : Blo 916578 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B1742143 : Blo 916578 1742143 := bstep (se 1 (by rfl) ⟨1306607, by rfl⟩ : syracuseStep 1742143 = 2613215) B2613215
theorem B1742249 : Blo 916578 1742249 := bstep (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) B1306687
theorem B1742303 : Blo 916578 1742303 := bstep (se 1 (by rfl) ⟨1306727, by rfl⟩ : syracuseStep 1742303 = 2613455) B2613455
theorem B42472997 : Blo 916578 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B4658795 : Blo 916578 4658795 := bstep (se 1 (by rfl) ⟨3494096, by rfl⟩ : syracuseStep 4658795 = 6988193) B6988193
theorem B4659119 : Blo 916578 4659119 := bstep (se 1 (by rfl) ⟨3494339, by rfl⟩ : syracuseStep 4659119 = 6988679) B6988679
theorem B72456677 : Blo 916578 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B1546735 : Blo 916578 1546735 := bstep (se 1 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 1546735 = 2320103) B2320103
theorem B1546843 : Blo 916578 1546843 := bstep (se 1 (by rfl) ⟨1160132, by rfl⟩ : syracuseStep 1546843 = 2320265) B2320265
theorem B1546985 : Blo 916578 1546985 := bstep (se 2 (by rfl) ⟨580119, by rfl⟩ : syracuseStep 1546985 = 1160239) B1160239
theorem B1548281 : Blo 916578 1548281 := bstep (se 2 (by rfl) ⟨580605, by rfl⟩ : syracuseStep 1548281 = 1161211) B1161211
theorem B4956659 : Blo 916578 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B1548841 : Blo 916578 1548841 := bstep (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) B1161631
theorem B2204671 : Blo 916578 2204671 := bstep (se 1 (by rfl) ⟨1653503, by rfl⟩ : syracuseStep 2204671 = 3307007) B3307007
theorem B1549543 : Blo 916578 1549543 := bstep (se 1 (by rfl) ⟨1162157, by rfl⟩ : syracuseStep 1549543 = 2324315) B2324315
theorem B11150729 : Blo 916578 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B1746335 : Blo 916578 1746335 := bstep (se 1 (by rfl) ⟨1309751, by rfl⟩ : syracuseStep 1746335 = 2619503) B2619503
theorem B3483755 : Blo 916578 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B1550623 : Blo 916578 1550623 := bstep (se 1 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 1550623 = 2325935) B2325935
theorem B7056443 : Blo 916578 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B7843949 : Blo 916578 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B4534427 : Blo 916578 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B10465523 : Blo 916578 10465523 := bstep (se 1 (by rfl) ⟨7849142, by rfl⟩ : syracuseStep 10465523 = 15698285) B15698285
theorem B131052107 : Blo 916578 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B7844633 : Blo 916578 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B2208745 : Blo 916578 2208745 := bstep (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) B1656559
theorem B817215095 : Blo 916578 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B1652393 : Blo 916578 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B4404995 : Blo 916578 4404995 := bstep (se 1 (by rfl) ⟨3303746, by rfl⟩ : syracuseStep 4404995 = 6607493) B6607493
theorem B3487643 : Blo 916578 3487643 := bstep (se 1 (by rfl) ⟨2615732, by rfl⟩ : syracuseStep 3487643 = 5231465) B5231465
theorem B4405535 : Blo 916578 4405535 := bstep (se 1 (by rfl) ⟨3304151, by rfl⟩ : syracuseStep 4405535 = 6608303) B6608303
theorem B3717623 : Blo 916578 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B2211023 : Blo 916578 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B1163099 : Blo 916578 1163099 := bstep (se 1 (by rfl) ⟨872324, by rfl⟩ : syracuseStep 1163099 = 1744649) B1744649
theorem B5226383 : Blo 916578 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B3489875 : Blo 916578 3489875 := bstep (se 1 (by rfl) ⟨2617406, by rfl⟩ : syracuseStep 3489875 = 5234813) B5234813
theorem B1032367 : Blo 916578 1032367 := bstep (se 1 (by rfl) ⟨774275, by rfl⟩ : syracuseStep 1032367 = 1548551) B1548551
theorem B10764845 : Blo 916578 10764845 := bstep (se 3 (by rfl) ⟨2018408, by rfl⟩ : syracuseStep 10764845 = 4036817) B4036817
theorem B1033087 : Blo 916578 1033087 := bstep (se 1 (by rfl) ⟨774815, by rfl⟩ : syracuseStep 1033087 = 1549631) B1549631
theorem B7849007 : Blo 916578 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B338936885 : Blo 916578 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B8045689 : Blo 916578 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B27608501 : Blo 916578 27608501 := bstep (se 5 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 27608501 = 2588297) B2588297
theorem B5293811 : Blo 916578 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B1034311 : Blo 916578 1034311 := bstep (se 1 (by rfl) ⟨775733, by rfl⟩ : syracuseStep 1034311 = 1551467) B1551467
theorem B1886441 : Blo 916578 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B9915047 : Blo 916578 9915047 := bstep (se 1 (by rfl) ⟨7436285, by rfl⟩ : syracuseStep 9915047 = 14872571) B14872571
theorem B5229481 : Blo 916578 5229481 := bstep (se 2 (by rfl) ⟨1961055, by rfl⟩ : syracuseStep 5229481 = 3922111) B3922111
theorem B3099707 : Blo 916578 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B3099815 : Blo 916578 3099815 := bstep (se 1 (by rfl) ⟨2324861, by rfl⟩ : syracuseStep 3099815 = 4649723) B4649723
theorem B1494335 : Blo 916578 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B3919583 : Blo 916578 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B4411145 : Blo 916578 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B5885885 : Blo 916578 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B39669857 : Blo 916578 39669857 := bstep (se 2 (by rfl) ⟨14876196, by rfl⟩ : syracuseStep 39669857 = 29752393) B29752393
theorem B11752391 : Blo 916578 11752391 := bstep (se 1 (by rfl) ⟨8814293, by rfl⟩ : syracuseStep 11752391 = 17628587) B17628587
theorem B3102461 : Blo 916578 3102461 := bstep (se 3 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 3102461 = 1163423) B1163423
theorem B29808445 : Blo 916578 29808445 := bstep (se 3 (by rfl) ⟨5589083, by rfl⟩ : syracuseStep 29808445 = 11178167) B11178167
theorem B17685175 : Blo 916578 17685175 := bstep (se 1 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 17685175 = 26527763) B26527763
theorem B4644539 : Blo 916578 4644539 := bstep (se 1 (by rfl) ⟨3483404, by rfl⟩ : syracuseStep 4644539 = 6966809) B6966809
theorem B3105107 : Blo 916578 3105107 := bstep (se 1 (by rfl) ⟨2328830, by rfl⟩ : syracuseStep 3105107 = 4657661) B4657661
theorem B2614913 : Blo 916578 2614913 := bstep (se 2 (by rfl) ⟨980592, by rfl⟩ : syracuseStep 2614913 = 1961185) B1961185
theorem B1959655 : Blo 916578 1959655 := bstep (se 1 (by rfl) ⟨1469741, by rfl⟩ : syracuseStep 1959655 = 2939483) B2939483
theorem B12576977 : Blo 916578 12576977 := bstep (se 2 (by rfl) ⟨4716366, by rfl⟩ : syracuseStep 12576977 = 9432733) B9432733
theorem B2124431 : Blo 916578 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B9923309 : Blo 916578 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B3927305 : Blo 916578 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B2617019 : Blo 916578 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B1306459 : Blo 916578 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B2946299 : Blo 916578 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B2324123 : Blo 916578 2324123 := bstep (se 1 (by rfl) ⟨1743092, by rfl⟩ : syracuseStep 2324123 = 3486185) B3486185
theorem B13236203 : Blo 916578 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B1964371 : Blo 916578 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B1243615 : Blo 916578 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B22346219 : Blo 916578 22346219 := bstep (se 1 (by rfl) ⟨16759664, by rfl⟩ : syracuseStep 22346219 = 33519329) B33519329
theorem B2324983 : Blo 916578 2324983 := bstep (se 1 (by rfl) ⟨1743737, by rfl⟩ : syracuseStep 2324983 = 3487475) B3487475
theorem B63765143 : Blo 916578 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B1374887 : Blo 916578 1374887 := bstep (se 1 (by rfl) ⟨1031165, by rfl⟩ : syracuseStep 1374887 = 2062331) B2062331
theorem B1309375 : Blo 916578 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B1375391 : Blo 916578 1375391 := bstep (se 1 (by rfl) ⟨1031543, by rfl⟩ : syracuseStep 1375391 = 2063087) B2063087
theorem B1309871 : Blo 916578 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B2325743 : Blo 916578 2325743 := bstep (se 1 (by rfl) ⟨1744307, by rfl⟩ : syracuseStep 2325743 = 3488615) B3488615
theorem B3538183 : Blo 916578 3538183 := bstep (se 1 (by rfl) ⟨2653637, by rfl⟩ : syracuseStep 3538183 = 5307275) B5307275
theorem B2620745 : Blo 916578 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B917019 : Blo 916578 917019 := bstep (se 1 (by rfl) ⟨687764, by rfl⟩ : syracuseStep 917019 = 1375529) B1375529
theorem B917231 : Blo 916578 917231 := bstep (se 1 (by rfl) ⟨687923, by rfl⟩ : syracuseStep 917231 = 1375847) B1375847
theorem B4423447 : Blo 916578 4423447 := bstep (se 1 (by rfl) ⟨3317585, by rfl⟩ : syracuseStep 4423447 = 6635171) B6635171
theorem B1048511 : Blo 916578 1048511 := bstep (se 1 (by rfl) ⟨786383, by rfl⟩ : syracuseStep 1048511 = 1572767) B1572767
theorem B2064347 : Blo 916578 2064347 := bstep (se 1 (by rfl) ⟨1548260, by rfl⟩ : syracuseStep 2064347 = 3096521) B3096521
theorem B1376303 : Blo 916578 1376303 := bstep (se 1 (by rfl) ⟨1032227, by rfl⟩ : syracuseStep 1376303 = 2064455) B2064455
theorem B2326583 : Blo 916578 2326583 := bstep (se 1 (by rfl) ⟨1744937, by rfl⟩ : syracuseStep 2326583 = 3489875) B3489875
theorem B917595 : Blo 916578 917595 := bstep (se 1 (by rfl) ⟨688196, by rfl⟩ : syracuseStep 917595 = 1376393) B1376393
theorem B917607 : Blo 916578 917607 := bstep (se 1 (by rfl) ⟨688205, by rfl⟩ : syracuseStep 917607 = 1376411) B1376411
theorem B1376489 : Blo 916578 1376489 := bstep (se 2 (by rfl) ⟨516183, by rfl⟩ : syracuseStep 1376489 = 1032367) B1032367
theorem B10617155 : Blo 916578 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B7176563 : Blo 916578 7176563 := bstep (se 1 (by rfl) ⟨5382422, by rfl⟩ : syracuseStep 7176563 = 10764845) B10764845
theorem B2065121 : Blo 916578 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B1377023 : Blo 916578 1377023 := bstep (se 1 (by rfl) ⟨1032767, by rfl⟩ : syracuseStep 1377023 = 2065535) B2065535
theorem B918495 : Blo 916578 918495 := bstep (se 1 (by rfl) ⟨688871, by rfl⟩ : syracuseStep 918495 = 1377743) B1377743
theorem B918527 : Blo 916578 918527 := bstep (se 1 (by rfl) ⟨688895, by rfl⟩ : syracuseStep 918527 = 1377791) B1377791
theorem B918619 : Blo 916578 918619 := bstep (se 1 (by rfl) ⟨688964, by rfl⟩ : syracuseStep 918619 = 1377929) B1377929
theorem B1377449 : Blo 916578 1377449 := bstep (se 2 (by rfl) ⟨516543, by rfl⟩ : syracuseStep 1377449 = 1033087) B1033087
theorem B1377599 : Blo 916578 1377599 := bstep (se 1 (by rfl) ⟨1033199, by rfl⟩ : syracuseStep 1377599 = 2066399) B2066399
theorem B2066057 : Blo 916578 2066057 := bstep (se 2 (by rfl) ⟨774771, by rfl⟩ : syracuseStep 2066057 = 1549543) B1549543
theorem B919195 : Blo 916578 919195 := bstep (se 1 (by rfl) ⟨689396, by rfl⟩ : syracuseStep 919195 = 1378793) B1378793
theorem B3147503 : Blo 916578 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B56624939 : Blo 916578 56624939 := bstep (se 1 (by rfl) ⟨42468704, by rfl⟩ : syracuseStep 56624939 = 84937409) B84937409
theorem B1378271 : Blo 916578 1378271 := bstep (se 1 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 1378271 = 2067407) B2067407
theorem B2066471 : Blo 916578 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B1378367 : Blo 916578 1378367 := bstep (se 1 (by rfl) ⟨1033775, by rfl⟩ : syracuseStep 1378367 = 2067551) B2067551
theorem B2066543 : Blo 916578 2066543 := bstep (se 1 (by rfl) ⟨1549907, by rfl⟩ : syracuseStep 2066543 = 3099815) B3099815
theorem B919663 : Blo 916578 919663 := bstep (se 1 (by rfl) ⟨689747, by rfl⟩ : syracuseStep 919663 = 1379495) B1379495
theorem B919711 : Blo 916578 919711 := bstep (se 1 (by rfl) ⟨689783, by rfl⟩ : syracuseStep 919711 = 1379567) B1379567
theorem B20122037 : Blo 916578 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B1378799 : Blo 916578 1378799 := bstep (se 1 (by rfl) ⟨1034099, by rfl⟩ : syracuseStep 1378799 = 2068199) B2068199
theorem B1378943 : Blo 916578 1378943 := bstep (se 1 (by rfl) ⟨1034207, by rfl⟩ : syracuseStep 1378943 = 2068415) B2068415
theorem B26446571 : Blo 916578 26446571 := bstep (se 1 (by rfl) ⟨19834928, by rfl⟩ : syracuseStep 26446571 = 39669857) B39669857
theorem B1379081 : Blo 916578 1379081 := bstep (se 2 (by rfl) ⟨517155, by rfl⟩ : syracuseStep 1379081 = 1034311) B1034311
theorem B2067497 : Blo 916578 2067497 := bstep (se 2 (by rfl) ⟨775311, by rfl⟩ : syracuseStep 2067497 = 1550623) B1550623
theorem B7834927 : Blo 916578 7834927 := bstep (se 1 (by rfl) ⟨5876195, by rfl⟩ : syracuseStep 7834927 = 11752391) B11752391
theorem B6983333 : Blo 916578 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B28315331 : Blo 916578 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B2068307 : Blo 916578 2068307 := bstep (se 1 (by rfl) ⟨1551230, by rfl⟩ : syracuseStep 2068307 = 3102461) B3102461
theorem B48304451 : Blo 916578 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B2070071 : Blo 916578 2070071 := bstep (se 1 (by rfl) ⟨1552553, by rfl⟩ : syracuseStep 2070071 = 3105107) B3105107
theorem B11934049 : Blo 916578 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B1743275 : Blo 916578 1743275 := bstep (se 1 (by rfl) ⟨1307456, by rfl⟩ : syracuseStep 1743275 = 2614913) B2614913
theorem B1416287 : Blo 916578 1416287 := bstep (se 1 (by rfl) ⟨1062215, by rfl⟩ : syracuseStep 1416287 = 2124431) B2124431
theorem B1744679 : Blo 916578 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B3022951 : Blo 916578 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B18817181 : Blo 916578 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B87368071 : Blo 916578 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B544810063 : Blo 916578 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B1549415 : Blo 916578 1549415 := bstep (se 1 (by rfl) ⟨1162061, by rfl⟩ : syracuseStep 1549415 = 2324123) B2324123
theorem B8824135 : Blo 916578 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B42510095 : Blo 916578 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B1550495 : Blo 916578 1550495 := bstep (se 1 (by rfl) ⟨1162871, by rfl⟩ : syracuseStep 1550495 = 2325743) B2325743
theorem B1747163 : Blo 916578 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B2796029 : Blo 916578 2796029 := bstep (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) B1048511
theorem B3484255 : Blo 916578 3484255 := bstep (se 1 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 3484255 = 5226383) B5226383
theorem B178564175 : Blo 916578 178564175 := bstep (se 1 (by rfl) ⟨133923131, by rfl⟩ : syracuseStep 178564175 = 267846263) B267846263
theorem B4238783 : Blo 916578 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B1551919 : Blo 916578 1551919 := bstep (se 1 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 1551919 = 2327879) B2327879
theorem B1552027 : Blo 916578 1552027 := bstep (se 1 (by rfl) ⟨1164020, by rfl⟩ : syracuseStep 1552027 = 2328041) B2328041
theorem B10727585 : Blo 916578 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B996223 : Blo 916578 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B1160831 : Blo 916578 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B1161535 : Blo 916578 1161535 := bstep (se 1 (by rfl) ⟨871151, by rfl⟩ : syracuseStep 1161535 = 1742303) B1742303
theorem B1031323 : Blo 916578 1031323 := bstep (se 1 (by rfl) ⟨773492, by rfl⟩ : syracuseStep 1031323 = 1546985) B1546985
theorem B3096359 : Blo 916578 3096359 := bstep (se 1 (by rfl) ⟨2322269, by rfl⟩ : syracuseStep 3096359 = 4644539) B4644539
theorem B1032187 : Blo 916578 1032187 := bstep (se 1 (by rfl) ⟨774140, by rfl⟩ : syracuseStep 1032187 = 1548281) B1548281
theorem B1164223 : Blo 916578 1164223 := bstep (se 1 (by rfl) ⟨873167, by rfl⟩ : syracuseStep 1164223 = 1746335) B1746335
theorem B9913661 : Blo 916578 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B5229299 : Blo 916578 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B3492989 : Blo 916578 3492989 := bstep (se 3 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 3492989 = 1309871) B1309871
theorem B5229755 : Blo 916578 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B1658153 : Blo 916578 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B3099977 : Blo 916578 3099977 := bstep (se 2 (by rfl) ⟨1162491, by rfl⟩ : syracuseStep 3099977 = 2324983) B2324983
theorem B10472813 : Blo 916578 10472813 := bstep (se 3 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 10472813 = 3927305) B3927305
theorem B23580233 : Blo 916578 23580233 := bstep (se 2 (by rfl) ⟨8842587, by rfl⟩ : syracuseStep 23580233 = 17685175) B17685175
theorem B1101595 : Blo 916578 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B2936663 : Blo 916578 2936663 := bstep (se 1 (by rfl) ⟨2202497, by rfl⟩ : syracuseStep 2936663 = 4404995) B4404995
theorem B2937023 : Blo 916578 2937023 := bstep (se 1 (by rfl) ⟨2202767, by rfl⟩ : syracuseStep 2937023 = 4405535) B4405535
theorem B14897479 : Blo 916578 14897479 := bstep (se 1 (by rfl) ⟨11173109, by rfl⟩ : syracuseStep 14897479 = 22346219) B22346219
theorem B6967781 : Blo 916578 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B3101597 : Blo 916578 3101597 := bstep (se 3 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 3101597 = 1163099) B1163099
theorem B5232671 : Blo 916578 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B225957923 : Blo 916578 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B18405667 : Blo 916578 18405667 := bstep (se 1 (by rfl) ⟨13804250, by rfl⟩ : syracuseStep 18405667 = 27608501) B27608501
theorem B3529207 : Blo 916578 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B2939561 : Blo 916578 2939561 := bstep (se 2 (by rfl) ⟨1102335, by rfl⟩ : syracuseStep 2939561 = 2204671) B2204671
theorem B27155159 : Blo 916578 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B2120575 : Blo 916578 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B6610031 : Blo 916578 6610031 := bstep (se 1 (by rfl) ⟨4957523, by rfl⟩ : syracuseStep 6610031 = 9915047) B9915047
theorem B2612873 : Blo 916578 2612873 := bstep (se 2 (by rfl) ⟨979827, by rfl⟩ : syracuseStep 2612873 = 1959655) B1959655
theorem B2613055 : Blo 916578 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B3923923 : Blo 916578 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B7856797 : Blo 916578 7856797 := bstep (se 3 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 7856797 = 2946299) B2946299
theorem B3105863 : Blo 916578 3105863 := bstep (se 1 (by rfl) ⟨2329397, by rfl⟩ : syracuseStep 3105863 = 4658795) B4658795
theorem B4645997 : Blo 916578 4645997 := bstep (se 3 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 4645997 = 1742249) B1742249
theorem B6972641 : Blo 916578 6972641 := bstep (se 2 (by rfl) ⟨2614740, by rfl⟩ : syracuseStep 6972641 = 5229481) B5229481
theorem B3106079 : Blo 916578 3106079 := bstep (se 1 (by rfl) ⟨2329559, by rfl⟩ : syracuseStep 3106079 = 4659119) B4659119
theorem B2321257 : Blo 916578 2321257 := bstep (se 2 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 2321257 = 1740943) B1740943
theorem B3304439 : Blo 916578 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B7433819 : Blo 916578 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B2944993 : Blo 916578 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B2322503 : Blo 916578 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B8384651 : Blo 916578 8384651 := bstep (se 1 (by rfl) ⟨6288488, by rfl⟩ : syracuseStep 8384651 = 12576977) B12576977
theorem B2322857 : Blo 916578 2322857 := bstep (se 2 (by rfl) ⟨871071, by rfl⟩ : syracuseStep 2322857 = 1742143) B1742143
theorem B6615539 : Blo 916578 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B39744593 : Blo 916578 39744593 := bstep (se 2 (by rfl) ⟨14904222, by rfl⟩ : syracuseStep 39744593 = 29808445) B29808445
theorem B6977015 : Blo 916578 6977015 := bstep (se 1 (by rfl) ⟨5232761, by rfl⟩ : syracuseStep 6977015 = 10465523) B10465523
theorem B2619161 : Blo 916578 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B5896061 : Blo 916578 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B2062313 : Blo 916578 2062313 := bstep (se 2 (by rfl) ⟨773367, by rfl⟩ : syracuseStep 2062313 = 1546735) B1546735
theorem B2062457 : Blo 916578 2062457 := bstep (se 2 (by rfl) ⟨773421, by rfl⟩ : syracuseStep 2062457 = 1546843) B1546843
theorem B2325095 : Blo 916578 2325095 := bstep (se 1 (by rfl) ⟨1743821, by rfl⟩ : syracuseStep 2325095 = 3487643) B3487643
theorem B4717577 : Blo 916578 4717577 := bstep (se 2 (by rfl) ⟨1769091, by rfl⟩ : syracuseStep 4717577 = 3538183) B3538183
theorem B916591 : Blo 916578 916591 := bstep (se 1 (by rfl) ⟨687443, by rfl⟩ : syracuseStep 916591 = 1374887) B1374887
theorem B11763053 : Blo 916578 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B916927 : Blo 916578 916927 := bstep (se 1 (by rfl) ⟨687695, by rfl⟩ : syracuseStep 916927 = 1375391) B1375391
theorem B5897929 : Blo 916578 5897929 := bstep (se 2 (by rfl) ⟨2211723, by rfl⟩ : syracuseStep 5897929 = 4423447) B4423447
theorem B1376231 : Blo 916578 1376231 := bstep (se 1 (by rfl) ⟨1032173, by rfl⟩ : syracuseStep 1376231 = 2064347) B2064347
theorem B917535 : Blo 916578 917535 := bstep (se 1 (by rfl) ⟨688151, by rfl⟩ : syracuseStep 917535 = 1376303) B1376303
theorem B4030601 : Blo 916578 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B917659 : Blo 916578 917659 := bstep (se 1 (by rfl) ⟨688244, by rfl⟩ : syracuseStep 917659 = 1376489) B1376489
theorem B7078103 : Blo 916578 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B4784375 : Blo 916578 4784375 := bstep (se 1 (by rfl) ⟨3588281, by rfl⟩ : syracuseStep 4784375 = 7176563) B7176563
theorem B1376747 : Blo 916578 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B918015 : Blo 916578 918015 := bstep (se 1 (by rfl) ⟨688511, by rfl⟩ : syracuseStep 918015 = 1377023) B1377023
theorem B116490761 : Blo 916578 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B918299 : Blo 916578 918299 := bstep (se 1 (by rfl) ⟨688724, by rfl⟩ : syracuseStep 918299 = 1377449) B1377449
theorem B918399 : Blo 916578 918399 := bstep (se 1 (by rfl) ⟨688799, by rfl⟩ : syracuseStep 918399 = 1377599) B1377599
theorem B1377371 : Blo 916578 1377371 := bstep (se 1 (by rfl) ⟨1033028, by rfl⟩ : syracuseStep 1377371 = 2066057) B2066057
theorem B37749959 : Blo 916578 37749959 := bstep (se 1 (by rfl) ⟨28312469, by rfl⟩ : syracuseStep 37749959 = 56624939) B56624939
theorem B918847 : Blo 916578 918847 := bstep (se 1 (by rfl) ⟨689135, by rfl⟩ : syracuseStep 918847 = 1378271) B1378271
theorem B1377647 : Blo 916578 1377647 := bstep (se 1 (by rfl) ⟨1033235, by rfl⟩ : syracuseStep 1377647 = 2066471) B2066471
theorem B918911 : Blo 916578 918911 := bstep (se 1 (by rfl) ⟨689183, by rfl⟩ : syracuseStep 918911 = 1378367) B1378367
theorem B1377695 : Blo 916578 1377695 := bstep (se 1 (by rfl) ⟨1033271, by rfl⟩ : syracuseStep 1377695 = 2066543) B2066543
theorem B919199 : Blo 916578 919199 := bstep (se 1 (by rfl) ⟨689399, by rfl⟩ : syracuseStep 919199 = 1378799) B1378799
theorem B919295 : Blo 916578 919295 := bstep (se 1 (by rfl) ⟨689471, by rfl⟩ : syracuseStep 919295 = 1378943) B1378943
theorem B11765513 : Blo 916578 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B17631047 : Blo 916578 17631047 := bstep (se 1 (by rfl) ⟨13223285, by rfl⟩ : syracuseStep 17631047 = 26446571) B26446571
theorem B919387 : Blo 916578 919387 := bstep (se 1 (by rfl) ⟨689540, by rfl⟩ : syracuseStep 919387 = 1379081) B1379081
theorem B1378331 : Blo 916578 1378331 := bstep (se 1 (by rfl) ⟨1033748, by rfl⟩ : syracuseStep 1378331 = 2067497) B2067497
theorem B2328659 : Blo 916578 2328659 := bstep (se 1 (by rfl) ⟨1746494, by rfl⟩ : syracuseStep 2328659 = 3492989) B3492989
theorem B2066651 : Blo 916578 2066651 := bstep (se 1 (by rfl) ⟨1549988, by rfl⟩ : syracuseStep 2066651 = 3099977) B3099977
theorem B6981875 : Blo 916578 6981875 := bstep (se 1 (by rfl) ⟨5236406, by rfl⟩ : syracuseStep 6981875 = 10472813) B10472813
theorem B4655555 : Blo 916578 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B18876887 : Blo 916578 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B1378871 : Blo 916578 1378871 := bstep (se 1 (by rfl) ⟨1034153, by rfl⟩ : syracuseStep 1378871 = 2068307) B2068307
theorem B2067731 : Blo 916578 2067731 := bstep (se 1 (by rfl) ⟨1550798, by rfl⟩ : syracuseStep 2067731 = 3101597) B3101597
theorem B1380047 : Blo 916578 1380047 := bstep (se 1 (by rfl) ⟨1035035, by rfl⟩ : syracuseStep 1380047 = 2070071) B2070071
theorem B150638615 : Blo 916578 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B8393341 : Blo 916578 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B2069225 : Blo 916578 2069225 := bstep (se 2 (by rfl) ⟨775959, by rfl⟩ : syracuseStep 2069225 = 1551919) B1551919
theorem B2069369 : Blo 916578 2069369 := bstep (se 2 (by rfl) ⟨776013, by rfl⟩ : syracuseStep 2069369 = 1552027) B1552027
theorem B1741915 : Blo 916578 1741915 := bstep (se 1 (by rfl) ⟨1306436, by rfl⟩ : syracuseStep 1741915 = 2612873) B2612873
theorem B19863305 : Blo 916578 19863305 := bstep (se 2 (by rfl) ⟨7448739, by rfl⟩ : syracuseStep 19863305 = 14897479) B14897479
theorem B2070575 : Blo 916578 2070575 := bstep (se 1 (by rfl) ⟨1552931, by rfl⟩ : syracuseStep 2070575 = 3105863) B3105863
theorem B2070719 : Blo 916578 2070719 := bstep (se 1 (by rfl) ⟨1553039, by rfl⟩ : syracuseStep 2070719 = 3106079) B3106079
theorem B2202959 : Blo 916578 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B2825855 : Blo 916578 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B4955879 : Blo 916578 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B1548335 : Blo 916578 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B7151723 : Blo 916578 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B1548571 : Blo 916578 1548571 := bstep (se 1 (by rfl) ⟨1161428, by rfl⟩ : syracuseStep 1548571 = 2322857) B2322857
theorem B1548713 : Blo 916578 1548713 := bstep (se 2 (by rfl) ⟨580767, by rfl⟩ : syracuseStep 1548713 = 1161535) B1161535
theorem B2827433 : Blo 916578 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B1746107 : Blo 916578 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B1550063 : Blo 916578 1550063 := bstep (se 1 (by rfl) ⟨1162547, by rfl⟩ : syracuseStep 1550063 = 2325095) B2325095
theorem B7842035 : Blo 916578 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B3484073 : Blo 916578 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B1551055 : Blo 916578 1551055 := bstep (se 1 (by rfl) ⟨1163291, by rfl⟩ : syracuseStep 1551055 = 2326583) B2326583
theorem B1552297 : Blo 916578 1552297 := bstep (se 2 (by rfl) ⟨582111, by rfl⟩ : syracuseStep 1552297 = 1164223) B1164223
theorem B726413417 : Blo 916578 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B13414691 : Blo 916578 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B3486199 : Blo 916578 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B3486503 : Blo 916578 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B3095009 : Blo 916578 3095009 := bstep (se 2 (by rfl) ⟨1160628, by rfl⟩ : syracuseStep 3095009 = 2321257) B2321257
theorem B3488447 : Blo 916578 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B1162183 : Blo 916578 1162183 := bstep (se 1 (by rfl) ⟨871637, by rfl⟩ : syracuseStep 1162183 = 1743275) B1743275
theorem B3095549 : Blo 916578 3095549 := bstep (se 3 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 3095549 = 1160831) B1160831
theorem B18103439 : Blo 916578 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B4406687 : Blo 916578 4406687 := bstep (se 1 (by rfl) ⟨3305015, by rfl⟩ : syracuseStep 4406687 = 6610031) B6610031
theorem B1032943 : Blo 916578 1032943 := bstep (se 1 (by rfl) ⟨774707, by rfl⟩ : syracuseStep 1032943 = 1549415) B1549415
theorem B3097331 : Blo 916578 3097331 := bstep (se 1 (by rfl) ⟨2322998, by rfl⟩ : syracuseStep 3097331 = 4645997) B4645997
theorem B1328297 : Blo 916578 1328297 := bstep (se 2 (by rfl) ⟨498111, by rfl⟩ : syracuseStep 1328297 = 996223) B996223
theorem B1033663 : Blo 916578 1033663 := bstep (se 1 (by rfl) ⟨775247, by rfl⟩ : syracuseStep 1033663 = 1550495) B1550495
theorem B1164775 : Blo 916578 1164775 := bstep (se 1 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 1164775 = 1747163) B1747163
theorem B5589767 : Blo 916578 5589767 := bstep (se 1 (by rfl) ⟨4192325, by rfl⟩ : syracuseStep 5589767 = 8384651) B8384651
theorem B4410359 : Blo 916578 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B15912065 : Blo 916578 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B4705609 : Blo 916578 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B26496395 : Blo 916578 26496395 := bstep (se 1 (by rfl) ⟨19872296, by rfl⟩ : syracuseStep 26496395 = 39744593) B39744593
theorem B5231897 : Blo 916578 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B10475729 : Blo 916578 10475729 := bstep (se 2 (by rfl) ⟨3928398, by rfl⟩ : syracuseStep 10475729 = 7856797) B7856797
theorem B6609107 : Blo 916578 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B1105435 : Blo 916578 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B15720155 : Blo 916578 15720155 := bstep (se 1 (by rfl) ⟨11790116, by rfl⟩ : syracuseStep 15720155 = 23580233) B23580233
theorem B1957775 : Blo 916578 1957775 := bstep (se 1 (by rfl) ⟨1468331, by rfl⟩ : syracuseStep 1957775 = 2936663) B2936663
theorem B1958015 : Blo 916578 1958015 := bstep (se 1 (by rfl) ⟨1468511, by rfl⟩ : syracuseStep 1958015 = 2937023) B2937023
theorem B32202967 : Blo 916578 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B4645187 : Blo 916578 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B4645673 : Blo 916578 4645673 := bstep (se 2 (by rfl) ⟨1742127, by rfl⟩ : syracuseStep 4645673 = 3484255) B3484255
theorem B10446569 : Blo 916578 10446569 := bstep (se 2 (by rfl) ⟨3917463, by rfl⟩ : syracuseStep 10446569 = 7834927) B7834927
theorem B1959707 : Blo 916578 1959707 := bstep (se 1 (by rfl) ⟨1469780, by rfl⟩ : syracuseStep 1959707 = 2939561) B2939561
theorem B944191 : Blo 916578 944191 := bstep (se 1 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 944191 = 1416287) B1416287
theorem B1468793 : Blo 916578 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B3926657 : Blo 916578 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B12544787 : Blo 916578 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B4648427 : Blo 916578 4648427 := bstep (se 1 (by rfl) ⟨3486320, by rfl⟩ : syracuseStep 4648427 = 6972641) B6972641
theorem B28340063 : Blo 916578 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B1864019 : Blo 916578 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B119042783 : Blo 916578 119042783 := bstep (se 1 (by rfl) ⟨89282087, by rfl⟩ : syracuseStep 119042783 = 178564175) B178564175
theorem B12580205 : Blo 916578 12580205 := bstep (se 3 (by rfl) ⟨2358788, by rfl⟩ : syracuseStep 12580205 = 4717577) B4717577
theorem B24540889 : Blo 916578 24540889 := bstep (se 2 (by rfl) ⟨9202833, by rfl⟩ : syracuseStep 24540889 = 18405667) B18405667
theorem B4651343 : Blo 916578 4651343 := bstep (se 1 (by rfl) ⟨3488507, by rfl⟩ : syracuseStep 4651343 = 6977015) B6977015
theorem B3930707 : Blo 916578 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B1374875 : Blo 916578 1374875 := bstep (se 1 (by rfl) ⟨1031156, by rfl⟩ : syracuseStep 1374875 = 2062313) B2062313
theorem B1374971 : Blo 916578 1374971 := bstep (se 1 (by rfl) ⟨1031228, by rfl⟩ : syracuseStep 1374971 = 2062457) B2062457
theorem B1375097 : Blo 916578 1375097 := bstep (se 2 (by rfl) ⟨515661, by rfl⟩ : syracuseStep 1375097 = 1031323) B1031323
theorem B4652477 : Blo 916578 4652477 := bstep (se 3 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 4652477 = 1744679) B1744679
theorem B7863905 : Blo 916578 7863905 := bstep (se 2 (by rfl) ⟨2948964, by rfl⟩ : syracuseStep 7863905 = 5897929) B5897929
theorem B2064239 : Blo 916578 2064239 := bstep (se 1 (by rfl) ⟨1548179, by rfl⟩ : syracuseStep 2064239 = 3096359) B3096359
theorem B917487 : Blo 916578 917487 := bstep (se 1 (by rfl) ⟨688115, by rfl⟩ : syracuseStep 917487 = 1376231) B1376231
theorem B1376249 : Blo 916578 1376249 := bstep (se 2 (by rfl) ⟨516093, by rfl⟩ : syracuseStep 1376249 = 1032187) B1032187
theorem B4718735 : Blo 916578 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B917831 : Blo 916578 917831 := bstep (se 1 (by rfl) ⟨688373, by rfl⟩ : syracuseStep 917831 = 1376747) B1376747
theorem B77660507 : Blo 916578 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B2064761 : Blo 916578 2064761 := bstep (se 2 (by rfl) ⟨774285, by rfl⟩ : syracuseStep 2064761 = 1548571) B1548571
theorem B2064887 : Blo 916578 2064887 := bstep (se 1 (by rfl) ⟨1548665, by rfl⟩ : syracuseStep 2064887 = 3097331) B3097331
theorem B918247 : Blo 916578 918247 := bstep (se 1 (by rfl) ⟨688685, by rfl⟩ : syracuseStep 918247 = 1377371) B1377371
theorem B25166639 : Blo 916578 25166639 := bstep (se 1 (by rfl) ⟨18874979, by rfl⟩ : syracuseStep 25166639 = 37749959) B37749959
theorem B918431 : Blo 916578 918431 := bstep (se 1 (by rfl) ⟨688823, by rfl⟩ : syracuseStep 918431 = 1377647) B1377647
theorem B918463 : Blo 916578 918463 := bstep (se 1 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 918463 = 1377695) B1377695
theorem B1377257 : Blo 916578 1377257 := bstep (se 2 (by rfl) ⟨516471, by rfl⟩ : syracuseStep 1377257 = 1032943) B1032943
theorem B918887 : Blo 916578 918887 := bstep (se 1 (by rfl) ⟨689165, by rfl⟩ : syracuseStep 918887 = 1378331) B1378331
theorem B42993077 : Blo 916578 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B1377767 : Blo 916578 1377767 := bstep (se 1 (by rfl) ⟨1033325, by rfl⟩ : syracuseStep 1377767 = 2066651) B2066651
theorem B4654583 : Blo 916578 4654583 := bstep (se 1 (by rfl) ⟨3490937, by rfl⟩ : syracuseStep 4654583 = 6981875) B6981875
theorem B12584591 : Blo 916578 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B919247 : Blo 916578 919247 := bstep (se 1 (by rfl) ⟨689435, by rfl⟩ : syracuseStep 919247 = 1378871) B1378871
theorem B1378217 : Blo 916578 1378217 := bstep (se 2 (by rfl) ⟨516831, by rfl⟩ : syracuseStep 1378217 = 1033663) B1033663
theorem B1378487 : Blo 916578 1378487 := bstep (se 1 (by rfl) ⟨1033865, by rfl⟩ : syracuseStep 1378487 = 2067731) B2067731
theorem B17664263 : Blo 916578 17664263 := bstep (se 1 (by rfl) ⟨13248197, by rfl⟩ : syracuseStep 17664263 = 26496395) B26496395
theorem B920031 : Blo 916578 920031 := bstep (se 1 (by rfl) ⟨690023, by rfl⟩ : syracuseStep 920031 = 1380047) B1380047
theorem B3542125 : Blo 916578 3542125 := bstep (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) B1328297
theorem B1379483 : Blo 916578 1379483 := bstep (se 1 (by rfl) ⟨1034612, by rfl⟩ : syracuseStep 1379483 = 2069225) B2069225
theorem B1379579 : Blo 916578 1379579 := bstep (se 1 (by rfl) ⟨1034684, by rfl⟩ : syracuseStep 1379579 = 2069369) B2069369
theorem B2068073 : Blo 916578 2068073 := bstep (se 2 (by rfl) ⟨775527, by rfl⟩ : syracuseStep 2068073 = 1551055) B1551055
theorem B13242203 : Blo 916578 13242203 := bstep (se 1 (by rfl) ⟨9931652, by rfl⟩ : syracuseStep 13242203 = 19863305) B19863305
theorem B1380383 : Blo 916578 1380383 := bstep (se 1 (by rfl) ⟨1035287, by rfl⟩ : syracuseStep 1380383 = 2070575) B2070575
theorem B1380479 : Blo 916578 1380479 := bstep (se 1 (by rfl) ⟨1035359, by rfl⟩ : syracuseStep 1380479 = 2070719) B2070719
theorem B6983819 : Blo 916578 6983819 := bstep (se 1 (by rfl) ⟨5237864, by rfl⟩ : syracuseStep 6983819 = 10475729) B10475729
theorem B2069729 : Blo 916578 2069729 := bstep (se 2 (by rfl) ⟨776148, by rfl⟩ : syracuseStep 2069729 = 1552297) B1552297
theorem B8363191 : Blo 916578 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B48275837 : Blo 916578 48275837 := bstep (se 3 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 48275837 = 18103439) B18103439
theorem B1549577 : Blo 916578 1549577 := bstep (se 2 (by rfl) ⟨581091, by rfl⟩ : syracuseStep 1549577 = 1162183) B1162183
theorem B5220733 : Blo 916578 5220733 := bstep (se 3 (by rfl) ⟨978887, by rfl⟩ : syracuseStep 5220733 = 1957775) B1957775
theorem B3189583 : Blo 916578 3189583 := bstep (se 1 (by rfl) ⟨2392187, by rfl⟩ : syracuseStep 3189583 = 4784375) B4784375
theorem B42937289 : Blo 916578 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B7843675 : Blo 916578 7843675 := bstep (se 1 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 7843675 = 11765513) B11765513
theorem B1552439 : Blo 916578 1552439 := bstep (se 1 (by rfl) ⟨1164329, by rfl⟩ : syracuseStep 1552439 = 2328659) B2328659
theorem B1553033 : Blo 916578 1553033 := bstep (se 2 (by rfl) ⟨582387, by rfl⟩ : syracuseStep 1553033 = 1164775) B1164775
theorem B1258921 : Blo 916578 1258921 := bstep (se 2 (by rfl) ⟨472095, by rfl⟩ : syracuseStep 1258921 = 944191) B944191
theorem B3487931 : Blo 916578 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B4406071 : Blo 916578 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B6274145 : Blo 916578 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1883903 : Blo 916578 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B1032223 : Blo 916578 1032223 := bstep (se 1 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 1032223 = 1548335) B1548335
theorem B4767815 : Blo 916578 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B3096791 : Blo 916578 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B1032475 : Blo 916578 1032475 := bstep (se 1 (by rfl) ⟨774356, by rfl⟩ : syracuseStep 1032475 = 1548713) B1548713
theorem B3097115 : Blo 916578 3097115 := bstep (se 1 (by rfl) ⟨2322836, by rfl⟩ : syracuseStep 3097115 = 4645673) B4645673
theorem B1884955 : Blo 916578 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B1164071 : Blo 916578 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B11191121 : Blo 916578 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B3916781 : Blo 916578 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B6964379 : Blo 916578 6964379 := bstep (se 1 (by rfl) ⟨5223284, by rfl⟩ : syracuseStep 6964379 = 10446569) B10446569
theorem B1033375 : Blo 916578 1033375 := bstep (se 1 (by rfl) ⟨775031, by rfl⟩ : syracuseStep 1033375 = 1550063) B1550063
theorem B5228023 : Blo 916578 5228023 := bstep (se 1 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 5228023 = 7842035) B7842035
theorem B32721185 : Blo 916578 32721185 := bstep (se 2 (by rfl) ⟨12270444, by rfl⟩ : syracuseStep 32721185 = 24540889) B24540889
theorem B3098951 : Blo 916578 3098951 := bstep (se 1 (by rfl) ⟨2324213, by rfl⟩ : syracuseStep 3098951 = 4648427) B4648427
theorem B18893375 : Blo 916578 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B3100895 : Blo 916578 3100895 := bstep (se 1 (by rfl) ⟨2325671, by rfl⟩ : syracuseStep 3100895 = 4651343) B4651343
theorem B2937791 : Blo 916578 2937791 := bstep (se 1 (by rfl) ⟨2203343, by rfl⟩ : syracuseStep 2937791 = 4406687) B4406687
theorem B3101651 : Blo 916578 3101651 := bstep (se 1 (by rfl) ⟨2326238, by rfl⟩ : syracuseStep 3101651 = 4652477) B4652477
theorem B35772509 : Blo 916578 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B4970717 : Blo 916578 4970717 := bstep (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) B1864019
theorem B11754031 : Blo 916578 11754031 := bstep (se 1 (by rfl) ⟨8815523, by rfl⟩ : syracuseStep 11754031 = 17631047) B17631047
theorem B3103703 : Blo 916578 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B2940239 : Blo 916578 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B100425743 : Blo 916578 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B33547213 : Blo 916578 33547213 := bstep (se 3 (by rfl) ⟨6290102, by rfl⟩ : syracuseStep 33547213 = 12580205) B12580205
theorem B1468639 : Blo 916578 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B10480103 : Blo 916578 10480103 := bstep (se 1 (by rfl) ⟨7860077, by rfl⟩ : syracuseStep 10480103 = 15720155) B15720155
theorem B3303919 : Blo 916578 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B1305343 : Blo 916578 1305343 := bstep (se 1 (by rfl) ⟨979007, by rfl⟩ : syracuseStep 1305343 = 1958015) B1958015
theorem B4648265 : Blo 916578 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B1306471 : Blo 916578 1306471 := bstep (se 1 (by rfl) ⟨979853, by rfl⟩ : syracuseStep 1306471 = 1959707) B1959707
theorem B2322553 : Blo 916578 2322553 := bstep (se 2 (by rfl) ⟨870957, by rfl⟩ : syracuseStep 2322553 = 1741915) B1741915
theorem B2322715 : Blo 916578 2322715 := bstep (se 1 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 2322715 = 3484073) B3484073
theorem B2617771 : Blo 916578 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B14906045 : Blo 916578 14906045 := bstep (se 3 (by rfl) ⟨2794883, by rfl⟩ : syracuseStep 14906045 = 5589767) B5589767
theorem B484275611 : Blo 916578 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B42432173 : Blo 916578 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B79361855 : Blo 916578 79361855 := bstep (se 1 (by rfl) ⟨59521391, by rfl⟩ : syracuseStep 79361855 = 119042783) B119042783
theorem B2324335 : Blo 916578 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B2063339 : Blo 916578 2063339 := bstep (se 1 (by rfl) ⟨1547504, by rfl⟩ : syracuseStep 2063339 = 3095009) B3095009
theorem B2620471 : Blo 916578 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B916583 : Blo 916578 916583 := bstep (se 1 (by rfl) ⟨687437, by rfl⟩ : syracuseStep 916583 = 1374875) B1374875
theorem B2325631 : Blo 916578 2325631 := bstep (se 1 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 2325631 = 3488447) B3488447
theorem B916647 : Blo 916578 916647 := bstep (se 1 (by rfl) ⟨687485, by rfl⟩ : syracuseStep 916647 = 1374971) B1374971
theorem B916731 : Blo 916578 916731 := bstep (se 1 (by rfl) ⟨687548, by rfl⟩ : syracuseStep 916731 = 1375097) B1375097
theorem B2063699 : Blo 916578 2063699 := bstep (se 1 (by rfl) ⟨1547774, by rfl⟩ : syracuseStep 2063699 = 3095549) B3095549
theorem B1473913 : Blo 916578 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B5242603 : Blo 916578 5242603 := bstep (se 1 (by rfl) ⟨3931952, by rfl⟩ : syracuseStep 5242603 = 7863905) B7863905
theorem B1376159 : Blo 916578 1376159 := bstep (se 1 (by rfl) ⟨1032119, by rfl⟩ : syracuseStep 1376159 = 2064239) B2064239
theorem B917499 : Blo 916578 917499 := bstep (se 1 (by rfl) ⟨688124, by rfl⟩ : syracuseStep 917499 = 1376249) B1376249
theorem B1376297 : Blo 916578 1376297 := bstep (se 2 (by rfl) ⟨516111, by rfl⟩ : syracuseStep 1376297 = 1032223) B1032223
theorem B3178543 : Blo 916578 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B3145823 : Blo 916578 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B2064527 : Blo 916578 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B51773671 : Blo 916578 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B1376507 : Blo 916578 1376507 := bstep (se 1 (by rfl) ⟨1032380, by rfl⟩ : syracuseStep 1376507 = 2064761) B2064761
theorem B1376591 : Blo 916578 1376591 := bstep (se 1 (by rfl) ⟨1032443, by rfl⟩ : syracuseStep 1376591 = 2064887) B2064887
theorem B2064743 : Blo 916578 2064743 := bstep (se 1 (by rfl) ⟨1548557, by rfl⟩ : syracuseStep 2064743 = 3097115) B3097115
theorem B1376633 : Blo 916578 1376633 := bstep (se 2 (by rfl) ⟨516237, by rfl⟩ : syracuseStep 1376633 = 1032475) B1032475
theorem B16777759 : Blo 916578 16777759 := bstep (se 1 (by rfl) ⟨12583319, by rfl⟩ : syracuseStep 16777759 = 25166639) B25166639
theorem B918171 : Blo 916578 918171 := bstep (se 1 (by rfl) ⟨688628, by rfl⟩ : syracuseStep 918171 = 1377257) B1377257
theorem B918511 : Blo 916578 918511 := bstep (se 1 (by rfl) ⟨688883, by rfl⟩ : syracuseStep 918511 = 1377767) B1377767
theorem B8389727 : Blo 916578 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B44729617 : Blo 916578 44729617 := bstep (se 2 (by rfl) ⟨16773606, by rfl⟩ : syracuseStep 44729617 = 33547213) B33547213
theorem B918811 : Blo 916578 918811 := bstep (se 1 (by rfl) ⟨689108, by rfl⟩ : syracuseStep 918811 = 1378217) B1378217
theorem B918991 : Blo 916578 918991 := bstep (se 1 (by rfl) ⟨689243, by rfl⟩ : syracuseStep 918991 = 1378487) B1378487
theorem B1377833 : Blo 916578 1377833 := bstep (se 2 (by rfl) ⟨516687, by rfl⟩ : syracuseStep 1377833 = 1033375) B1033375
theorem B2065967 : Blo 916578 2065967 := bstep (se 1 (by rfl) ⟨1549475, by rfl⟩ : syracuseStep 2065967 = 3098951) B3098951
theorem B919655 : Blo 916578 919655 := bstep (se 1 (by rfl) ⟨689741, by rfl⟩ : syracuseStep 919655 = 1379483) B1379483
theorem B919719 : Blo 916578 919719 := bstep (se 1 (by rfl) ⟨689789, by rfl⟩ : syracuseStep 919719 = 1379579) B1379579
theorem B1378715 : Blo 916578 1378715 := bstep (se 1 (by rfl) ⟨1034036, by rfl⟩ : syracuseStep 1378715 = 2068073) B2068073
theorem B920255 : Blo 916578 920255 := bstep (se 1 (by rfl) ⟨690191, by rfl⟩ : syracuseStep 920255 = 1380383) B1380383
theorem B920319 : Blo 916578 920319 := bstep (se 1 (by rfl) ⟨690239, by rfl⟩ : syracuseStep 920319 = 1380479) B1380479
theorem B4655879 : Blo 916578 4655879 := bstep (se 1 (by rfl) ⟨3491909, by rfl⟩ : syracuseStep 4655879 = 6983819) B6983819
theorem B2067263 : Blo 916578 2067263 := bstep (se 1 (by rfl) ⟨1550447, by rfl⟩ : syracuseStep 2067263 = 3100895) B3100895
theorem B2067767 : Blo 916578 2067767 := bstep (se 1 (by rfl) ⟨1550825, by rfl⟩ : syracuseStep 2067767 = 3101651) B3101651
theorem B1379819 : Blo 916578 1379819 := bstep (se 1 (by rfl) ⟨1034864, by rfl⟩ : syracuseStep 1379819 = 2069729) B2069729
theorem B1740457 : Blo 916578 1740457 := bstep (se 2 (by rfl) ⟨652671, by rfl⟩ : syracuseStep 1740457 = 1305343) B1305343
theorem B4722833 : Blo 916578 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B3313811 : Blo 916578 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B17011109 : Blo 916578 17011109 := bstep (se 4 (by rfl) ⟨1594791, by rfl⟩ : syracuseStep 17011109 = 3189583) B3189583
theorem B2069135 : Blo 916578 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B10458233 : Blo 916578 10458233 := bstep (se 2 (by rfl) ⟨3921837, by rfl⟩ : syracuseStep 10458233 = 7843675) B7843675
theorem B1741961 : Blo 916578 1741961 := bstep (se 2 (by rfl) ⟨653235, by rfl⟩ : syracuseStep 1741961 = 1306471) B1306471
theorem B66950495 : Blo 916578 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B32183891 : Blo 916578 32183891 := bstep (se 1 (by rfl) ⟨24137918, by rfl⟩ : syracuseStep 32183891 = 48275837) B48275837
theorem B6986735 : Blo 916578 6986735 := bstep (se 1 (by rfl) ⟨5240051, by rfl⟩ : syracuseStep 6986735 = 10480103) B10480103
theorem B9937363 : Blo 916578 9937363 := bstep (se 1 (by rfl) ⟨7453022, by rfl⟩ : syracuseStep 9937363 = 14906045) B14906045
theorem B15672041 : Blo 916578 15672041 := bstep (se 2 (by rfl) ⟨5877015, by rfl⟩ : syracuseStep 15672041 = 11754031) B11754031
theorem B7840637 : Blo 916578 7840637 := bstep (se 3 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 7840637 = 2940239) B2940239
theorem B5874761 : Blo 916578 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B28288115 : Blo 916578 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B11150921 : Blo 916578 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B5023741 : Blo 916578 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B6990137 : Blo 916578 6990137 := bstep (se 2 (by rfl) ⟨2621301, by rfl⟩ : syracuseStep 6990137 = 5242603) B5242603
theorem B11776175 : Blo 916578 11776175 := bstep (se 1 (by rfl) ⟨8832131, by rfl⟩ : syracuseStep 11776175 = 17664263) B17664263
theorem B12595583 : Blo 916578 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B8828135 : Blo 916578 8828135 := bstep (se 1 (by rfl) ⟨6621101, by rfl⟩ : syracuseStep 8828135 = 13242203) B13242203
theorem B6960977 : Blo 916578 6960977 := bstep (se 2 (by rfl) ⟨2610366, by rfl⟩ : syracuseStep 6960977 = 5220733) B5220733
theorem B1291401629 : Blo 916578 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B3096737 : Blo 916578 3096737 := bstep (se 2 (by rfl) ⟨1161276, by rfl⟩ : syracuseStep 3096737 = 2322553) B2322553
theorem B3096953 : Blo 916578 3096953 := bstep (se 2 (by rfl) ⟨1161357, by rfl⟩ : syracuseStep 3096953 = 2322715) B2322715
theorem B3490361 : Blo 916578 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B1033051 : Blo 916578 1033051 := bstep (se 1 (by rfl) ⟨774788, by rfl⟩ : syracuseStep 1033051 = 1549577) B1549577
theorem B28624859 : Blo 916578 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B3098843 : Blo 916578 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B3099113 : Blo 916578 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B1034959 : Blo 916578 1034959 := bstep (se 1 (by rfl) ⟨776219, by rfl⟩ : syracuseStep 1034959 = 1552439) B1552439
theorem B1035355 : Blo 916578 1035355 := bstep (se 1 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 1035355 = 1553033) B1553033
theorem B52907903 : Blo 916578 52907903 := bstep (se 1 (by rfl) ⟨39680927, by rfl⟩ : syracuseStep 52907903 = 79361855) B79361855
theorem B3493961 : Blo 916578 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B3100841 : Blo 916578 3100841 := bstep (se 2 (by rfl) ⟨1162815, by rfl⟩ : syracuseStep 3100841 = 2325631) B2325631
theorem B4182763 : Blo 916578 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B7460747 : Blo 916578 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B2611187 : Blo 916578 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B4642919 : Blo 916578 4642919 := bstep (se 1 (by rfl) ⟨3482189, by rfl⟩ : syracuseStep 4642919 = 6964379) B6964379
theorem B3103055 : Blo 916578 3103055 := bstep (se 1 (by rfl) ⟨2327291, by rfl⟩ : syracuseStep 3103055 = 4654583) B4654583
theorem B2513273 : Blo 916578 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B21814123 : Blo 916578 21814123 := bstep (se 1 (by rfl) ⟨16360592, by rfl⟩ : syracuseStep 21814123 = 32721185) B32721185
theorem B6970697 : Blo 916578 6970697 := bstep (se 2 (by rfl) ⟨2614011, by rfl⟩ : syracuseStep 6970697 = 5228023) B5228023
theorem B3104189 : Blo 916578 3104189 := bstep (se 3 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 3104189 = 1164071) B1164071
theorem B17620901 : Blo 916578 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B1958185 : Blo 916578 1958185 := bstep (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) B1468639
theorem B1958527 : Blo 916578 1958527 := bstep (se 1 (by rfl) ⟨1468895, by rfl⟩ : syracuseStep 1958527 = 2937791) B2937791
theorem B114648205 : Blo 916578 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B23848339 : Blo 916578 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B6714245 : Blo 916578 6714245 := bstep (se 4 (by rfl) ⟨629460, by rfl⟩ : syracuseStep 6714245 = 1258921) B1258921
theorem B2325287 : Blo 916578 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B1965217 : Blo 916578 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1375559 : Blo 916578 1375559 := bstep (se 1 (by rfl) ⟨1031669, by rfl⟩ : syracuseStep 1375559 = 2063339) B2063339
theorem B1375799 : Blo 916578 1375799 := bstep (se 1 (by rfl) ⟨1031849, by rfl⟩ : syracuseStep 1375799 = 2063699) B2063699
theorem B917439 : Blo 916578 917439 := bstep (se 1 (by rfl) ⟨688079, by rfl⟩ : syracuseStep 917439 = 1376159) B1376159
theorem B917531 : Blo 916578 917531 := bstep (se 1 (by rfl) ⟨688148, by rfl⟩ : syracuseStep 917531 = 1376297) B1376297
theorem B2097215 : Blo 916578 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B1376351 : Blo 916578 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B2064491 : Blo 916578 2064491 := bstep (se 1 (by rfl) ⟨1548368, by rfl⟩ : syracuseStep 2064491 = 3096737) B3096737
theorem B917671 : Blo 916578 917671 := bstep (se 1 (by rfl) ⟨688253, by rfl⟩ : syracuseStep 917671 = 1376507) B1376507
theorem B917727 : Blo 916578 917727 := bstep (se 1 (by rfl) ⟨688295, by rfl⟩ : syracuseStep 917727 = 1376591) B1376591
theorem B1376495 : Blo 916578 1376495 := bstep (se 1 (by rfl) ⟨1032371, by rfl⟩ : syracuseStep 1376495 = 2064743) B2064743
theorem B2064635 : Blo 916578 2064635 := bstep (se 1 (by rfl) ⟨1548476, by rfl⟩ : syracuseStep 2064635 = 3096953) B3096953
theorem B917755 : Blo 916578 917755 := bstep (se 1 (by rfl) ⟨688316, by rfl⟩ : syracuseStep 917755 = 1376633) B1376633
theorem B2326907 : Blo 916578 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B918555 : Blo 916578 918555 := bstep (se 1 (by rfl) ⟨688916, by rfl⟩ : syracuseStep 918555 = 1377833) B1377833
theorem B1377311 : Blo 916578 1377311 := bstep (se 1 (by rfl) ⟨1032983, by rfl⟩ : syracuseStep 1377311 = 2065967) B2065967
theorem B1377401 : Blo 916578 1377401 := bstep (se 2 (by rfl) ⟨516525, by rfl⟩ : syracuseStep 1377401 = 1033051) B1033051
theorem B2065895 : Blo 916578 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B152864273 : Blo 916578 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B919143 : Blo 916578 919143 := bstep (se 1 (by rfl) ⟨689357, by rfl⟩ : syracuseStep 919143 = 1378715) B1378715
theorem B2066075 : Blo 916578 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B59639489 : Blo 916578 59639489 := bstep (se 2 (by rfl) ⟨22364808, by rfl⟩ : syracuseStep 59639489 = 44729617) B44729617
theorem B1378175 : Blo 916578 1378175 := bstep (se 1 (by rfl) ⟨1033631, by rfl⟩ : syracuseStep 1378175 = 2067263) B2067263
theorem B1378511 : Blo 916578 1378511 := bstep (se 1 (by rfl) ⟨1033883, by rfl⟩ : syracuseStep 1378511 = 2067767) B2067767
theorem B919879 : Blo 916578 919879 := bstep (se 1 (by rfl) ⟨689909, by rfl⟩ : syracuseStep 919879 = 1379819) B1379819
theorem B2329307 : Blo 916578 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B3148555 : Blo 916578 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B2067227 : Blo 916578 2067227 := bstep (se 1 (by rfl) ⟨1550420, by rfl⟩ : syracuseStep 2067227 = 3100841) B3100841
theorem B11340739 : Blo 916578 11340739 := bstep (se 1 (by rfl) ⟨8505554, by rfl⟩ : syracuseStep 11340739 = 17011109) B17011109
theorem B1379423 : Blo 916578 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B44633663 : Blo 916578 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B1379945 : Blo 916578 1379945 := bstep (se 2 (by rfl) ⟨517479, by rfl⟩ : syracuseStep 1379945 = 1034959) B1034959
theorem B26808245 : Blo 916578 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B1740791 : Blo 916578 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B1380473 : Blo 916578 1380473 := bstep (se 2 (by rfl) ⟨517677, by rfl⟩ : syracuseStep 1380473 = 1035355) B1035355
theorem B2068703 : Blo 916578 2068703 := bstep (se 1 (by rfl) ⟨1551527, by rfl⟩ : syracuseStep 2068703 = 3103055) B3103055
theorem B4657823 : Blo 916578 4657823 := bstep (se 1 (by rfl) ⟨3493367, by rfl⟩ : syracuseStep 4657823 = 6986735) B6986735
theorem B2069459 : Blo 916578 2069459 := bstep (se 1 (by rfl) ⟨1552094, by rfl⟩ : syracuseStep 2069459 = 3104189) B3104189
theorem B5577017 : Blo 916578 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B4660091 : Blo 916578 4660091 := bstep (se 1 (by rfl) ⟨3495068, by rfl⟩ : syracuseStep 4660091 = 6990137) B6990137
theorem B8397055 : Blo 916578 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B1550191 : Blo 916578 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B4238057 : Blo 916578 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B13249817 : Blo 916578 13249817 := bstep (se 2 (by rfl) ⟨4968681, by rfl⟩ : syracuseStep 13249817 = 9937363) B9937363
theorem B19083239 : Blo 916578 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B31797785 : Blo 916578 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B35271935 : Blo 916578 35271935 := bstep (se 1 (by rfl) ⟨26453951, by rfl⟩ : syracuseStep 35271935 = 52907903) B52907903
theorem B6698321 : Blo 916578 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B2209207 : Blo 916578 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B1161307 : Blo 916578 1161307 := bstep (se 1 (by rfl) ⟨870980, by rfl⟩ : syracuseStep 1161307 = 1741961) B1741961
theorem B3095279 : Blo 916578 3095279 := bstep (se 1 (by rfl) ⟨2321459, by rfl⟩ : syracuseStep 3095279 = 4642919) B4642919
theorem B11747267 : Blo 916578 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B5227091 : Blo 916578 5227091 := bstep (se 1 (by rfl) ⟨3920318, by rfl⟩ : syracuseStep 5227091 = 7840637) B7840637
theorem B3916507 : Blo 916578 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B18858743 : Blo 916578 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B7850783 : Blo 916578 7850783 := bstep (se 1 (by rfl) ⟨5888087, by rfl⟩ : syracuseStep 7850783 = 11776175) B11776175
theorem B4476163 : Blo 916578 4476163 := bstep (se 1 (by rfl) ⟨3357122, by rfl⟩ : syracuseStep 4476163 = 6714245) B6714245
theorem B5885423 : Blo 916578 5885423 := bstep (se 1 (by rfl) ⟨4414067, by rfl⟩ : syracuseStep 5885423 = 8828135) B8828135
theorem B29085497 : Blo 916578 29085497 := bstep (se 2 (by rfl) ⟨10907061, by rfl⟩ : syracuseStep 29085497 = 21814123) B21814123
theorem B4640651 : Blo 916578 4640651 := bstep (se 1 (by rfl) ⟨3480488, by rfl⟩ : syracuseStep 4640651 = 6960977) B6960977
theorem B860934419 : Blo 916578 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B69031561 : Blo 916578 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B22370345 : Blo 916578 22370345 := bstep (se 2 (by rfl) ⟨8388879, by rfl⟩ : syracuseStep 22370345 = 16777759) B16777759
theorem B5593151 : Blo 916578 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B2611369 : Blo 916578 2611369 := bstep (se 2 (by rfl) ⟨979263, by rfl⟩ : syracuseStep 2611369 = 1958527) B1958527
theorem B10443653 : Blo 916578 10443653 := bstep (se 4 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 10443653 = 1958185) B1958185
theorem B3103919 : Blo 916578 3103919 := bstep (se 1 (by rfl) ⟨2327939, by rfl⟩ : syracuseStep 3103919 = 4655879) B4655879
theorem B6972155 : Blo 916578 6972155 := bstep (se 1 (by rfl) ⟨5229116, by rfl⟩ : syracuseStep 6972155 = 10458233) B10458233
theorem B21455927 : Blo 916578 21455927 := bstep (se 1 (by rfl) ⟨16091945, by rfl⟩ : syracuseStep 21455927 = 32183891) B32183891
theorem B4973831 : Blo 916578 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B4647131 : Blo 916578 4647131 := bstep (se 1 (by rfl) ⟨3485348, by rfl⟩ : syracuseStep 4647131 = 6970697) B6970697
theorem B2320609 : Blo 916578 2320609 := bstep (se 2 (by rfl) ⟨870228, by rfl⟩ : syracuseStep 2320609 = 1740457) B1740457
theorem B10448027 : Blo 916578 10448027 := bstep (se 1 (by rfl) ⟨7836020, by rfl⟩ : syracuseStep 10448027 = 15672041) B15672041
theorem B7433947 : Blo 916578 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B2620289 : Blo 916578 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B917039 : Blo 916578 917039 := bstep (se 1 (by rfl) ⟨687779, by rfl⟩ : syracuseStep 917039 = 1375559) B1375559
theorem B917199 : Blo 916578 917199 := bstep (se 1 (by rfl) ⟨687899, by rfl⟩ : syracuseStep 917199 = 1375799) B1375799
theorem B917567 : Blo 916578 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B1376327 : Blo 916578 1376327 := bstep (se 1 (by rfl) ⟨1032245, by rfl⟩ : syracuseStep 1376327 = 2064491) B2064491
theorem B917663 : Blo 916578 917663 := bstep (se 1 (by rfl) ⟨688247, by rfl⟩ : syracuseStep 917663 = 1376495) B1376495
theorem B1376423 : Blo 916578 1376423 := bstep (se 1 (by rfl) ⟨1032317, by rfl⟩ : syracuseStep 1376423 = 2064635) B2064635
theorem B918207 : Blo 916578 918207 := bstep (se 1 (by rfl) ⟨688655, by rfl⟩ : syracuseStep 918207 = 1377311) B1377311
theorem B918267 : Blo 916578 918267 := bstep (se 1 (by rfl) ⟨688700, by rfl⟩ : syracuseStep 918267 = 1377401) B1377401
theorem B1377263 : Blo 916578 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B101909515 : Blo 916578 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B1377383 : Blo 916578 1377383 := bstep (se 1 (by rfl) ⟨1033037, by rfl⟩ : syracuseStep 1377383 = 2066075) B2066075
theorem B918783 : Blo 916578 918783 := bstep (se 1 (by rfl) ⟨689087, by rfl⟩ : syracuseStep 918783 = 1378175) B1378175
theorem B919007 : Blo 916578 919007 := bstep (se 1 (by rfl) ⟨689255, by rfl⟩ : syracuseStep 919007 = 1378511) B1378511
theorem B1378151 : Blo 916578 1378151 := bstep (se 1 (by rfl) ⟨1033613, by rfl⟩ : syracuseStep 1378151 = 2067227) B2067227
theorem B919615 : Blo 916578 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B29755775 : Blo 916578 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B919963 : Blo 916578 919963 := bstep (se 1 (by rfl) ⟨689972, by rfl⟩ : syracuseStep 919963 = 1379945) B1379945
theorem B2066921 : Blo 916578 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B920315 : Blo 916578 920315 := bstep (se 1 (by rfl) ⟨690236, by rfl⟩ : syracuseStep 920315 = 1380473) B1380473
theorem B1379135 : Blo 916578 1379135 := bstep (se 1 (by rfl) ⟨1034351, by rfl⟩ : syracuseStep 1379135 = 2068703) B2068703
theorem B1379639 : Blo 916578 1379639 := bstep (se 1 (by rfl) ⟨1034729, by rfl⟩ : syracuseStep 1379639 = 2069459) B2069459
theorem B4198073 : Blo 916578 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B14913563 : Blo 916578 14913563 := bstep (se 1 (by rfl) ⟨11185172, by rfl⟩ : syracuseStep 14913563 = 22370345) B22370345
theorem B5968217 : Blo 916578 5968217 := bstep (se 2 (by rfl) ⟨2238081, by rfl⟩ : syracuseStep 5968217 = 4476163) B4476163
theorem B2069279 : Blo 916578 2069279 := bstep (se 1 (by rfl) ⟨1551959, by rfl⟩ : syracuseStep 2069279 = 3103919) B3103919
theorem B3315887 : Blo 916578 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2825371 : Blo 916578 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B12722159 : Blo 916578 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B1548409 : Blo 916578 1548409 := bstep (se 2 (by rfl) ⟨580653, by rfl⟩ : syracuseStep 1548409 = 1161307) B1161307
theorem B3481825 : Blo 916578 3481825 := bstep (se 2 (by rfl) ⟨1305684, by rfl⟩ : syracuseStep 3481825 = 2611369) B2611369
theorem B4465547 : Blo 916578 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B1746859 : Blo 916578 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B1551271 : Blo 916578 1551271 := bstep (se 1 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 1551271 = 2326907) B2326907
theorem B3484727 : Blo 916578 3484727 := bstep (se 1 (by rfl) ⟨2613545, by rfl⟩ : syracuseStep 3484727 = 5227091) B5227091
theorem B5222009 : Blo 916578 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B39759659 : Blo 916578 39759659 := bstep (se 1 (by rfl) ⟨29819744, by rfl⟩ : syracuseStep 39759659 = 59639489) B59639489
theorem B1552871 : Blo 916578 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B3093767 : Blo 916578 3093767 := bstep (se 1 (by rfl) ⟨2320325, by rfl⟩ : syracuseStep 3093767 = 4640651) B4640651
theorem B17872163 : Blo 916578 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B3094145 : Blo 916578 3094145 := bstep (se 2 (by rfl) ⟨1160304, by rfl⟩ : syracuseStep 3094145 = 2320609) B2320609
theorem B15120985 : Blo 916578 15120985 := bstep (se 2 (by rfl) ⟨5670369, by rfl⟩ : syracuseStep 15120985 = 11340739) B11340739
theorem B6962435 : Blo 916578 6962435 := bstep (se 1 (by rfl) ⟨5221826, by rfl⟩ : syracuseStep 6962435 = 10443653) B10443653
theorem B9911929 : Blo 916578 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B14303951 : Blo 916578 14303951 := bstep (se 1 (by rfl) ⟨10727963, by rfl⟩ : syracuseStep 14303951 = 21455927) B21455927
theorem B3098087 : Blo 916578 3098087 := bstep (se 1 (by rfl) ⟨2323565, by rfl⟩ : syracuseStep 3098087 = 4647131) B4647131
theorem B6965351 : Blo 916578 6965351 := bstep (se 1 (by rfl) ⟨5224013, by rfl⟩ : syracuseStep 6965351 = 10448027) B10448027
theorem B8833211 : Blo 916578 8833211 := bstep (se 1 (by rfl) ⟨6624908, by rfl⟩ : syracuseStep 8833211 = 13249817) B13249817
theorem B23514623 : Blo 916578 23514623 := bstep (se 1 (by rfl) ⟨17635967, by rfl⟩ : syracuseStep 23514623 = 35271935) B35271935
theorem B4642109 : Blo 916578 4642109 := bstep (se 3 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 4642109 = 1740791) B1740791
theorem B1398143 : Blo 916578 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B11196073 : Blo 916578 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B12572495 : Blo 916578 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B5233855 : Blo 916578 5233855 := bstep (se 1 (by rfl) ⟨3925391, by rfl⟩ : syracuseStep 5233855 = 7850783) B7850783
theorem B3923615 : Blo 916578 3923615 := bstep (se 1 (by rfl) ⟨2942711, by rfl⟩ : syracuseStep 3923615 = 5885423) B5885423
theorem B19390331 : Blo 916578 19390331 := bstep (se 1 (by rfl) ⟨14542748, by rfl⟩ : syracuseStep 19390331 = 29085497) B29085497
theorem B573956279 : Blo 916578 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B3105215 : Blo 916578 3105215 := bstep (se 1 (by rfl) ⟨2328911, by rfl⟩ : syracuseStep 3105215 = 4657823) B4657823
theorem B3728767 : Blo 916578 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B3106727 : Blo 916578 3106727 := bstep (se 1 (by rfl) ⟨2330045, by rfl⟩ : syracuseStep 3106727 = 4660091) B4660091
theorem B4648103 : Blo 916578 4648103 := bstep (se 1 (by rfl) ⟨3486077, by rfl⟩ : syracuseStep 4648103 = 6972155) B6972155
theorem B14872045 : Blo 916578 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B2945609 : Blo 916578 2945609 := bstep (se 2 (by rfl) ⟨1104603, by rfl⟩ : syracuseStep 2945609 = 2209207) B2209207
theorem B92042081 : Blo 916578 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B21198523 : Blo 916578 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B2063519 : Blo 916578 2063519 := bstep (se 1 (by rfl) ⟨1547639, by rfl⟩ : syracuseStep 2063519 = 3095279) B3095279
theorem B7831511 : Blo 916578 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B917551 : Blo 916578 917551 := bstep (se 1 (by rfl) ⟨688163, by rfl⟩ : syracuseStep 917551 = 1376327) B1376327
theorem B917615 : Blo 916578 917615 := bstep (se 1 (by rfl) ⟨688211, by rfl⟩ : syracuseStep 917615 = 1376423) B1376423
theorem B2064545 : Blo 916578 2064545 := bstep (se 2 (by rfl) ⟨774204, by rfl⟩ : syracuseStep 2064545 = 1548409) B1548409
theorem B9535967 : Blo 916578 9535967 := bstep (se 1 (by rfl) ⟨7151975, by rfl⟩ : syracuseStep 9535967 = 14303951) B14303951
theorem B918175 : Blo 916578 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B918255 : Blo 916578 918255 := bstep (se 1 (by rfl) ⟨688691, by rfl⟩ : syracuseStep 918255 = 1377383) B1377383
theorem B2065391 : Blo 916578 2065391 := bstep (se 1 (by rfl) ⟨1549043, by rfl⟩ : syracuseStep 2065391 = 3098087) B3098087
theorem B918767 : Blo 916578 918767 := bstep (se 1 (by rfl) ⟨689075, by rfl⟩ : syracuseStep 918767 = 1378151) B1378151
theorem B1377947 : Blo 916578 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B919423 : Blo 916578 919423 := bstep (se 1 (by rfl) ⟨689567, by rfl⟩ : syracuseStep 919423 = 1379135) B1379135
theorem B919759 : Blo 916578 919759 := bstep (se 1 (by rfl) ⟨689819, by rfl⟩ : syracuseStep 919759 = 1379639) B1379639
theorem B2329145 : Blo 916578 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B1379519 : Blo 916578 1379519 := bstep (se 1 (by rfl) ⟨1034639, by rfl⟩ : syracuseStep 1379519 = 2069279) B2069279
theorem B2068361 : Blo 916578 2068361 := bstep (se 2 (by rfl) ⟨775635, by rfl⟩ : syracuseStep 2068361 = 1551271) B1551271
theorem B19829393 : Blo 916578 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B382637519 : Blo 916578 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B2070143 : Blo 916578 2070143 := bstep (se 1 (by rfl) ⟨1552607, by rfl⟩ : syracuseStep 2070143 = 3105215) B3105215
theorem B2071151 : Blo 916578 2071151 := bstep (se 1 (by rfl) ⟨1553363, by rfl⟩ : syracuseStep 2071151 = 3106727) B3106727
theorem B3481339 : Blo 916578 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B20161313 : Blo 916578 20161313 := bstep (se 2 (by rfl) ⟨7560492, by rfl⟩ : syracuseStep 20161313 = 15120985) B15120985
theorem B13215905 : Blo 916578 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B5221007 : Blo 916578 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B19837183 : Blo 916578 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B15676415 : Blo 916578 15676415 := bstep (se 1 (by rfl) ⟨11757311, by rfl⟩ : syracuseStep 15676415 = 23514623) B23514623
theorem B3978811 : Blo 916578 3978811 := bstep (se 1 (by rfl) ⟨2984108, by rfl⟩ : syracuseStep 3978811 = 5968217) B5968217
theorem B3094739 : Blo 916578 3094739 := bstep (se 1 (by rfl) ⟨2321054, by rfl⟩ : syracuseStep 3094739 = 4642109) B4642109
theorem B932095 : Blo 916578 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B2210591 : Blo 916578 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B3098735 : Blo 916578 3098735 := bstep (se 1 (by rfl) ⟨2324051, by rfl⟩ : syracuseStep 3098735 = 4648103) B4648103
theorem B14928097 : Blo 916578 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B28264697 : Blo 916578 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B1035247 : Blo 916578 1035247 := bstep (se 1 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 1035247 = 1552871) B1552871
theorem B61361387 : Blo 916578 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B11914775 : Blo 916578 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B11194861 : Blo 916578 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B4641623 : Blo 916578 4641623 := bstep (se 1 (by rfl) ⟨3481217, by rfl⟩ : syracuseStep 4641623 = 6962435) B6962435
theorem B39769501 : Blo 916578 39769501 := bstep (se 3 (by rfl) ⟨7456781, by rfl⟩ : syracuseStep 39769501 = 14913563) B14913563
theorem B4642433 : Blo 916578 4642433 := bstep (se 2 (by rfl) ⟨1740912, by rfl⟩ : syracuseStep 4642433 = 3481825) B3481825
theorem B135879353 : Blo 916578 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B4643567 : Blo 916578 4643567 := bstep (se 1 (by rfl) ⟨3482675, by rfl⟩ : syracuseStep 4643567 = 6965351) B6965351
theorem B5888807 : Blo 916578 5888807 := bstep (se 1 (by rfl) ⟨4416605, by rfl⟩ : syracuseStep 5888807 = 8833211) B8833211
theorem B4971689 : Blo 916578 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B8381663 : Blo 916578 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B2615743 : Blo 916578 2615743 := bstep (se 1 (by rfl) ⟨1961807, by rfl⟩ : syracuseStep 2615743 = 3923615) B3923615
theorem B8481439 : Blo 916578 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B2977031 : Blo 916578 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B15068645 : Blo 916578 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B2323151 : Blo 916578 2323151 := bstep (se 1 (by rfl) ⟨1742363, by rfl⟩ : syracuseStep 2323151 = 3484727) B3484727
theorem B26506439 : Blo 916578 26506439 := bstep (se 1 (by rfl) ⟨19879829, by rfl⟩ : syracuseStep 26506439 = 39759659) B39759659
theorem B1963739 : Blo 916578 1963739 := bstep (se 1 (by rfl) ⟨1472804, by rfl⟩ : syracuseStep 1963739 = 2945609) B2945609
theorem B2062511 : Blo 916578 2062511 := bstep (se 1 (by rfl) ⟨1546883, by rfl⟩ : syracuseStep 2062511 = 3093767) B3093767
theorem B2062763 : Blo 916578 2062763 := bstep (se 1 (by rfl) ⟨1547072, by rfl⟩ : syracuseStep 2062763 = 3094145) B3094145
theorem B6978473 : Blo 916578 6978473 := bstep (se 2 (by rfl) ⟨2616927, by rfl⟩ : syracuseStep 6978473 = 5233855) B5233855
theorem B1375679 : Blo 916578 1375679 := bstep (se 1 (by rfl) ⟨1031759, by rfl⟩ : syracuseStep 1375679 = 2063519) B2063519
theorem B51707549 : Blo 916578 51707549 := bstep (se 3 (by rfl) ⟨9695165, by rfl⟩ : syracuseStep 51707549 = 19390331) B19390331
theorem B1376363 : Blo 916578 1376363 := bstep (se 1 (by rfl) ⟨1032272, by rfl⟩ : syracuseStep 1376363 = 2064545) B2064545
theorem B6357311 : Blo 916578 6357311 := bstep (se 1 (by rfl) ⟨4767983, by rfl⟩ : syracuseStep 6357311 = 9535967) B9535967
theorem B1376927 : Blo 916578 1376927 := bstep (se 1 (by rfl) ⟨1032695, by rfl⟩ : syracuseStep 1376927 = 2065391) B2065391
theorem B918631 : Blo 916578 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B2065823 : Blo 916578 2065823 := bstep (se 1 (by rfl) ⟨1549367, by rfl⟩ : syracuseStep 2065823 = 3098735) B3098735
theorem B18843131 : Blo 916578 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B919679 : Blo 916578 919679 := bstep (se 1 (by rfl) ⟨689759, by rfl⟩ : syracuseStep 919679 = 1379519) B1379519
theorem B1378907 : Blo 916578 1378907 := bstep (se 1 (by rfl) ⟨1034180, by rfl⟩ : syracuseStep 1378907 = 2068361) B2068361
theorem B11308585 : Blo 916578 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B1380095 : Blo 916578 1380095 := bstep (se 1 (by rfl) ⟨1035071, by rfl⟩ : syracuseStep 1380095 = 2070143) B2070143
theorem B1380329 : Blo 916578 1380329 := bstep (se 2 (by rfl) ⟨517623, by rfl⟩ : syracuseStep 1380329 = 1035247) B1035247
theorem B1380767 : Blo 916578 1380767 := bstep (se 1 (by rfl) ⟨1035575, by rfl⟩ : syracuseStep 1380767 = 2071151) B2071151
theorem B3314459 : Blo 916578 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B26449577 : Blo 916578 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B13440875 : Blo 916578 13440875 := bstep (se 1 (by rfl) ⟨10080656, by rfl⟩ : syracuseStep 13440875 = 20161313) B20161313
theorem B3480671 : Blo 916578 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B53026001 : Blo 916578 53026001 := bstep (se 2 (by rfl) ⟨19884750, by rfl⟩ : syracuseStep 53026001 = 39769501) B39769501
theorem B1548767 : Blo 916578 1548767 := bstep (se 1 (by rfl) ⟨1161575, by rfl⟩ : syracuseStep 1548767 = 2323151) B2323151
theorem B7938749 : Blo 916578 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B17670959 : Blo 916578 17670959 := bstep (se 1 (by rfl) ⟨13253219, by rfl⟩ : syracuseStep 17670959 = 26506439) B26506439
theorem B1552763 : Blo 916578 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B40907591 : Blo 916578 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B7943183 : Blo 916578 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B19904129 : Blo 916578 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B13219595 : Blo 916578 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B3094415 : Blo 916578 3094415 := bstep (se 1 (by rfl) ⟨2320811, by rfl⟩ : syracuseStep 3094415 = 4641623) B4641623
theorem B3487657 : Blo 916578 3487657 := bstep (se 2 (by rfl) ⟨1307871, by rfl⟩ : syracuseStep 3487657 = 2615743) B2615743
theorem B3094955 : Blo 916578 3094955 := bstep (se 1 (by rfl) ⟨2321216, by rfl⟩ : syracuseStep 3094955 = 4642433) B4642433
theorem B90586235 : Blo 916578 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B3095711 : Blo 916578 3095711 := bstep (se 1 (by rfl) ⟨2321783, by rfl⟩ : syracuseStep 3095711 = 4643567) B4643567
theorem B14926481 : Blo 916578 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B5587775 : Blo 916578 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B10045763 : Blo 916578 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B21220325 : Blo 916578 21220325 := bstep (se 4 (by rfl) ⟨1989405, by rfl⟩ : syracuseStep 21220325 = 3978811) B3978811
theorem B4641785 : Blo 916578 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B255091679 : Blo 916578 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B3925871 : Blo 916578 3925871 := bstep (se 1 (by rfl) ⟨2944403, by rfl⟩ : syracuseStep 3925871 = 5888807) B5888807
theorem B8810603 : Blo 916578 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B1242793 : Blo 916578 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B10450943 : Blo 916578 10450943 := bstep (se 1 (by rfl) ⟨7838207, by rfl⟩ : syracuseStep 10450943 = 15676415) B15676415
theorem B1309159 : Blo 916578 1309159 := bstep (se 1 (by rfl) ⟨981869, by rfl⟩ : syracuseStep 1309159 = 1963739) B1963739
theorem B1375007 : Blo 916578 1375007 := bstep (se 1 (by rfl) ⟨1031255, by rfl⟩ : syracuseStep 1375007 = 2062511) B2062511
theorem B2063159 : Blo 916578 2063159 := bstep (se 1 (by rfl) ⟨1547369, by rfl⟩ : syracuseStep 2063159 = 3094739) B3094739
theorem B1375175 : Blo 916578 1375175 := bstep (se 1 (by rfl) ⟨1031381, by rfl⟩ : syracuseStep 1375175 = 2062763) B2062763
theorem B1473727 : Blo 916578 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B4652315 : Blo 916578 4652315 := bstep (se 1 (by rfl) ⟨3489236, by rfl⟩ : syracuseStep 4652315 = 6978473) B6978473
theorem B917119 : Blo 916578 917119 := bstep (se 1 (by rfl) ⟨687839, by rfl⟩ : syracuseStep 917119 = 1375679) B1375679
theorem B34471699 : Blo 916578 34471699 := bstep (se 1 (by rfl) ⟨25853774, by rfl⟩ : syracuseStep 34471699 = 51707549) B51707549
theorem B917575 : Blo 916578 917575 := bstep (se 1 (by rfl) ⟨688181, by rfl⟩ : syracuseStep 917575 = 1376363) B1376363
theorem B917951 : Blo 916578 917951 := bstep (se 1 (by rfl) ⟨688463, by rfl⟩ : syracuseStep 917951 = 1376927) B1376927
theorem B1377215 : Blo 916578 1377215 := bstep (se 1 (by rfl) ⟨1032911, by rfl⟩ : syracuseStep 1377215 = 2065823) B2065823
theorem B919271 : Blo 916578 919271 := bstep (se 1 (by rfl) ⟨689453, by rfl⟩ : syracuseStep 919271 = 1378907) B1378907
theorem B920063 : Blo 916578 920063 := bstep (se 1 (by rfl) ⟨690047, by rfl⟩ : syracuseStep 920063 = 1380095) B1380095
theorem B920219 : Blo 916578 920219 := bstep (se 1 (by rfl) ⟨690164, by rfl⟩ : syracuseStep 920219 = 1380329) B1380329
theorem B920511 : Blo 916578 920511 := bstep (se 1 (by rfl) ⟨690383, by rfl⟩ : syracuseStep 920511 = 1380767) B1380767
theorem B17633051 : Blo 916578 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B15078113 : Blo 916578 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B5873735 : Blo 916578 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B27271727 : Blo 916578 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B1745545 : Blo 916578 1745545 := bstep (se 2 (by rfl) ⟨654579, by rfl⟩ : syracuseStep 1745545 = 1309159) B1309159
theorem B6628229 : Blo 916578 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B4238207 : Blo 916578 4238207 := bstep (se 1 (by rfl) ⟨3178655, by rfl⟩ : syracuseStep 4238207 = 6357311) B6357311
theorem B12562087 : Blo 916578 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B6697175 : Blo 916578 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B3094523 : Blo 916578 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B1032511 : Blo 916578 1032511 := bstep (se 1 (by rfl) ⟨774383, by rfl⟩ : syracuseStep 1032511 = 1548767) B1548767
theorem B5292499 : Blo 916578 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B11780639 : Blo 916578 11780639 := bstep (se 1 (by rfl) ⟨8835479, by rfl⟩ : syracuseStep 11780639 = 17670959) B17670959
theorem B1035175 : Blo 916578 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B5295455 : Blo 916578 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B6967295 : Blo 916578 6967295 := bstep (se 1 (by rfl) ⟨5225471, by rfl⟩ : syracuseStep 6967295 = 10450943) B10450943
theorem B183849061 : Blo 916578 183849061 := bstep (se 4 (by rfl) ⟨17235849, by rfl⟩ : syracuseStep 183849061 = 34471699) B34471699
theorem B3101543 : Blo 916578 3101543 := bstep (se 1 (by rfl) ⟨2326157, by rfl⟩ : syracuseStep 3101543 = 4652315) B4652315
theorem B9950987 : Blo 916578 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B3725183 : Blo 916578 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B14146883 : Blo 916578 14146883 := bstep (se 1 (by rfl) ⟨10610162, by rfl⟩ : syracuseStep 14146883 = 21220325) B21220325
theorem B8838557 : Blo 916578 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B2320447 : Blo 916578 2320447 := bstep (se 1 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 2320447 = 3480671) B3480671
theorem B35350667 : Blo 916578 35350667 := bstep (se 1 (by rfl) ⟨26513000, by rfl⟩ : syracuseStep 35350667 = 53026001) B53026001
theorem B35842333 : Blo 916578 35842333 := bstep (se 3 (by rfl) ⟨6720437, by rfl⟩ : syracuseStep 35842333 = 13440875) B13440875
theorem B170061119 : Blo 916578 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B2617247 : Blo 916578 2617247 := bstep (se 1 (by rfl) ⟨1962935, by rfl⟩ : syracuseStep 2617247 = 3925871) B3925871
theorem B4650209 : Blo 916578 4650209 := bstep (se 2 (by rfl) ⟨1743828, by rfl⟩ : syracuseStep 4650209 = 3487657) B3487657
theorem B241563293 : Blo 916578 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B13269419 : Blo 916578 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B8813063 : Blo 916578 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B2062943 : Blo 916578 2062943 := bstep (se 1 (by rfl) ⟨1547207, by rfl⟩ : syracuseStep 2062943 = 3094415) B3094415
theorem B1964969 : Blo 916578 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B2063303 : Blo 916578 2063303 := bstep (se 1 (by rfl) ⟨1547477, by rfl⟩ : syracuseStep 2063303 = 3094955) B3094955
theorem B916671 : Blo 916578 916671 := bstep (se 1 (by rfl) ⟨687503, by rfl⟩ : syracuseStep 916671 = 1375007) B1375007
theorem B1375439 : Blo 916578 1375439 := bstep (se 1 (by rfl) ⟨1031579, by rfl⟩ : syracuseStep 1375439 = 2063159) B2063159
theorem B916783 : Blo 916578 916783 := bstep (se 1 (by rfl) ⟨687587, by rfl⟩ : syracuseStep 916783 = 1375175) B1375175
theorem B2063807 : Blo 916578 2063807 := bstep (se 1 (by rfl) ⟨1547855, by rfl⟩ : syracuseStep 2063807 = 3095711) B3095711
theorem B15663293 : Blo 916578 15663293 := bstep (se 3 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 15663293 = 5873735) B5873735
theorem B1376681 : Blo 916578 1376681 := bstep (se 2 (by rfl) ⟨516255, by rfl⟩ : syracuseStep 1376681 = 1032511) B1032511
theorem B17859133 : Blo 916578 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B918143 : Blo 916578 918143 := bstep (se 1 (by rfl) ⟨688607, by rfl⟩ : syracuseStep 918143 = 1377215) B1377215
theorem B2327393 : Blo 916578 2327393 := bstep (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) B1745545
theorem B2067695 : Blo 916578 2067695 := bstep (se 1 (by rfl) ⟨1550771, by rfl⟩ : syracuseStep 2067695 = 3101543) B3101543
theorem B1380233 : Blo 916578 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B16749449 : Blo 916578 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B23501501 : Blo 916578 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B23567111 : Blo 916578 23567111 := bstep (se 1 (by rfl) ⟨17675333, by rfl⟩ : syracuseStep 23567111 = 35350667) B35350667
theorem B2825471 : Blo 916578 2825471 := bstep (se 1 (by rfl) ⟨2119103, by rfl⟩ : syracuseStep 2825471 = 4238207) B4238207
theorem B1744831 : Blo 916578 1744831 := bstep (se 1 (by rfl) ⟨1308623, by rfl⟩ : syracuseStep 1744831 = 2617247) B2617247
theorem B7056665 : Blo 916578 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B3093929 : Blo 916578 3093929 := bstep (se 2 (by rfl) ⟨1160223, by rfl⟩ : syracuseStep 3093929 = 2320447) B2320447
theorem B47789777 : Blo 916578 47789777 := bstep (se 2 (by rfl) ⟨17921166, by rfl⟩ : syracuseStep 47789777 = 35842333) B35842333
theorem B6633991 : Blo 916578 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B3100139 : Blo 916578 3100139 := bstep (se 1 (by rfl) ⟨2325104, by rfl⟩ : syracuseStep 3100139 = 4650209) B4650209
theorem B161042195 : Blo 916578 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B7853759 : Blo 916578 7853759 := bstep (se 1 (by rfl) ⟨5890319, by rfl⟩ : syracuseStep 7853759 = 11780639) B11780639
theorem B3530303 : Blo 916578 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B11755367 : Blo 916578 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B4644863 : Blo 916578 4644863 := bstep (se 1 (by rfl) ⟨3483647, by rfl⟩ : syracuseStep 4644863 = 6967295) B6967295
theorem B10052075 : Blo 916578 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B2483455 : Blo 916578 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B9431255 : Blo 916578 9431255 := bstep (se 1 (by rfl) ⟨7073441, by rfl⟩ : syracuseStep 9431255 = 14146883) B14146883
theorem B5892371 : Blo 916578 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B245132081 : Blo 916578 245132081 := bstep (se 2 (by rfl) ⟨91924530, by rfl⟩ : syracuseStep 245132081 = 183849061) B183849061
theorem B18181151 : Blo 916578 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B4418819 : Blo 916578 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B113374079 : Blo 916578 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B2063015 : Blo 916578 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B8846279 : Blo 916578 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B1375295 : Blo 916578 1375295 := bstep (se 1 (by rfl) ⟨1031471, by rfl⟩ : syracuseStep 1375295 = 2062943) B2062943
theorem B1309979 : Blo 916578 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B1375535 : Blo 916578 1375535 := bstep (se 1 (by rfl) ⟨1031651, by rfl⟩ : syracuseStep 1375535 = 2063303) B2063303
theorem B916959 : Blo 916578 916959 := bstep (se 1 (by rfl) ⟨687719, by rfl⟩ : syracuseStep 916959 = 1375439) B1375439
theorem B1375871 : Blo 916578 1375871 := bstep (se 1 (by rfl) ⟨1031903, by rfl⟩ : syracuseStep 1375871 = 2063807) B2063807
theorem B917787 : Blo 916578 917787 := bstep (se 1 (by rfl) ⟨688340, by rfl⟩ : syracuseStep 917787 = 1376681) B1376681
theorem B3311273 : Blo 916578 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B1378463 : Blo 916578 1378463 := bstep (se 1 (by rfl) ⟨1033847, by rfl⟩ : syracuseStep 1378463 = 2067695) B2067695
theorem B2066759 : Blo 916578 2066759 := bstep (se 1 (by rfl) ⟨1550069, by rfl⟩ : syracuseStep 2066759 = 3100139) B3100139
theorem B920155 : Blo 916578 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B15667667 : Blo 916578 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B7836911 : Blo 916578 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B163421387 : Blo 916578 163421387 := bstep (se 1 (by rfl) ⟨122566040, by rfl⟩ : syracuseStep 163421387 = 245132081) B245132081
theorem B31859851 : Blo 916578 31859851 := bstep (se 1 (by rfl) ⟨23894888, by rfl⟩ : syracuseStep 31859851 = 47789777) B47789777
theorem B1551595 : Blo 916578 1551595 := bstep (se 1 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 1551595 = 2327393) B2327393
theorem B107361463 : Blo 916578 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B15711407 : Blo 916578 15711407 := bstep (se 1 (by rfl) ⟨11783555, by rfl⟩ : syracuseStep 15711407 = 23567111) B23567111
theorem B1883647 : Blo 916578 1883647 := bstep (se 1 (by rfl) ⟨1412735, by rfl⟩ : syracuseStep 1883647 = 2825471) B2825471
theorem B3096575 : Blo 916578 3096575 := bstep (se 1 (by rfl) ⟨2322431, by rfl⟩ : syracuseStep 3096575 = 4644863) B4644863
theorem B6701383 : Blo 916578 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B4704443 : Blo 916578 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B75582719 : Blo 916578 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B3493277 : Blo 916578 3493277 := bstep (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) B1309979
theorem B10442195 : Blo 916578 10442195 := bstep (se 1 (by rfl) ⟨7831646, by rfl⟩ : syracuseStep 10442195 = 15663293) B15663293
theorem B23812177 : Blo 916578 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B11166299 : Blo 916578 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B5235839 : Blo 916578 5235839 := bstep (se 1 (by rfl) ⟨3926879, by rfl⟩ : syracuseStep 5235839 = 7853759) B7853759
theorem B2353535 : Blo 916578 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B6287503 : Blo 916578 6287503 := bstep (se 1 (by rfl) ⟨4715627, by rfl⟩ : syracuseStep 6287503 = 9431255) B9431255
theorem B3928247 : Blo 916578 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B12120767 : Blo 916578 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B2945879 : Blo 916578 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B8845321 : Blo 916578 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B2062619 : Blo 916578 2062619 := bstep (se 1 (by rfl) ⟨1546964, by rfl⟩ : syracuseStep 2062619 = 3093929) B3093929
theorem B1375343 : Blo 916578 1375343 := bstep (se 1 (by rfl) ⟨1031507, by rfl⟩ : syracuseStep 1375343 = 2063015) B2063015
theorem B5897519 : Blo 916578 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B916863 : Blo 916578 916863 := bstep (se 1 (by rfl) ⟨687647, by rfl⟩ : syracuseStep 916863 = 1375295) B1375295
theorem B917023 : Blo 916578 917023 := bstep (se 1 (by rfl) ⟨687767, by rfl⟩ : syracuseStep 917023 = 1375535) B1375535
theorem B917247 : Blo 916578 917247 := bstep (se 1 (by rfl) ⟨687935, by rfl⟩ : syracuseStep 917247 = 1375871) B1375871
theorem B2326441 : Blo 916578 2326441 := bstep (se 2 (by rfl) ⟨872415, by rfl⟩ : syracuseStep 2326441 = 1744831) B1744831
theorem B918975 : Blo 916578 918975 := bstep (se 1 (by rfl) ⟨689231, by rfl⟩ : syracuseStep 918975 = 1378463) B1378463
theorem B1377839 : Blo 916578 1377839 := bstep (se 1 (by rfl) ⟨1033379, by rfl⟩ : syracuseStep 1377839 = 2066759) B2066759
theorem B2328851 : Blo 916578 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B2068793 : Blo 916578 2068793 := bstep (se 2 (by rfl) ⟨775797, by rfl⟩ : syracuseStep 2068793 = 1551595) B1551595
theorem B7444199 : Blo 916578 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B2207515 : Blo 916578 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B42479801 : Blo 916578 42479801 := bstep (se 2 (by rfl) ⟨15929925, by rfl⟩ : syracuseStep 42479801 = 31859851) B31859851
theorem B5224607 : Blo 916578 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B6961463 : Blo 916578 6961463 := bstep (se 1 (by rfl) ⟨5221097, by rfl⟩ : syracuseStep 6961463 = 10442195) B10442195
theorem B3490559 : Blo 916578 3490559 := bstep (se 1 (by rfl) ⟨2617919, by rfl⟩ : syracuseStep 3490559 = 5235839) B5235839
theorem B143148617 : Blo 916578 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B8080511 : Blo 916578 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B2511529 : Blo 916578 2511529 := bstep (se 2 (by rfl) ⟨941823, by rfl⟩ : syracuseStep 2511529 = 1883647) B1883647
theorem B10474271 : Blo 916578 10474271 := bstep (se 1 (by rfl) ⟨7855703, by rfl⟩ : syracuseStep 10474271 = 15711407) B15711407
theorem B3101921 : Blo 916578 3101921 := bstep (se 2 (by rfl) ⟨1163220, by rfl⟩ : syracuseStep 3101921 = 2326441) B2326441
theorem B8935177 : Blo 916578 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B3136295 : Blo 916578 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B50388479 : Blo 916578 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B10445111 : Blo 916578 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B108947591 : Blo 916578 108947591 := bstep (se 1 (by rfl) ⟨81710693, by rfl⟩ : syracuseStep 108947591 = 163421387) B163421387
theorem B8383337 : Blo 916578 8383337 := bstep (se 2 (by rfl) ⟨3143751, by rfl⟩ : syracuseStep 8383337 = 6287503) B6287503
theorem B1569023 : Blo 916578 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B11793761 : Blo 916578 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B31749569 : Blo 916578 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B2618831 : Blo 916578 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B1963919 : Blo 916578 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B1375079 : Blo 916578 1375079 := bstep (se 1 (by rfl) ⟨1031309, by rfl⟩ : syracuseStep 1375079 = 2062619) B2062619
theorem B2064383 : Blo 916578 2064383 := bstep (se 1 (by rfl) ⟨1548287, by rfl⟩ : syracuseStep 2064383 = 3096575) B3096575
theorem B916895 : Blo 916578 916895 := bstep (se 1 (by rfl) ⟨687671, by rfl⟩ : syracuseStep 916895 = 1375343) B1375343
theorem B3931679 : Blo 916578 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B2327039 : Blo 916578 2327039 := bstep (se 1 (by rfl) ⟨1745279, by rfl⟩ : syracuseStep 2327039 = 3490559) B3490559
theorem B918559 : Blo 916578 918559 := bstep (se 1 (by rfl) ⟨688919, by rfl⟩ : syracuseStep 918559 = 1377839) B1377839
theorem B1379195 : Blo 916578 1379195 := bstep (se 1 (by rfl) ⟨1034396, by rfl⟩ : syracuseStep 1379195 = 2068793) B2068793
theorem B6982847 : Blo 916578 6982847 := bstep (se 1 (by rfl) ⟨5237135, by rfl⟩ : syracuseStep 6982847 = 10474271) B10474271
theorem B2067947 : Blo 916578 2067947 := bstep (se 1 (by rfl) ⟨1550960, by rfl⟩ : syracuseStep 2067947 = 3101921) B3101921
theorem B33592319 : Blo 916578 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B28319867 : Blo 916578 28319867 := bstep (se 1 (by rfl) ⟨21239900, by rfl⟩ : syracuseStep 28319867 = 42479801) B42479801
theorem B1745887 : Blo 916578 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B3483071 : Blo 916578 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B95432411 : Blo 916578 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B1552567 : Blo 916578 1552567 := bstep (se 1 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 1552567 = 2328851) B2328851
theorem B4962799 : Blo 916578 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B6963407 : Blo 916578 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B72631727 : Blo 916578 72631727 := bstep (se 1 (by rfl) ⟨54473795, by rfl⟩ : syracuseStep 72631727 = 108947591) B108947591
theorem B5588891 : Blo 916578 5588891 := bstep (se 1 (by rfl) ⟨4191668, by rfl⟩ : syracuseStep 5588891 = 8383337) B8383337
theorem B11913569 : Blo 916578 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B21548029 : Blo 916578 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B4640975 : Blo 916578 4640975 := bstep (se 1 (by rfl) ⟨3480731, by rfl⟩ : syracuseStep 4640975 = 6961463) B6961463
theorem B13394821 : Blo 916578 13394821 := bstep (se 4 (by rfl) ⟨1255764, by rfl⟩ : syracuseStep 13394821 = 2511529) B2511529
theorem B2090863 : Blo 916578 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B2943353 : Blo 916578 2943353 := bstep (se 2 (by rfl) ⟨1103757, by rfl⟩ : syracuseStep 2943353 = 2207515) B2207515
theorem B1046015 : Blo 916578 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B7862507 : Blo 916578 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B21166379 : Blo 916578 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B1309279 : Blo 916578 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B10484477 : Blo 916578 10484477 := bstep (se 3 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 10484477 = 3931679) B3931679
theorem B916719 : Blo 916578 916719 := bstep (se 1 (by rfl) ⟨687539, by rfl⟩ : syracuseStep 916719 = 1375079) B1375079
theorem B1376255 : Blo 916578 1376255 := bstep (se 1 (by rfl) ⟨1032191, by rfl⟩ : syracuseStep 1376255 = 2064383) B2064383
theorem B17859761 : Blo 916578 17859761 := bstep (se 2 (by rfl) ⟨6697410, by rfl⟩ : syracuseStep 17859761 = 13394821) B13394821
theorem B2327849 : Blo 916578 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B919463 : Blo 916578 919463 := bstep (se 1 (by rfl) ⟨689597, by rfl⟩ : syracuseStep 919463 = 1379195) B1379195
theorem B4655231 : Blo 916578 4655231 := bstep (se 1 (by rfl) ⟨3491423, by rfl⟩ : syracuseStep 4655231 = 6982847) B6982847
theorem B1378631 : Blo 916578 1378631 := bstep (se 1 (by rfl) ⟨1033973, by rfl⟩ : syracuseStep 1378631 = 2067947) B2067947
theorem B18879911 : Blo 916578 18879911 := bstep (se 1 (by rfl) ⟨14159933, by rfl⟩ : syracuseStep 18879911 = 28319867) B28319867
theorem B2070089 : Blo 916578 2070089 := bstep (se 2 (by rfl) ⟨776283, by rfl⟩ : syracuseStep 2070089 = 1552567) B1552567
theorem B1745705 : Blo 916578 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B6989651 : Blo 916578 6989651 := bstep (se 1 (by rfl) ⟨5242238, by rfl⟩ : syracuseStep 6989651 = 10484477) B10484477
theorem B11151269 : Blo 916578 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1551359 : Blo 916578 1551359 := bstep (se 1 (by rfl) ⟨1163519, by rfl⟩ : syracuseStep 1551359 = 2327039) B2327039
theorem B7942379 : Blo 916578 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B3093983 : Blo 916578 3093983 := bstep (se 1 (by rfl) ⟨2320487, by rfl⟩ : syracuseStep 3093983 = 4640975) B4640975
theorem B22394879 : Blo 916578 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B63621607 : Blo 916578 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B14110919 : Blo 916578 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B4642271 : Blo 916578 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B48421151 : Blo 916578 48421151 := bstep (se 1 (by rfl) ⟨36315863, by rfl⟩ : syracuseStep 48421151 = 72631727) B72631727
theorem B3725927 : Blo 916578 3725927 := bstep (se 1 (by rfl) ⟨2794445, by rfl⟩ : syracuseStep 3725927 = 5588891) B5588891
theorem B28730705 : Blo 916578 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B2322047 : Blo 916578 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B917503 : Blo 916578 917503 := bstep (se 1 (by rfl) ⟨688127, by rfl⟩ : syracuseStep 917503 = 1376255) B1376255
theorem B1962235 : Blo 916578 1962235 := bstep (se 1 (by rfl) ⟨1471676, by rfl⟩ : syracuseStep 1962235 = 2943353) B2943353
theorem B6617065 : Blo 916578 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B5241671 : Blo 916578 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B44629973 : Blo 916578 44629973 := bstep (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) B1046015
theorem B919087 : Blo 916578 919087 := bstep (se 1 (by rfl) ⟨689315, by rfl⟩ : syracuseStep 919087 = 1378631) B1378631
theorem B9407279 : Blo 916578 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B12586607 : Blo 916578 12586607 := bstep (se 1 (by rfl) ⟨9439955, by rfl⟩ : syracuseStep 12586607 = 18879911) B18879911
theorem B1380059 : Blo 916578 1380059 := bstep (se 1 (by rfl) ⟨1035044, by rfl⟩ : syracuseStep 1380059 = 2070089) B2070089
theorem B32280767 : Blo 916578 32280767 := bstep (se 1 (by rfl) ⟨24210575, by rfl⟩ : syracuseStep 32280767 = 48421151) B48421151
theorem B4659767 : Blo 916578 4659767 := bstep (se 1 (by rfl) ⟨3494825, by rfl⟩ : syracuseStep 4659767 = 6989651) B6989651
theorem B1548031 : Blo 916578 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B8822753 : Blo 916578 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B11906507 : Blo 916578 11906507 := bstep (se 1 (by rfl) ⟨8929880, by rfl⟩ : syracuseStep 11906507 = 17859761) B17859761
theorem B1551899 : Blo 916578 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B84718709 : Blo 916578 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B306460853 : Blo 916578 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B3094847 : Blo 916578 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1163803 : Blo 916578 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B1034239 : Blo 916578 1034239 := bstep (se 1 (by rfl) ⟨775679, by rfl⟩ : syracuseStep 1034239 = 1551359) B1551359
theorem B14929919 : Blo 916578 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B3494447 : Blo 916578 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B3103487 : Blo 916578 3103487 := bstep (se 1 (by rfl) ⟨2327615, by rfl⟩ : syracuseStep 3103487 = 4655231) B4655231
theorem B84828809 : Blo 916578 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B2483951 : Blo 916578 2483951 := bstep (se 1 (by rfl) ⟨1862963, by rfl⟩ : syracuseStep 2483951 = 3725927) B3725927
theorem B2616313 : Blo 916578 2616313 := bstep (se 2 (by rfl) ⟨981117, by rfl⟩ : syracuseStep 2616313 = 1962235) B1962235
theorem B7434179 : Blo 916578 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B2062655 : Blo 916578 2062655 := bstep (se 1 (by rfl) ⟨1546991, by rfl⟩ : syracuseStep 2062655 = 3093983) B3093983
theorem B29753315 : Blo 916578 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B8391071 : Blo 916578 8391071 := bstep (se 1 (by rfl) ⟨6293303, by rfl⟩ : syracuseStep 8391071 = 12586607) B12586607
theorem B920039 : Blo 916578 920039 := bstep (se 1 (by rfl) ⟨690029, by rfl⟩ : syracuseStep 920039 = 1380059) B1380059
theorem B1378985 : Blo 916578 1378985 := bstep (se 2 (by rfl) ⟨517119, by rfl⟩ : syracuseStep 1378985 = 1034239) B1034239
theorem B2329631 : Blo 916578 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B2068991 : Blo 916578 2068991 := bstep (se 1 (by rfl) ⟨1551743, by rfl⟩ : syracuseStep 2068991 = 3103487) B3103487
theorem B6623869 : Blo 916578 6623869 := bstep (se 3 (by rfl) ⟨1241975, by rfl⟩ : syracuseStep 6623869 = 2483951) B2483951
theorem B7937671 : Blo 916578 7937671 := bstep (se 1 (by rfl) ⟨5953253, by rfl⟩ : syracuseStep 7937671 = 11906507) B11906507
theorem B4956119 : Blo 916578 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B19835543 : Blo 916578 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B1551737 : Blo 916578 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B226210157 : Blo 916578 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B6271519 : Blo 916578 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B3488417 : Blo 916578 3488417 := bstep (se 2 (by rfl) ⟨1308156, by rfl⟩ : syracuseStep 3488417 = 2616313) B2616313
theorem B5881835 : Blo 916578 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B1034599 : Blo 916578 1034599 := bstep (se 1 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 1034599 = 1551899) B1551899
theorem B56479139 : Blo 916578 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B9953279 : Blo 916578 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B21520511 : Blo 916578 21520511 := bstep (se 1 (by rfl) ⟨16140383, by rfl⟩ : syracuseStep 21520511 = 32280767) B32280767
theorem B3106511 : Blo 916578 3106511 := bstep (se 1 (by rfl) ⟨2329883, by rfl⟩ : syracuseStep 3106511 = 4659767) B4659767
theorem B204307235 : Blo 916578 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B1375103 : Blo 916578 1375103 := bstep (se 1 (by rfl) ⟨1031327, by rfl⟩ : syracuseStep 1375103 = 2062655) B2062655
theorem B2063231 : Blo 916578 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B2064041 : Blo 916578 2064041 := bstep (se 2 (by rfl) ⟨774015, by rfl⟩ : syracuseStep 2064041 = 1548031) B1548031
theorem B919323 : Blo 916578 919323 := bstep (se 1 (by rfl) ⟨689492, by rfl⟩ : syracuseStep 919323 = 1378985) B1378985
theorem B37652759 : Blo 916578 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B1379327 : Blo 916578 1379327 := bstep (se 1 (by rfl) ⟨1034495, by rfl⟩ : syracuseStep 1379327 = 2068991) B2068991
theorem B1379465 : Blo 916578 1379465 := bstep (se 2 (by rfl) ⟨517299, by rfl⟩ : syracuseStep 1379465 = 1034599) B1034599
theorem B8362025 : Blo 916578 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B2071007 : Blo 916578 2071007 := bstep (se 1 (by rfl) ⟨1553255, by rfl⟩ : syracuseStep 2071007 = 3106511) B3106511
theorem B150806771 : Blo 916578 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B1553087 : Blo 916578 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B6635519 : Blo 916578 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B8831825 : Blo 916578 8831825 := bstep (se 2 (by rfl) ⟨3311934, by rfl⟩ : syracuseStep 8831825 = 6623869) B6623869
theorem B13223695 : Blo 916578 13223695 := bstep (se 1 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 13223695 = 19835543) B19835543
theorem B1034491 : Blo 916578 1034491 := bstep (se 1 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 1034491 = 1551737) B1551737
theorem B136204823 : Blo 916578 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B3921223 : Blo 916578 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B3304079 : Blo 916578 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B14347007 : Blo 916578 14347007 := bstep (se 1 (by rfl) ⟨10760255, by rfl⟩ : syracuseStep 14347007 = 21520511) B21520511
theorem B22376189 : Blo 916578 22376189 := bstep (se 3 (by rfl) ⟨4195535, by rfl⟩ : syracuseStep 22376189 = 8391071) B8391071
theorem B2325611 : Blo 916578 2325611 := bstep (se 1 (by rfl) ⟨1744208, by rfl⟩ : syracuseStep 2325611 = 3488417) B3488417
theorem B916735 : Blo 916578 916735 := bstep (se 1 (by rfl) ⟨687551, by rfl⟩ : syracuseStep 916735 = 1375103) B1375103
theorem B1375487 : Blo 916578 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B10583561 : Blo 916578 10583561 := bstep (se 2 (by rfl) ⟨3968835, by rfl⟩ : syracuseStep 10583561 = 7937671) B7937671
theorem B1376027 : Blo 916578 1376027 := bstep (se 1 (by rfl) ⟨1032020, by rfl⟩ : syracuseStep 1376027 = 2064041) B2064041
theorem B25101839 : Blo 916578 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B919551 : Blo 916578 919551 := bstep (se 1 (by rfl) ⟨689663, by rfl⟩ : syracuseStep 919551 = 1379327) B1379327
theorem B919643 : Blo 916578 919643 := bstep (se 1 (by rfl) ⟨689732, by rfl⟩ : syracuseStep 919643 = 1379465) B1379465
theorem B17631593 : Blo 916578 17631593 := bstep (se 2 (by rfl) ⟨6611847, by rfl⟩ : syracuseStep 17631593 = 13223695) B13223695
theorem B1379321 : Blo 916578 1379321 := bstep (se 2 (by rfl) ⟨517245, by rfl⟩ : syracuseStep 1379321 = 1034491) B1034491
theorem B90803215 : Blo 916578 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B5574683 : Blo 916578 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B1380671 : Blo 916578 1380671 := bstep (se 1 (by rfl) ⟨1035503, by rfl⟩ : syracuseStep 1380671 = 2071007) B2071007
theorem B100537847 : Blo 916578 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B4423679 : Blo 916578 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B2202719 : Blo 916578 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B14917459 : Blo 916578 14917459 := bstep (se 1 (by rfl) ⟨11188094, by rfl⟩ : syracuseStep 14917459 = 22376189) B22376189
theorem B1550407 : Blo 916578 1550407 := bstep (se 1 (by rfl) ⟨1162805, by rfl⟩ : syracuseStep 1550407 = 2325611) B2325611
theorem B7055707 : Blo 916578 7055707 := bstep (se 1 (by rfl) ⟨5291780, by rfl⟩ : syracuseStep 7055707 = 10583561) B10583561
theorem B5228297 : Blo 916578 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B1035391 : Blo 916578 1035391 := bstep (se 1 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 1035391 = 1553087) B1553087
theorem B5887883 : Blo 916578 5887883 := bstep (se 1 (by rfl) ⟨4415912, by rfl⟩ : syracuseStep 5887883 = 8831825) B8831825
theorem B9564671 : Blo 916578 9564671 := bstep (se 1 (by rfl) ⟨7173503, by rfl⟩ : syracuseStep 9564671 = 14347007) B14347007
theorem B916991 : Blo 916578 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B917351 : Blo 916578 917351 := bstep (se 1 (by rfl) ⟨688013, by rfl⟩ : syracuseStep 917351 = 1376027) B1376027
theorem B919547 : Blo 916578 919547 := bstep (se 1 (by rfl) ⟨689660, by rfl⟩ : syracuseStep 919547 = 1379321) B1379321
theorem B2067209 : Blo 916578 2067209 := bstep (se 2 (by rfl) ⟨775203, by rfl⟩ : syracuseStep 2067209 = 1550407) B1550407
theorem B920447 : Blo 916578 920447 := bstep (se 1 (by rfl) ⟨690335, by rfl⟩ : syracuseStep 920447 = 1380671) B1380671
theorem B9407609 : Blo 916578 9407609 := bstep (se 2 (by rfl) ⟨3527853, by rfl⟩ : syracuseStep 9407609 = 7055707) B7055707
theorem B1380521 : Blo 916578 1380521 := bstep (se 2 (by rfl) ⟨517695, by rfl⟩ : syracuseStep 1380521 = 1035391) B1035391
theorem B5873917 : Blo 916578 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B3485531 : Blo 916578 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B3716455 : Blo 916578 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B67025231 : Blo 916578 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B6376447 : Blo 916578 6376447 := bstep (se 1 (by rfl) ⟨4782335, by rfl⟩ : syracuseStep 6376447 = 9564671) B9564671
theorem B16734559 : Blo 916578 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B11754395 : Blo 916578 11754395 := bstep (se 1 (by rfl) ⟨8815796, by rfl⟩ : syracuseStep 11754395 = 17631593) B17631593
theorem B3925255 : Blo 916578 3925255 := bstep (se 1 (by rfl) ⟨2943941, by rfl⟩ : syracuseStep 3925255 = 5887883) B5887883
theorem B121070953 : Blo 916578 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B2949119 : Blo 916578 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B19889945 : Blo 916578 19889945 := bstep (se 2 (by rfl) ⟨7458729, by rfl⟩ : syracuseStep 19889945 = 14917459) B14917459
theorem B7831889 : Blo 916578 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B1378139 : Blo 916578 1378139 := bstep (se 1 (by rfl) ⟨1033604, by rfl⟩ : syracuseStep 1378139 = 2067209) B2067209
theorem B920347 : Blo 916578 920347 := bstep (se 1 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 920347 = 1380521) B1380521
theorem B7836263 : Blo 916578 7836263 := bstep (se 1 (by rfl) ⟨5877197, by rfl⟩ : syracuseStep 7836263 = 11754395) B11754395
theorem B4955273 : Blo 916578 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B161427937 : Blo 916578 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B6271739 : Blo 916578 6271739 := bstep (se 1 (by rfl) ⟨4703804, by rfl⟩ : syracuseStep 6271739 = 9407609) B9407609
theorem B8501929 : Blo 916578 8501929 := bstep (se 2 (by rfl) ⟨3188223, by rfl⟩ : syracuseStep 8501929 = 6376447) B6376447
theorem B44683487 : Blo 916578 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B13259963 : Blo 916578 13259963 := bstep (se 1 (by rfl) ⟨9944972, by rfl⟩ : syracuseStep 13259963 = 19889945) B19889945
theorem B5233673 : Blo 916578 5233673 := bstep (se 2 (by rfl) ⟨1962627, by rfl⟩ : syracuseStep 5233673 = 3925255) B3925255
theorem B1966079 : Blo 916578 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B2323687 : Blo 916578 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B22312745 : Blo 916578 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B918759 : Blo 916578 918759 := bstep (se 1 (by rfl) ⟨689069, by rfl⟩ : syracuseStep 918759 = 1378139) B1378139
theorem B29788991 : Blo 916578 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B5221259 : Blo 916578 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B5224175 : Blo 916578 5224175 := bstep (se 1 (by rfl) ⟨3918131, by rfl⟩ : syracuseStep 5224175 = 7836263) B7836263
theorem B3489115 : Blo 916578 3489115 := bstep (se 1 (by rfl) ⟨2616836, by rfl⟩ : syracuseStep 3489115 = 5233673) B5233673
theorem B215237249 : Blo 916578 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B3098249 : Blo 916578 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B4181159 : Blo 916578 4181159 := bstep (se 1 (by rfl) ⟨3135869, by rfl⟩ : syracuseStep 4181159 = 6271739) B6271739
theorem B8839975 : Blo 916578 8839975 := bstep (se 1 (by rfl) ⟨6629981, by rfl⟩ : syracuseStep 8839975 = 13259963) B13259963
theorem B45343621 : Blo 916578 45343621 := bstep (se 4 (by rfl) ⟨4250964, by rfl⟩ : syracuseStep 45343621 = 8501929) B8501929
theorem B3303515 : Blo 916578 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B14875163 : Blo 916578 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B5242877 : Blo 916578 5242877 := bstep (se 3 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 5242877 = 1966079) B1966079
theorem B143491499 : Blo 916578 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B2065499 : Blo 916578 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B60458161 : Blo 916578 60458161 := bstep (se 2 (by rfl) ⟨22671810, by rfl⟩ : syracuseStep 60458161 = 45343621) B45343621
theorem B19859327 : Blo 916578 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B2787439 : Blo 916578 2787439 := bstep (se 1 (by rfl) ⟨2090579, by rfl⟩ : syracuseStep 2787439 = 4181159) B4181159
theorem B3480839 : Blo 916578 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B3482783 : Blo 916578 3482783 := bstep (se 1 (by rfl) ⟨2612087, by rfl⟩ : syracuseStep 3482783 = 5224175) B5224175
theorem B9916775 : Blo 916578 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B3495251 : Blo 916578 3495251 := bstep (se 1 (by rfl) ⟨2621438, by rfl⟩ : syracuseStep 3495251 = 5242877) B5242877
theorem B11786633 : Blo 916578 11786633 := bstep (se 2 (by rfl) ⟨4419987, by rfl⟩ : syracuseStep 11786633 = 8839975) B8839975
theorem B8809373 : Blo 916578 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B4652153 : Blo 916578 4652153 := bstep (se 2 (by rfl) ⟨1744557, by rfl⟩ : syracuseStep 4652153 = 3489115) B3489115
theorem B1376999 : Blo 916578 1376999 := bstep (se 1 (by rfl) ⟨1032749, by rfl⟩ : syracuseStep 1376999 = 2065499) B2065499
theorem B13239551 : Blo 916578 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B80610881 : Blo 916578 80610881 := bstep (se 2 (by rfl) ⟨30229080, by rfl⟩ : syracuseStep 80610881 = 60458161) B60458161
theorem B2330167 : Blo 916578 2330167 := bstep (se 1 (by rfl) ⟨1747625, by rfl⟩ : syracuseStep 2330167 = 3495251) B3495251
theorem B5872915 : Blo 916578 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B95660999 : Blo 916578 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B3716585 : Blo 916578 3716585 := bstep (se 2 (by rfl) ⟨1393719, by rfl⟩ : syracuseStep 3716585 = 2787439) B2787439
theorem B3101435 : Blo 916578 3101435 := bstep (se 1 (by rfl) ⟨2326076, by rfl⟩ : syracuseStep 3101435 = 4652153) B4652153
theorem B6611183 : Blo 916578 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B7857755 : Blo 916578 7857755 := bstep (se 1 (by rfl) ⟨5893316, by rfl⟩ : syracuseStep 7857755 = 11786633) B11786633
theorem B2320559 : Blo 916578 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B2321855 : Blo 916578 2321855 := bstep (se 1 (by rfl) ⟨1741391, by rfl⟩ : syracuseStep 2321855 = 3482783) B3482783
theorem B917999 : Blo 916578 917999 := bstep (se 1 (by rfl) ⟨688499, by rfl⟩ : syracuseStep 917999 = 1376999) B1376999
theorem B2067623 : Blo 916578 2067623 := bstep (se 1 (by rfl) ⟨1550717, by rfl⟩ : syracuseStep 2067623 = 3101435) B3101435
theorem B214962349 : Blo 916578 214962349 := bstep (se 3 (by rfl) ⟨40305440, by rfl⟩ : syracuseStep 214962349 = 80610881) B80610881
theorem B1547039 : Blo 916578 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B63773999 : Blo 916578 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B1547903 : Blo 916578 1547903 := bstep (se 1 (by rfl) ⟨1160927, by rfl⟩ : syracuseStep 1547903 = 2321855) B2321855
theorem B8826367 : Blo 916578 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B4407455 : Blo 916578 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2477723 : Blo 916578 2477723 := bstep (se 1 (by rfl) ⟨1858292, by rfl⟩ : syracuseStep 2477723 = 3716585) B3716585
theorem B3106889 : Blo 916578 3106889 := bstep (se 2 (by rfl) ⟨1165083, by rfl⟩ : syracuseStep 3106889 = 2330167) B2330167
theorem B5238503 : Blo 916578 5238503 := bstep (se 1 (by rfl) ⟨3928877, by rfl⟩ : syracuseStep 5238503 = 7857755) B7857755
theorem B7830553 : Blo 916578 7830553 := bstep (se 2 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 7830553 = 5872915) B5872915
theorem B1378415 : Blo 916578 1378415 := bstep (se 1 (by rfl) ⟨1033811, by rfl⟩ : syracuseStep 1378415 = 2067623) B2067623
theorem B11768489 : Blo 916578 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B2071259 : Blo 916578 2071259 := bstep (se 1 (by rfl) ⟨1553444, by rfl⟩ : syracuseStep 2071259 = 3106889) B3106889
theorem B1031359 : Blo 916578 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B42515999 : Blo 916578 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B1031935 : Blo 916578 1031935 := bstep (se 1 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 1031935 = 1547903) B1547903
theorem B3492335 : Blo 916578 3492335 := bstep (se 1 (by rfl) ⟨2619251, by rfl⟩ : syracuseStep 3492335 = 5238503) B5238503
theorem B10440737 : Blo 916578 10440737 := bstep (se 2 (by rfl) ⟨3915276, by rfl⟩ : syracuseStep 10440737 = 7830553) B7830553
theorem B6607261 : Blo 916578 6607261 := bstep (se 3 (by rfl) ⟨1238861, by rfl⟩ : syracuseStep 6607261 = 2477723) B2477723
theorem B2938303 : Blo 916578 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B286616465 : Blo 916578 286616465 := bstep (se 2 (by rfl) ⟨107481174, by rfl⟩ : syracuseStep 286616465 = 214962349) B214962349
theorem B918943 : Blo 916578 918943 := bstep (se 1 (by rfl) ⟨689207, by rfl⟩ : syracuseStep 918943 = 1378415) B1378415
theorem B2328223 : Blo 916578 2328223 := bstep (se 1 (by rfl) ⟨1746167, by rfl⟩ : syracuseStep 2328223 = 3492335) B3492335
theorem B1380839 : Blo 916578 1380839 := bstep (se 1 (by rfl) ⟨1035629, by rfl⟩ : syracuseStep 1380839 = 2071259) B2071259
theorem B191077643 : Blo 916578 191077643 := bstep (se 1 (by rfl) ⟨143308232, by rfl⟩ : syracuseStep 191077643 = 286616465) B286616465
theorem B6960491 : Blo 916578 6960491 := bstep (se 1 (by rfl) ⟨5220368, by rfl⟩ : syracuseStep 6960491 = 10440737) B10440737
theorem B7845659 : Blo 916578 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B3917737 : Blo 916578 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B8809681 : Blo 916578 8809681 := bstep (se 2 (by rfl) ⟨3303630, by rfl⟩ : syracuseStep 8809681 = 6607261) B6607261
theorem B1375145 : Blo 916578 1375145 := bstep (se 2 (by rfl) ⟨515679, by rfl⟩ : syracuseStep 1375145 = 1031359) B1031359
theorem B1375913 : Blo 916578 1375913 := bstep (se 2 (by rfl) ⟨515967, by rfl⟩ : syracuseStep 1375913 = 1031935) B1031935
theorem B28343999 : Blo 916578 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B920559 : Blo 916578 920559 := bstep (se 1 (by rfl) ⟨690419, by rfl⟩ : syracuseStep 920559 = 1380839) B1380839
theorem B5223649 : Blo 916578 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B11746241 : Blo 916578 11746241 := bstep (se 2 (by rfl) ⟨4404840, by rfl⟩ : syracuseStep 11746241 = 8809681) B8809681
theorem B127385095 : Blo 916578 127385095 := bstep (se 1 (by rfl) ⟨95538821, by rfl⟩ : syracuseStep 127385095 = 191077643) B191077643
theorem B4640327 : Blo 916578 4640327 := bstep (se 1 (by rfl) ⟨3480245, by rfl⟩ : syracuseStep 4640327 = 6960491) B6960491
theorem B5230439 : Blo 916578 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B18895999 : Blo 916578 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B3104297 : Blo 916578 3104297 := bstep (se 2 (by rfl) ⟨1164111, by rfl⟩ : syracuseStep 3104297 = 2328223) B2328223
theorem B916763 : Blo 916578 916763 := bstep (se 1 (by rfl) ⟨687572, by rfl⟩ : syracuseStep 916763 = 1375145) B1375145
theorem B917275 : Blo 916578 917275 := bstep (se 1 (by rfl) ⟨687956, by rfl⟩ : syracuseStep 917275 = 1375913) B1375913
theorem B2069531 : Blo 916578 2069531 := bstep (se 1 (by rfl) ⟨1552148, by rfl⟩ : syracuseStep 2069531 = 3104297) B3104297
theorem B169846793 : Blo 916578 169846793 := bstep (se 2 (by rfl) ⟨63692547, by rfl⟩ : syracuseStep 169846793 = 127385095) B127385095
theorem B3093551 : Blo 916578 3093551 := bstep (se 1 (by rfl) ⟨2320163, by rfl⟩ : syracuseStep 3093551 = 4640327) B4640327
theorem B3486959 : Blo 916578 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B6964865 : Blo 916578 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B25194665 : Blo 916578 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B7830827 : Blo 916578 7830827 := bstep (se 1 (by rfl) ⟨5873120, by rfl⟩ : syracuseStep 7830827 = 11746241) B11746241
theorem B1379687 : Blo 916578 1379687 := bstep (se 1 (by rfl) ⟨1034765, by rfl⟩ : syracuseStep 1379687 = 2069531) B2069531
theorem B5220551 : Blo 916578 5220551 := bstep (se 1 (by rfl) ⟨3915413, by rfl⟩ : syracuseStep 5220551 = 7830827) B7830827
theorem B113231195 : Blo 916578 113231195 := bstep (se 1 (by rfl) ⟨84923396, by rfl⟩ : syracuseStep 113231195 = 169846793) B169846793
theorem B16796443 : Blo 916578 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B4643243 : Blo 916578 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B2062367 : Blo 916578 2062367 := bstep (se 1 (by rfl) ⟨1546775, by rfl⟩ : syracuseStep 2062367 = 3093551) B3093551
theorem B2324639 : Blo 916578 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B919791 : Blo 916578 919791 := bstep (se 1 (by rfl) ⟨689843, by rfl⟩ : syracuseStep 919791 = 1379687) B1379687
theorem B3480367 : Blo 916578 3480367 := bstep (se 1 (by rfl) ⟨2610275, by rfl⟩ : syracuseStep 3480367 = 5220551) B5220551
theorem B1549759 : Blo 916578 1549759 := bstep (se 1 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 1549759 = 2324639) B2324639
theorem B22395257 : Blo 916578 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B3095495 : Blo 916578 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B75487463 : Blo 916578 75487463 := bstep (se 1 (by rfl) ⟨56615597, by rfl⟩ : syracuseStep 75487463 = 113231195) B113231195
theorem B1374911 : Blo 916578 1374911 := bstep (se 1 (by rfl) ⟨1031183, by rfl⟩ : syracuseStep 1374911 = 2062367) B2062367
theorem B2066345 : Blo 916578 2066345 := bstep (se 2 (by rfl) ⟨774879, by rfl⟩ : syracuseStep 2066345 = 1549759) B1549759
theorem B4640489 : Blo 916578 4640489 := bstep (se 2 (by rfl) ⟨1740183, by rfl⟩ : syracuseStep 4640489 = 3480367) B3480367
theorem B14930171 : Blo 916578 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B50324975 : Blo 916578 50324975 := bstep (se 1 (by rfl) ⟨37743731, by rfl⟩ : syracuseStep 50324975 = 75487463) B75487463
theorem B916607 : Blo 916578 916607 := bstep (se 1 (by rfl) ⟨687455, by rfl⟩ : syracuseStep 916607 = 1374911) B1374911
theorem B2063663 : Blo 916578 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1377563 : Blo 916578 1377563 := bstep (se 1 (by rfl) ⟨1033172, by rfl⟩ : syracuseStep 1377563 = 2066345) B2066345
theorem B3093659 : Blo 916578 3093659 := bstep (se 1 (by rfl) ⟨2320244, by rfl⟩ : syracuseStep 3093659 = 4640489) B4640489
theorem B9953447 : Blo 916578 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B33549983 : Blo 916578 33549983 := bstep (se 1 (by rfl) ⟨25162487, by rfl⟩ : syracuseStep 33549983 = 50324975) B50324975
theorem B1375775 : Blo 916578 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B26542525 : Blo 916578 26542525 := bstep (se 3 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 26542525 = 9953447) B9953447
theorem B918375 : Blo 916578 918375 := bstep (se 1 (by rfl) ⟨688781, by rfl⟩ : syracuseStep 918375 = 1377563) B1377563
theorem B22366655 : Blo 916578 22366655 := bstep (se 1 (by rfl) ⟨16774991, by rfl⟩ : syracuseStep 22366655 = 33549983) B33549983
theorem B2062439 : Blo 916578 2062439 := bstep (se 1 (by rfl) ⟨1546829, by rfl⟩ : syracuseStep 2062439 = 3093659) B3093659
theorem B917183 : Blo 916578 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B35390033 : Blo 916578 35390033 := bstep (se 2 (by rfl) ⟨13271262, by rfl⟩ : syracuseStep 35390033 = 26542525) B26542525
theorem B14911103 : Blo 916578 14911103 := bstep (se 1 (by rfl) ⟨11183327, by rfl⟩ : syracuseStep 14911103 = 22366655) B22366655
theorem B1374959 : Blo 916578 1374959 := bstep (se 1 (by rfl) ⟨1031219, by rfl⟩ : syracuseStep 1374959 = 2062439) B2062439
theorem B23593355 : Blo 916578 23593355 := bstep (se 1 (by rfl) ⟨17695016, by rfl⟩ : syracuseStep 23593355 = 35390033) B35390033
theorem B9940735 : Blo 916578 9940735 := bstep (se 1 (by rfl) ⟨7455551, by rfl⟩ : syracuseStep 9940735 = 14911103) B14911103
theorem B916639 : Blo 916578 916639 := bstep (se 1 (by rfl) ⟨687479, by rfl⟩ : syracuseStep 916639 = 1374959) B1374959
theorem B15728903 : Blo 916578 15728903 := bstep (se 1 (by rfl) ⟨11796677, by rfl⟩ : syracuseStep 15728903 = 23593355) B23593355
theorem B13254313 : Blo 916578 13254313 := bstep (se 2 (by rfl) ⟨4970367, by rfl⟩ : syracuseStep 13254313 = 9940735) B9940735
theorem B10485935 : Blo 916578 10485935 := bstep (se 1 (by rfl) ⟨7864451, by rfl⟩ : syracuseStep 10485935 = 15728903) B15728903
theorem B17672417 : Blo 916578 17672417 := bstep (se 2 (by rfl) ⟨6627156, by rfl⟩ : syracuseStep 17672417 = 13254313) B13254313
theorem B6990623 : Blo 916578 6990623 := bstep (se 1 (by rfl) ⟨5242967, by rfl⟩ : syracuseStep 6990623 = 10485935) B10485935
theorem B11781611 : Blo 916578 11781611 := bstep (se 1 (by rfl) ⟨8836208, by rfl⟩ : syracuseStep 11781611 = 17672417) B17672417
theorem B4660415 : Blo 916578 4660415 := bstep (se 1 (by rfl) ⟨3495311, by rfl⟩ : syracuseStep 4660415 = 6990623) B6990623
theorem B7854407 : Blo 916578 7854407 := bstep (se 1 (by rfl) ⟨5890805, by rfl⟩ : syracuseStep 7854407 = 11781611) B11781611
theorem B5236271 : Blo 916578 5236271 := bstep (se 1 (by rfl) ⟨3927203, by rfl⟩ : syracuseStep 5236271 = 7854407) B7854407
theorem B3106943 : Blo 916578 3106943 := bstep (se 1 (by rfl) ⟨2330207, by rfl⟩ : syracuseStep 3106943 = 4660415) B4660415
theorem B2071295 : Blo 916578 2071295 := bstep (se 1 (by rfl) ⟨1553471, by rfl⟩ : syracuseStep 2071295 = 3106943) B3106943
theorem B3490847 : Blo 916578 3490847 := bstep (se 1 (by rfl) ⟨2618135, by rfl⟩ : syracuseStep 3490847 = 5236271) B5236271
theorem B2327231 : Blo 916578 2327231 := bstep (se 1 (by rfl) ⟨1745423, by rfl⟩ : syracuseStep 2327231 = 3490847) B3490847
theorem B1380863 : Blo 916578 1380863 := bstep (se 1 (by rfl) ⟨1035647, by rfl⟩ : syracuseStep 1380863 = 2071295) B2071295
theorem B920575 : Blo 916578 920575 := bstep (se 1 (by rfl) ⟨690431, by rfl⟩ : syracuseStep 920575 = 1380863) B1380863
theorem B1551487 : Blo 916578 1551487 := bstep (se 1 (by rfl) ⟨1163615, by rfl⟩ : syracuseStep 1551487 = 2327231) B2327231
theorem B2068649 : Blo 916578 2068649 := bstep (se 2 (by rfl) ⟨775743, by rfl⟩ : syracuseStep 2068649 = 1551487) B1551487
theorem B1379099 : Blo 916578 1379099 := bstep (se 1 (by rfl) ⟨1034324, by rfl⟩ : syracuseStep 1379099 = 2068649) B2068649
theorem B919399 : Blo 916578 919399 := bstep (se 1 (by rfl) ⟨689549, by rfl⟩ : syracuseStep 919399 = 1379099) B1379099

theorem C0 (j : ℕ) (h1 : 229144 ≤ j) (h2 : j ≤ 229843) : Blo 916578 (4 * j + 3) := by
  interval_cases j
  · exact B916579
  · exact B916583
  · exact B916587
  · exact B916591
  · exact B916595
  · exact B916599
  · exact B916603
  · exact B916607
  · exact B916611
  · exact B916615
  · exact B916619
  · exact B916623
  · exact B916627
  · exact B916631
  · exact B916635
  · exact B916639
  · exact B916643
  · exact B916647
  · exact B916651
  · exact B916655
  · exact B916659
  · exact B916663
  · exact B916667
  · exact B916671
  · exact B916675
  · exact B916679
  · exact B916683
  · exact B916687
  · exact B916691
  · exact B916695
  · exact B916699
  · exact B916703
  · exact B916707
  · exact B916711
  · exact B916715
  · exact B916719
  · exact B916723
  · exact B916727
  · exact B916731
  · exact B916735
  · exact B916739
  · exact B916743
  · exact B916747
  · exact B916751
  · exact B916755
  · exact B916759
  · exact B916763
  · exact B916767
  · exact B916771
  · exact B916775
  · exact B916779
  · exact B916783
  · exact B916787
  · exact B916791
  · exact B916795
  · exact B916799
  · exact B916803
  · exact B916807
  · exact B916811
  · exact B916815
  · exact B916819
  · exact B916823
  · exact B916827
  · exact B916831
  · exact B916835
  · exact B916839
  · exact B916843
  · exact B916847
  · exact B916851
  · exact B916855
  · exact B916859
  · exact B916863
  · exact B916867
  · exact B916871
  · exact B916875
  · exact B916879
  · exact B916883
  · exact B916887
  · exact B916891
  · exact B916895
  · exact B916899
  · exact B916903
  · exact B916907
  · exact B916911
  · exact B916915
  · exact B916919
  · exact B916923
  · exact B916927
  · exact B916931
  · exact B916935
  · exact B916939
  · exact B916943
  · exact B916947
  · exact B916951
  · exact B916955
  · exact B916959
  · exact B916963
  · exact B916967
  · exact B916971
  · exact B916975
  · exact B916979
  · exact B916983
  · exact B916987
  · exact B916991
  · exact B916995
  · exact B916999
  · exact B917003
  · exact B917007
  · exact B917011
  · exact B917015
  · exact B917019
  · exact B917023
  · exact B917027
  · exact B917031
  · exact B917035
  · exact B917039
  · exact B917043
  · exact B917047
  · exact B917051
  · exact B917055
  · exact B917059
  · exact B917063
  · exact B917067
  · exact B917071
  · exact B917075
  · exact B917079
  · exact B917083
  · exact B917087
  · exact B917091
  · exact B917095
  · exact B917099
  · exact B917103
  · exact B917107
  · exact B917111
  · exact B917115
  · exact B917119
  · exact B917123
  · exact B917127
  · exact B917131
  · exact B917135
  · exact B917139
  · exact B917143
  · exact B917147
  · exact B917151
  · exact B917155
  · exact B917159
  · exact B917163
  · exact B917167
  · exact B917171
  · exact B917175
  · exact B917179
  · exact B917183
  · exact B917187
  · exact B917191
  · exact B917195
  · exact B917199
  · exact B917203
  · exact B917207
  · exact B917211
  · exact B917215
  · exact B917219
  · exact B917223
  · exact B917227
  · exact B917231
  · exact B917235
  · exact B917239
  · exact B917243
  · exact B917247
  · exact B917251
  · exact B917255
  · exact B917259
  · exact B917263
  · exact B917267
  · exact B917271
  · exact B917275
  · exact B917279
  · exact B917283
  · exact B917287
  · exact B917291
  · exact B917295
  · exact B917299
  · exact B917303
  · exact B917307
  · exact B917311
  · exact B917315
  · exact B917319
  · exact B917323
  · exact B917327
  · exact B917331
  · exact B917335
  · exact B917339
  · exact B917343
  · exact B917347
  · exact B917351
  · exact B917355
  · exact B917359
  · exact B917363
  · exact B917367
  · exact B917371
  · exact B917375
  · exact B917379
  · exact B917383
  · exact B917387
  · exact B917391
  · exact B917395
  · exact B917399
  · exact B917403
  · exact B917407
  · exact B917411
  · exact B917415
  · exact B917419
  · exact B917423
  · exact B917427
  · exact B917431
  · exact B917435
  · exact B917439
  · exact B917443
  · exact B917447
  · exact B917451
  · exact B917455
  · exact B917459
  · exact B917463
  · exact B917467
  · exact B917471
  · exact B917475
  · exact B917479
  · exact B917483
  · exact B917487
  · exact B917491
  · exact B917495
  · exact B917499
  · exact B917503
  · exact B917507
  · exact B917511
  · exact B917515
  · exact B917519
  · exact B917523
  · exact B917527
  · exact B917531
  · exact B917535
  · exact B917539
  · exact B917543
  · exact B917547
  · exact B917551
  · exact B917555
  · exact B917559
  · exact B917563
  · exact B917567
  · exact B917571
  · exact B917575
  · exact B917579
  · exact B917583
  · exact B917587
  · exact B917591
  · exact B917595
  · exact B917599
  · exact B917603
  · exact B917607
  · exact B917611
  · exact B917615
  · exact B917619
  · exact B917623
  · exact B917627
  · exact B917631
  · exact B917635
  · exact B917639
  · exact B917643
  · exact B917647
  · exact B917651
  · exact B917655
  · exact B917659
  · exact B917663
  · exact B917667
  · exact B917671
  · exact B917675
  · exact B917679
  · exact B917683
  · exact B917687
  · exact B917691
  · exact B917695
  · exact B917699
  · exact B917703
  · exact B917707
  · exact B917711
  · exact B917715
  · exact B917719
  · exact B917723
  · exact B917727
  · exact B917731
  · exact B917735
  · exact B917739
  · exact B917743
  · exact B917747
  · exact B917751
  · exact B917755
  · exact B917759
  · exact B917763
  · exact B917767
  · exact B917771
  · exact B917775
  · exact B917779
  · exact B917783
  · exact B917787
  · exact B917791
  · exact B917795
  · exact B917799
  · exact B917803
  · exact B917807
  · exact B917811
  · exact B917815
  · exact B917819
  · exact B917823
  · exact B917827
  · exact B917831
  · exact B917835
  · exact B917839
  · exact B917843
  · exact B917847
  · exact B917851
  · exact B917855
  · exact B917859
  · exact B917863
  · exact B917867
  · exact B917871
  · exact B917875
  · exact B917879
  · exact B917883
  · exact B917887
  · exact B917891
  · exact B917895
  · exact B917899
  · exact B917903
  · exact B917907
  · exact B917911
  · exact B917915
  · exact B917919
  · exact B917923
  · exact B917927
  · exact B917931
  · exact B917935
  · exact B917939
  · exact B917943
  · exact B917947
  · exact B917951
  · exact B917955
  · exact B917959
  · exact B917963
  · exact B917967
  · exact B917971
  · exact B917975
  · exact B917979
  · exact B917983
  · exact B917987
  · exact B917991
  · exact B917995
  · exact B917999
  · exact B918003
  · exact B918007
  · exact B918011
  · exact B918015
  · exact B918019
  · exact B918023
  · exact B918027
  · exact B918031
  · exact B918035
  · exact B918039
  · exact B918043
  · exact B918047
  · exact B918051
  · exact B918055
  · exact B918059
  · exact B918063
  · exact B918067
  · exact B918071
  · exact B918075
  · exact B918079
  · exact B918083
  · exact B918087
  · exact B918091
  · exact B918095
  · exact B918099
  · exact B918103
  · exact B918107
  · exact B918111
  · exact B918115
  · exact B918119
  · exact B918123
  · exact B918127
  · exact B918131
  · exact B918135
  · exact B918139
  · exact B918143
  · exact B918147
  · exact B918151
  · exact B918155
  · exact B918159
  · exact B918163
  · exact B918167
  · exact B918171
  · exact B918175
  · exact B918179
  · exact B918183
  · exact B918187
  · exact B918191
  · exact B918195
  · exact B918199
  · exact B918203
  · exact B918207
  · exact B918211
  · exact B918215
  · exact B918219
  · exact B918223
  · exact B918227
  · exact B918231
  · exact B918235
  · exact B918239
  · exact B918243
  · exact B918247
  · exact B918251
  · exact B918255
  · exact B918259
  · exact B918263
  · exact B918267
  · exact B918271
  · exact B918275
  · exact B918279
  · exact B918283
  · exact B918287
  · exact B918291
  · exact B918295
  · exact B918299
  · exact B918303
  · exact B918307
  · exact B918311
  · exact B918315
  · exact B918319
  · exact B918323
  · exact B918327
  · exact B918331
  · exact B918335
  · exact B918339
  · exact B918343
  · exact B918347
  · exact B918351
  · exact B918355
  · exact B918359
  · exact B918363
  · exact B918367
  · exact B918371
  · exact B918375
  · exact B918379
  · exact B918383
  · exact B918387
  · exact B918391
  · exact B918395
  · exact B918399
  · exact B918403
  · exact B918407
  · exact B918411
  · exact B918415
  · exact B918419
  · exact B918423
  · exact B918427
  · exact B918431
  · exact B918435
  · exact B918439
  · exact B918443
  · exact B918447
  · exact B918451
  · exact B918455
  · exact B918459
  · exact B918463
  · exact B918467
  · exact B918471
  · exact B918475
  · exact B918479
  · exact B918483
  · exact B918487
  · exact B918491
  · exact B918495
  · exact B918499
  · exact B918503
  · exact B918507
  · exact B918511
  · exact B918515
  · exact B918519
  · exact B918523
  · exact B918527
  · exact B918531
  · exact B918535
  · exact B918539
  · exact B918543
  · exact B918547
  · exact B918551
  · exact B918555
  · exact B918559
  · exact B918563
  · exact B918567
  · exact B918571
  · exact B918575
  · exact B918579
  · exact B918583
  · exact B918587
  · exact B918591
  · exact B918595
  · exact B918599
  · exact B918603
  · exact B918607
  · exact B918611
  · exact B918615
  · exact B918619
  · exact B918623
  · exact B918627
  · exact B918631
  · exact B918635
  · exact B918639
  · exact B918643
  · exact B918647
  · exact B918651
  · exact B918655
  · exact B918659
  · exact B918663
  · exact B918667
  · exact B918671
  · exact B918675
  · exact B918679
  · exact B918683
  · exact B918687
  · exact B918691
  · exact B918695
  · exact B918699
  · exact B918703
  · exact B918707
  · exact B918711
  · exact B918715
  · exact B918719
  · exact B918723
  · exact B918727
  · exact B918731
  · exact B918735
  · exact B918739
  · exact B918743
  · exact B918747
  · exact B918751
  · exact B918755
  · exact B918759
  · exact B918763
  · exact B918767
  · exact B918771
  · exact B918775
  · exact B918779
  · exact B918783
  · exact B918787
  · exact B918791
  · exact B918795
  · exact B918799
  · exact B918803
  · exact B918807
  · exact B918811
  · exact B918815
  · exact B918819
  · exact B918823
  · exact B918827
  · exact B918831
  · exact B918835
  · exact B918839
  · exact B918843
  · exact B918847
  · exact B918851
  · exact B918855
  · exact B918859
  · exact B918863
  · exact B918867
  · exact B918871
  · exact B918875
  · exact B918879
  · exact B918883
  · exact B918887
  · exact B918891
  · exact B918895
  · exact B918899
  · exact B918903
  · exact B918907
  · exact B918911
  · exact B918915
  · exact B918919
  · exact B918923
  · exact B918927
  · exact B918931
  · exact B918935
  · exact B918939
  · exact B918943
  · exact B918947
  · exact B918951
  · exact B918955
  · exact B918959
  · exact B918963
  · exact B918967
  · exact B918971
  · exact B918975
  · exact B918979
  · exact B918983
  · exact B918987
  · exact B918991
  · exact B918995
  · exact B918999
  · exact B919003
  · exact B919007
  · exact B919011
  · exact B919015
  · exact B919019
  · exact B919023
  · exact B919027
  · exact B919031
  · exact B919035
  · exact B919039
  · exact B919043
  · exact B919047
  · exact B919051
  · exact B919055
  · exact B919059
  · exact B919063
  · exact B919067
  · exact B919071
  · exact B919075
  · exact B919079
  · exact B919083
  · exact B919087
  · exact B919091
  · exact B919095
  · exact B919099
  · exact B919103
  · exact B919107
  · exact B919111
  · exact B919115
  · exact B919119
  · exact B919123
  · exact B919127
  · exact B919131
  · exact B919135
  · exact B919139
  · exact B919143
  · exact B919147
  · exact B919151
  · exact B919155
  · exact B919159
  · exact B919163
  · exact B919167
  · exact B919171
  · exact B919175
  · exact B919179
  · exact B919183
  · exact B919187
  · exact B919191
  · exact B919195
  · exact B919199
  · exact B919203
  · exact B919207
  · exact B919211
  · exact B919215
  · exact B919219
  · exact B919223
  · exact B919227
  · exact B919231
  · exact B919235
  · exact B919239
  · exact B919243
  · exact B919247
  · exact B919251
  · exact B919255
  · exact B919259
  · exact B919263
  · exact B919267
  · exact B919271
  · exact B919275
  · exact B919279
  · exact B919283
  · exact B919287
  · exact B919291
  · exact B919295
  · exact B919299
  · exact B919303
  · exact B919307
  · exact B919311
  · exact B919315
  · exact B919319
  · exact B919323
  · exact B919327
  · exact B919331
  · exact B919335
  · exact B919339
  · exact B919343
  · exact B919347
  · exact B919351
  · exact B919355
  · exact B919359
  · exact B919363
  · exact B919367
  · exact B919371
  · exact B919375

theorem C1 (j : ℕ) (h1 : 229844 ≤ j) (h2 : j ≤ 230143) : Blo 916578 (4 * j + 3) := by
  interval_cases j
  · exact B919379
  · exact B919383
  · exact B919387
  · exact B919391
  · exact B919395
  · exact B919399
  · exact B919403
  · exact B919407
  · exact B919411
  · exact B919415
  · exact B919419
  · exact B919423
  · exact B919427
  · exact B919431
  · exact B919435
  · exact B919439
  · exact B919443
  · exact B919447
  · exact B919451
  · exact B919455
  · exact B919459
  · exact B919463
  · exact B919467
  · exact B919471
  · exact B919475
  · exact B919479
  · exact B919483
  · exact B919487
  · exact B919491
  · exact B919495
  · exact B919499
  · exact B919503
  · exact B919507
  · exact B919511
  · exact B919515
  · exact B919519
  · exact B919523
  · exact B919527
  · exact B919531
  · exact B919535
  · exact B919539
  · exact B919543
  · exact B919547
  · exact B919551
  · exact B919555
  · exact B919559
  · exact B919563
  · exact B919567
  · exact B919571
  · exact B919575
  · exact B919579
  · exact B919583
  · exact B919587
  · exact B919591
  · exact B919595
  · exact B919599
  · exact B919603
  · exact B919607
  · exact B919611
  · exact B919615
  · exact B919619
  · exact B919623
  · exact B919627
  · exact B919631
  · exact B919635
  · exact B919639
  · exact B919643
  · exact B919647
  · exact B919651
  · exact B919655
  · exact B919659
  · exact B919663
  · exact B919667
  · exact B919671
  · exact B919675
  · exact B919679
  · exact B919683
  · exact B919687
  · exact B919691
  · exact B919695
  · exact B919699
  · exact B919703
  · exact B919707
  · exact B919711
  · exact B919715
  · exact B919719
  · exact B919723
  · exact B919727
  · exact B919731
  · exact B919735
  · exact B919739
  · exact B919743
  · exact B919747
  · exact B919751
  · exact B919755
  · exact B919759
  · exact B919763
  · exact B919767
  · exact B919771
  · exact B919775
  · exact B919779
  · exact B919783
  · exact B919787
  · exact B919791
  · exact B919795
  · exact B919799
  · exact B919803
  · exact B919807
  · exact B919811
  · exact B919815
  · exact B919819
  · exact B919823
  · exact B919827
  · exact B919831
  · exact B919835
  · exact B919839
  · exact B919843
  · exact B919847
  · exact B919851
  · exact B919855
  · exact B919859
  · exact B919863
  · exact B919867
  · exact B919871
  · exact B919875
  · exact B919879
  · exact B919883
  · exact B919887
  · exact B919891
  · exact B919895
  · exact B919899
  · exact B919903
  · exact B919907
  · exact B919911
  · exact B919915
  · exact B919919
  · exact B919923
  · exact B919927
  · exact B919931
  · exact B919935
  · exact B919939
  · exact B919943
  · exact B919947
  · exact B919951
  · exact B919955
  · exact B919959
  · exact B919963
  · exact B919967
  · exact B919971
  · exact B919975
  · exact B919979
  · exact B919983
  · exact B919987
  · exact B919991
  · exact B919995
  · exact B919999
  · exact B920003
  · exact B920007
  · exact B920011
  · exact B920015
  · exact B920019
  · exact B920023
  · exact B920027
  · exact B920031
  · exact B920035
  · exact B920039
  · exact B920043
  · exact B920047
  · exact B920051
  · exact B920055
  · exact B920059
  · exact B920063
  · exact B920067
  · exact B920071
  · exact B920075
  · exact B920079
  · exact B920083
  · exact B920087
  · exact B920091
  · exact B920095
  · exact B920099
  · exact B920103
  · exact B920107
  · exact B920111
  · exact B920115
  · exact B920119
  · exact B920123
  · exact B920127
  · exact B920131
  · exact B920135
  · exact B920139
  · exact B920143
  · exact B920147
  · exact B920151
  · exact B920155
  · exact B920159
  · exact B920163
  · exact B920167
  · exact B920171
  · exact B920175
  · exact B920179
  · exact B920183
  · exact B920187
  · exact B920191
  · exact B920195
  · exact B920199
  · exact B920203
  · exact B920207
  · exact B920211
  · exact B920215
  · exact B920219
  · exact B920223
  · exact B920227
  · exact B920231
  · exact B920235
  · exact B920239
  · exact B920243
  · exact B920247
  · exact B920251
  · exact B920255
  · exact B920259
  · exact B920263
  · exact B920267
  · exact B920271
  · exact B920275
  · exact B920279
  · exact B920283
  · exact B920287
  · exact B920291
  · exact B920295
  · exact B920299
  · exact B920303
  · exact B920307
  · exact B920311
  · exact B920315
  · exact B920319
  · exact B920323
  · exact B920327
  · exact B920331
  · exact B920335
  · exact B920339
  · exact B920343
  · exact B920347
  · exact B920351
  · exact B920355
  · exact B920359
  · exact B920363
  · exact B920367
  · exact B920371
  · exact B920375
  · exact B920379
  · exact B920383
  · exact B920387
  · exact B920391
  · exact B920395
  · exact B920399
  · exact B920403
  · exact B920407
  · exact B920411
  · exact B920415
  · exact B920419
  · exact B920423
  · exact B920427
  · exact B920431
  · exact B920435
  · exact B920439
  · exact B920443
  · exact B920447
  · exact B920451
  · exact B920455
  · exact B920459
  · exact B920463
  · exact B920467
  · exact B920471
  · exact B920475
  · exact B920479
  · exact B920483
  · exact B920487
  · exact B920491
  · exact B920495
  · exact B920499
  · exact B920503
  · exact B920507
  · exact B920511
  · exact B920515
  · exact B920519
  · exact B920523
  · exact B920527
  · exact B920531
  · exact B920535
  · exact B920539
  · exact B920543
  · exact B920547
  · exact B920551
  · exact B920555
  · exact B920559
  · exact B920563
  · exact B920567
  · exact B920571
  · exact B920575

theorem solution (m : ℕ) (hlo : 916578 ≤ m) (hhi : m ≤ 920578) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 229144 ≤ j := by omega
    have hj2 : j ≤ 230143 := by omega
    have hb : Blo 916578 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 229844 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
