-- Prove2me | solution 1 for mme_CW_q6_fixed_z_difference_hash_lower_tail_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:40:00.061335+00:00
-- url     : https://prove2.me/submissions/d40e2534-b9f7-4dae-96c7-a555cc3b6308

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment
import Theorems.Thm_mme_finite_variance_lower_tail_gap_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The exact fixed-Z variance bound controls every integer threshold whose
scaled distance below the mean is at least `R`. -/
theorem solution
    {M n L G B H R : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z)
    (hcard : A.card = B)
    (hgap : M * H + R ≤ B) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    R ^ 2 * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
      (fun w => ¬ H ≤ (A.attach.filter
        (fun e => ∑ i, c e i * w i = 0)).card)).card) ≤
      2 * B * M ^ (2 * n + 3) := by
  classical
  let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
    (2 * ((e.1.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
  let D : (Fin (2 * n + 2) → ZMod M) → ℕ := fun w =>
    (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card
  let U : Finset (Fin (2 * n + 2) → ZMod M) := Finset.univ
  have hmom := mme_CW_q6_fixed_z_difference_hash_first_second_moment
    hM h2 hG A z hz
  change
    (∑ w, D w) = A.card * M ^ (2 * n + 1) ∧
      (∑ w, D w ^ 2) ≤
        2 * A.card * M ^ (2 * n + 1) + A.card ^ 2 * M ^ (2 * n) at hmom
  have hfirstReal : (∑ w, (D w : ℝ)) =
      (B : ℝ) * (M : ℝ) ^ (2 * n + 1) := by
    exact_mod_cast (show (∑ w, D w) = B * M ^ (2 * n + 1) by
      simpa [hcard] using hmom.1)
  have hsecondReal : (∑ w, (D w : ℝ) ^ 2) ≤
      2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 1) +
        (B : ℝ) ^ 2 * (M : ℝ) ^ (2 * n) := by
    exact_mod_cast (show (∑ w, D w ^ 2) ≤
        2 * B * M ^ (2 * n + 1) + B ^ 2 * M ^ (2 * n) by
      simpa [hcard] using hmom.2)
  have hUcard : (U.card : ℝ) = (M : ℝ) ^ (2 * n + 2) := by
    norm_num [U]
  have hvarIdentity :
      (∑ w ∈ U, ((M : ℝ) * (D w : ℝ) - (B : ℝ)) ^ 2) =
        (M : ℝ) ^ 2 * (∑ w, (D w : ℝ) ^ 2) -
          2 * (M : ℝ) * (B : ℝ) * (∑ w, (D w : ℝ)) +
          (U.card : ℝ) * (B : ℝ) ^ 2 := by
    simp only [U]
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring_nf
    congr 2
    funext x
    ring
  have hvar :
      (∑ w ∈ U, ((M : ℝ) * (D w : ℝ) - (B : ℝ)) ^ 2) ≤
        2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := by
    rw [hvarIdentity, hfirstReal, hUcard]
    calc
      (M : ℝ) ^ 2 * (∑ w, (D w : ℝ) ^ 2) -
            2 * (M : ℝ) * (B : ℝ) *
              ((B : ℝ) * (M : ℝ) ^ (2 * n + 1)) +
            (M : ℝ) ^ (2 * n + 2) * (B : ℝ) ^ 2 ≤
          (M : ℝ) ^ 2 *
              (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 1) +
                (B : ℝ) ^ 2 * (M : ℝ) ^ (2 * n)) -
            2 * (M : ℝ) * (B : ℝ) *
              ((B : ℝ) * (M : ℝ) ^ (2 * n + 1)) +
            (M : ℝ) ^ (2 * n + 2) * (B : ℝ) ^ 2 := by
        gcongr
      _ = 2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := by ring
  have htail := mme_finite_variance_lower_tail_gap_card
    U (fun w => (M : ℝ) * (D w : ℝ))
      (B : ℝ) (R : ℝ) (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3))
      (by positivity) hvar
  have hsubset :
      U.filter (fun w => ¬ H ≤ D w) ⊆
        U.filter (fun w =>
          (M : ℝ) * (D w : ℝ) + (R : ℝ) ≤ (B : ℝ)) := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨hw'.1, ?_⟩
    have hD : D w ≤ H := Nat.le_of_lt (Nat.lt_of_not_ge hw'.2)
    have hnat : M * D w + R ≤ B :=
      (Nat.add_le_add_right (Nat.mul_le_mul_left M hD) R).trans hgap
    exact_mod_cast hnat
  have hcardBad := Finset.card_le_card hsubset
  have hreal :
      (R : ℝ) ^ 2 * ((U.filter (fun w => ¬ H ≤ D w)).card : ℝ) ≤
        2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := by
    calc
      (R : ℝ) ^ 2 * ((U.filter (fun w => ¬ H ≤ D w)).card : ℝ) ≤
          (R : ℝ) ^ 2 *
            ((U.filter (fun w =>
              (M : ℝ) * (D w : ℝ) + (R : ℝ) ≤ (B : ℝ))).card : ℝ) := by
        gcongr
      _ ≤ 2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := htail
  have hnat :
      R ^ 2 * (U.filter (fun w => ¬ H ≤ D w)).card ≤
        2 * B * M ^ (2 * n + 3) := by
    exact_mod_cast hreal
  simpa only [c, D, U] using hnat
