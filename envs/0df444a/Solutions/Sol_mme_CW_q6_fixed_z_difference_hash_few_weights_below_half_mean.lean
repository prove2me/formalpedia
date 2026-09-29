-- Prove2me | solution 1 for mme_CW_q6_fixed_z_difference_hash_few_weights_below_half_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:42:44.262124+00:00
-- url     : https://prove2.me/submissions/a25448f2-794e-40f7-8a77-a18585b8c81e

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment
import Theorems.Thm_mme_finite_variance_below_half_mean_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For a regular fixed Z-fiber, all but a quantitatively small set of
difference-hash parameters have degree at least the half-mean threshold. -/
theorem solution
    {M n L G B H : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z)
    (hcard : A.card = B) (hB : 0 < B)
    (hH : 2 * M * H ≤ B) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    B * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
      (fun w => ¬ H ≤ (A.attach.filter
        (fun e => ∑ i, c e i * w i = 0)).card)).card) ≤
      8 * M * M ^ (2 * n + 2) := by
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
  have hbadHalf := mme_finite_variance_below_half_mean_card
    U (fun w => (M : ℝ) * (D w : ℝ)) (B : ℝ)
      (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3))
      (by intro w hw; positivity) (by positivity) hvar
  have hbadSubset :
      U.filter (fun w => ¬ H ≤ D w) ⊆
        U.filter (fun w => 2 * ((M : ℝ) * (D w : ℝ)) ≤ (B : ℝ)) := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨hw'.1, ?_⟩
    have hD : D w ≤ H := Nat.le_of_lt (Nat.lt_of_not_ge hw'.2)
    have hnat : 2 * M * D w ≤ B := calc
      2 * M * D w ≤ 2 * M * H := Nat.mul_le_mul_left (2 * M) hD
      _ ≤ B := hH
    exact_mod_cast (show 2 * (M * D w) ≤ B by
      simpa [Nat.mul_assoc] using hnat)
  have hbadCard := Finset.card_le_card hbadSubset
  have hboundReal :
      (B : ℝ) ^ 2 * ((U.filter (fun w => ¬ H ≤ D w)).card : ℝ) ≤
        8 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := by
    calc
      (B : ℝ) ^ 2 * ((U.filter (fun w => ¬ H ≤ D w)).card : ℝ) ≤
          (B : ℝ) ^ 2 *
            ((U.filter (fun w =>
              2 * ((M : ℝ) * (D w : ℝ)) ≤ (B : ℝ))).card : ℝ) := by
        gcongr
      _ ≤ 4 * (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3)) := hbadHalf
      _ = 8 * (B : ℝ) * (M : ℝ) ^ (2 * n + 3) := by ring
  have hBreal : 0 < (B : ℝ) := by positivity
  have hcancelReal :
      (B : ℝ) * ((U.filter (fun w => ¬ H ≤ D w)).card : ℝ) ≤
        8 * (M : ℝ) ^ (2 * n + 3) := by
    apply le_of_mul_le_mul_left (a := (B : ℝ)) (by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hboundReal) hBreal
  have hcancelNat :
      B * (U.filter (fun w => ¬ H ≤ D w)).card ≤
        8 * M ^ (2 * n + 3) := by
    exact_mod_cast hcancelReal
  simpa only [c, D, U, ← pow_succ', Nat.mul_assoc] using hcancelNat
