-- Prove2me | solution 1 for mme_CW_q6_fixed_z_many_weights_above_half_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:51:33.374434+00:00
-- url     : https://prove2.me/submissions/9360e0ef-2da1-4bd4-8c0c-74adf4e5f3b3

import Mathlib
import Theorems.Thm_mme_finite_second_moment_many_above_threshold
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A fixed Z-fiber has source-scale many weight vectors whose surviving
degree is at least any threshold below half of its mean. -/
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
    (B : ℝ) * (M : ℝ) ^ (2 * n + 2) ≤
      4 * (2 * (M : ℝ) + (B : ℝ)) *
        (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
          (fun w => H ≤ (A.attach.filter
            (fun e => ∑ i, c e i * w i = 0)).card)).card : ℝ) := by
  classical
  let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
    (2 * ((e.1.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
  let D : (Fin (2 * n + 2) → ZMod M) → ℕ := fun w =>
    (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card
  have hmom := mme_CW_q6_fixed_z_difference_hash_first_second_moment
    hM h2 hG A z hz
  change
    (∑ w, D w) = A.card * M ^ (2 * n + 1) ∧
      (∑ w, D w ^ 2) ≤
        2 * A.card * M ^ (2 * n + 1) + A.card ^ 2 * M ^ (2 * n) at hmom
  have hcardU : Fintype.card (Fin (2 * n + 2) → ZMod M) = M ^ (2 * n + 2) := by
    simp
  have hhalfNat : 2 * Fintype.card (Fin (2 * n + 2) → ZMod M) * H ≤
      ∑ w, D w := by
    rw [hmom.1, hcard, hcardU]
    have hpow : M ^ (2 * n + 2) = M * M ^ (2 * n + 1) := by
      ring
    rw [hpow]
    nlinarith [Nat.zero_le (M ^ (2 * n + 1))]
  have hpz := mme_finite_second_moment_many_above_threshold
    (Finset.univ : Finset (Fin (2 * n + 2) → ZMod M))
    (fun w => (D w : ℝ)) (H : ℝ)
    (by intro w hw; positivity) (by positivity) (by
      have hhalfNat' :
          2 * (Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).card * H ≤
            ∑ w, D w := by
        simpa only [Finset.card_univ] using hhalfNat
      have hcast :
          ((2 * (Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).card * H : ℕ) : ℝ) ≤
            ((∑ w, D w : ℕ) : ℝ) := by
        exact_mod_cast hhalfNat'
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using hcast)
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
  have hgood :
      (Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
          (fun w => (H : ℝ) ≤ (D w : ℝ)) =
        (Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
          (fun w => H ≤ D w) := by
    ext w
    simp
  rw [hfirstReal] at hpz
  rw [hgood] at hpz
  have hpz' :
      ((B : ℝ) * (M : ℝ) ^ (2 * n + 1)) ^ 2 ≤
        4 * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
          (fun w => H ≤ D w)).card : ℝ) *
          (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 1) +
            (B : ℝ) ^ 2 * (M : ℝ) ^ (2 * n)) := by
    calc
      ((B : ℝ) * (M : ℝ) ^ (2 * n + 1)) ^ 2 ≤
          4 * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
            (fun w => H ≤ D w)).card : ℝ) *
            (∑ w, (D w : ℝ) ^ 2) := hpz
      _ ≤ 4 * (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
            (fun w => H ≤ D w)).card : ℝ) *
          (2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 1) +
            (B : ℝ) ^ 2 * (M : ℝ) ^ (2 * n)) := by
        exact mul_le_mul_of_nonneg_left hsecondReal
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hfactor : 0 < (B : ℝ) * (M : ℝ) ^ (2 * n) := by
    positivity
  have hid1 :
      ((B : ℝ) * (M : ℝ) ^ (2 * n + 1)) ^ 2 =
        ((B : ℝ) * (M : ℝ) ^ (2 * n)) *
          ((B : ℝ) * (M : ℝ) ^ (2 * n + 2)) := by
    ring
  have hid2 :
      2 * (B : ℝ) * (M : ℝ) ^ (2 * n + 1) +
          (B : ℝ) ^ 2 * (M : ℝ) ^ (2 * n) =
        ((B : ℝ) * (M : ℝ) ^ (2 * n)) *
          (2 * (M : ℝ) + (B : ℝ)) := by
    ring
  rw [hid1, hid2] at hpz'
  have hcancel :
      ((B : ℝ) * (M : ℝ) ^ (2 * n)) *
          ((B : ℝ) * (M : ℝ) ^ (2 * n + 2)) ≤
        ((B : ℝ) * (M : ℝ) ^ (2 * n)) *
          (4 * (2 * (M : ℝ) + (B : ℝ)) *
            (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
              (fun w => H ≤ D w)).card : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpz'
  have hresult := le_of_mul_le_mul_left hcancel hfactor
  simpa only [c, D] using hresult
