-- Prove2me | solution 1 for mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:51:12.533992+00:00
-- url     : https://prove2.me/submissions/dbf8d6c5-956d-4a46-9e68-51bfd66bbb4c

import Mathlib
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_extraction

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem exp_split_double_loss_generic (C x : ℝ) :
    Real.exp (-(2 * C + 400) * x) =
      (Real.exp (-C * x)) ^ (2 : ℕ) *
        (Real.exp (-200 * x)) ^ (2 : ℕ) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem volume_weight_square_generic
    (tau : ℝ) (volume : ℕ) :
    (((volume ^ 3 : ℕ) : ℝ) ^ tau) ^ (2 : ℕ) =
      (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
  let v : ℝ := ((volume ^ 3 : ℕ) : ℝ)
  have hv : 0 ≤ v := by positivity
  have hcast : (((((volume ^ 3) ^ 2 : ℕ) : ℝ))) = v ^ (2 : ℕ) := by
    dsimp only [v]
    norm_num
  rw [hcast]
  change (v ^ tau) ^ (2 : ℕ) = ((v ^ (2 : ℕ)) ^ tau)
  rw [pow_two, ← Real.mul_rpow hv hv, ← pow_two]

/-- Any nonnegative pointwise exponential capacity bound for a one-half
C-tensor family squares to a finite six-symmetric extraction. -/
theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3}
    (tau C R : ℝ) (N A H volume : ℕ)
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hR : 0 ≤ R) (hH : 0 < H) (hHbound : H ≤ 4 ^ N)
    (hrate :
      R ^ (2 * N) *
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      R ^ (4 * N) *
          Real.exp (-(2 * C + 400) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  obtain ⟨q, a, b, c, hrestrict, hextract⟩ :=
    mme_Ctensor_one_half_family_to_six_finite_extraction
      tau N A H volume stars hH hHbound
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  let capacity : ℝ :=
    (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
      (((volume ^ 3 : ℕ) : ℝ) ^ tau)
  have hrate' : R ^ (2 * N) * Real.exp (-C * x) ≤ capacity := by
    simpa only [x, capacity] using hrate
  have hleft0 : 0 ≤ R ^ (2 * N) * Real.exp (-C * x) := by
    positivity
  have hsquared :
      (R ^ (2 * N) * Real.exp (-C * x)) ^ (2 : ℕ) ≤
        capacity ^ (2 : ℕ) :=
    pow_le_pow_left₀ hleft0 hrate' 2
  let sourceLoss : ℝ := Real.exp (-200 * x)
  let D : ℝ := (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2)
  let w : ℝ := (((volume ^ 3 : ℕ) : ℝ) ^ tau)
  have hweight : w ^ (2 : ℕ) =
      (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
    simpa only [w] using volume_weight_square_generic tau volume
  change R ^ (4 * N) * Real.exp (-(2 * C + 400) * x) ≤ _
  calc
    R ^ (4 * N) * Real.exp (-(2 * C + 400) * x) =
        (R ^ (2 * N) * Real.exp (-C * x)) ^ (2 : ℕ) *
          sourceLoss ^ (2 : ℕ) := by
      rw [exp_split_double_loss_generic]
      dsimp only [sourceLoss]
      have hRpow : R ^ (4 * N) =
          (R ^ (2 * N)) ^ (2 : ℕ) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hRpow, mul_pow]
      ring
    _ ≤ capacity ^ (2 : ℕ) * sourceLoss ^ (2 : ℕ) := by
      gcongr
    _ = (D * sourceLoss) ^ (2 : ℕ) *
          (((((volume ^ 3) ^ 2 : ℕ) : ℝ)) ^ tau) := by
      dsimp only [capacity, D, w]
      rw [← hweight]
      ring
    _ ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
      simpa only [D, sourceLoss] using hextract
