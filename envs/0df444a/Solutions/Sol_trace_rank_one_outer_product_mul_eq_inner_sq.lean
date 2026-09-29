-- Prove2me | solution 1 for trace_rank_one_outer_product_mul_eq_inner_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:54.68788+00:00
-- url     : https://prove2.me/submissions/180841e5-4b0c-4775-88c6-19c105b1d675

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y z : Fin d → ℝ) :
    Matrix.trace (Matrix.vecMulVec y y * Matrix.vecMulVec z z) = (y ⬝ᵥ z) ^ 2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  unfold Matrix.trace Matrix.vecMulVec
  simp only [Matrix.diag_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have hstep : ∀ x, y x * ((y ⬝ᵥ z) * z x) = (y ⬝ᵥ z) * (y x * z x) := fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum]
  rw [show (y ⬝ᵥ z) = ∑ i, y i * z i from rfl]; ring
