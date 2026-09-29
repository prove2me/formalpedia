-- Prove2me | solution 1 for rank_one_outer_product_self_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:56.027405+00:00
-- url     : https://prove2.me/submissions/7df5db5b-8cc9-4ab4-9d84-b7e3c16673e3

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y : Fin d → ℝ) :
    (Matrix.vecMulVec y y)ᵀ = Matrix.vecMulVec y y := by
  ext i j
  simp [Matrix.vecMulVec, Matrix.transpose_apply, mul_comm]
