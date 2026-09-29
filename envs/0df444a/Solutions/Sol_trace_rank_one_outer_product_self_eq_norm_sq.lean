-- Prove2me | solution 1 for trace_rank_one_outer_product_self_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:57.36295+00:00
-- url     : https://prove2.me/submissions/e2c4f8aa-4362-4e74-a9ab-1f57c74dd953

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y : Fin d → ℝ) :
    Matrix.trace (Matrix.vecMulVec y y) = ∑ i, (y i) ^ 2 := by
  unfold Matrix.trace Matrix.vecMulVec
  simp [Matrix.diag, sq]
