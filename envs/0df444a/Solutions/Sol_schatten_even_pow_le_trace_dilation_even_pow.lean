-- Prove2me | solution 1 for schatten_even_pow_le_trace_dilation_even_pow
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T03:10:58.460994+00:00
-- url     : https://prove2.me/submissions/8d84c188-f268-45f3-936a-8edd40824e37

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Theorems.Thm_schatten_norm_even_pow_eq_trace_row_gram_pow
import Theorems.Thm_trace_dilation_even_pow

open Matrix MatrixCompletion
open scoped BigOperators

/-- **D1-link.** `schattenNorm(2n)(X)^{2n} ≤ tr((dilation X)^{2n})`, where
`dilation X = fromBlocks 0 X Xᵀ 0`.  Reduction: `schattenNorm` even-power = row-Gram trace
(197d0150), the dilation even power splits into the two Gram traces (trace_dilation_even_pow),
and the column-Gram trace is nonnegative (PSD). -/
theorem solution
    (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (X : MatrixCompletion.RealMatrix n1 n2) :
    MatrixCompletion.schattenNorm (2 * n) X ^ (2 * n)
      ≤ Matrix.trace ((Matrix.fromBlocks 0 X Xᵀ 0) ^ (2 * n)) := by
  rw [schatten_norm_even_pow_eq_trace_row_gram_pow n hn X, trace_dilation_even_pow]
  -- tr((XXᵀ)^n) ≤ tr((XXᵀ)^n) + tr((XᵀX)^n), since tr((XᵀX)^n) ≥ 0 (PSD power).
  have hPSD : (Xᵀ * X).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self X
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hpow : ((Xᵀ * X) ^ n).PosSemidef := hPSD.pow n
  have hnn : 0 ≤ Matrix.trace ((Xᵀ * X) ^ n) := hpow.trace_nonneg
  have hkey : Matrix.trace ((X * X.transpose) ^ n)
      ≤ Matrix.trace ((X * X.transpose) ^ n) + Matrix.trace ((Xᵀ * X) ^ n) := by linarith
  simpa using hkey

#print axioms solution
