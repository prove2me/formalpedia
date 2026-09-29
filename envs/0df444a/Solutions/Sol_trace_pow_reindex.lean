-- Prove2me | solution 1 for trace_pow_reindex
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:30:50.514118+00:00
-- url     : https://prove2.me/submissions/300219f9-3bd0-4864-9aac-b52c00743056

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection

open scoped BigOperators
open Matrix

theorem solution {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing R] (M : Matrix m m R) (e : m ≃ n) (k : ℕ) :
    Matrix.trace ((M.reindex e e) ^ k) = Matrix.trace (M ^ k) := by
  classical
  -- reindex commutes with powers
  have reindex_pow : ∀ j : ℕ, (M.reindex e e) ^ j = (M ^ j).reindex e e := by
    intro j
    induction j with
    | zero => simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    | succ i ih =>
        rw [pow_succ, pow_succ, ih]
        simp only [Matrix.reindex_apply]
        rw [Matrix.submatrix_mul_equiv (M ^ i) M e.symm e.symm e.symm]
  -- trace is reindex-invariant
  have trace_reindex : ∀ (P : Matrix m m R), Matrix.trace (P.reindex e e) = Matrix.trace P := by
    intro P
    unfold Matrix.trace Matrix.diag
    rw [← Equiv.sum_comp e (fun i => (P.reindex e e) (i) (i))]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [reindex_pow, trace_reindex]
