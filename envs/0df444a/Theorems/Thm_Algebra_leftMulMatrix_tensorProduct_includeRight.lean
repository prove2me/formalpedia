-- Prove2me | Theorems.Thm_Algebra_leftMulMatrix_tensorProduct_includeRight
-- name    : Algebra.leftMulMatrix_tensorProduct_includeRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:55:03.493201+00:00
-- url     : https://prove2.me/theorems/336187b9-82c9-40e6-ac80-c30594b074c8
-- title:
--   Algebra: left Mul Matrix tensor Product include Right
-- statement:
--   In the scalar-extended basis, left multiplication by `1 ⊗ x` is the
--   entrywise scalar extension of the original left-multiplication matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L216-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L216-L228

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
set_option autoImplicit false
open scoped Matrix
open Algebra

theorem Algebra.leftMulMatrix_tensorProduct_includeRight
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis L b)
        (Algebra.TensorProduct.includeRight x) =
      (Algebra.leftMulMatrix b x).map (algebraMap K L) := by sorry
