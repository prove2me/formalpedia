-- Prove2me | Theorems.Thm_Algebra_norm_tensorProduct_includeRight
-- name    : Algebra.norm_tensorProduct_includeRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:26.249878+00:00
-- url     : https://prove2.me/theorems/969de1ab-d3f1-4c9e-98d8-a8c357b5bee5
-- title:
--   Algebra: norm tensor Product include Right
-- statement:
--   Regular algebra norm commutes with scalar extension, stated for the
--   canonical inclusion into a tensor product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L232-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L232-L242

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
set_option autoImplicit false
open scoped Matrix
open Algebra

theorem Algebra.norm_tensorProduct_includeRight
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.norm L (Algebra.TensorProduct.includeRight x :
        TensorProduct K L A) =
      algebraMap K L (Algebra.norm K x) := by sorry
