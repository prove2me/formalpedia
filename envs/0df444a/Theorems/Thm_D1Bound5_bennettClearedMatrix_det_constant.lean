-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedMatrix_det_constant
-- name    : D1Bound5.bennettClearedMatrix_det_constant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:33.351384+00:00
-- url     : https://prove2.me/theorems/ab206e81-3fb0-40fc-8a17-5f354b13a7ec
-- title:
--   Bennett Cleared Matrix det constant
-- statement:
--   The cleared determinant is a constant polynomial. Consequently evaluation at a removed node, including zero, is justified algebraically.
-- source:
--   D1Bound5/BennettDeterminantConstant.lean, lines 54-73, SHA-256 267ae930e881e7b102ec7dd3ddb0469bc45ab29e4985e0503efec75e7c50bb50. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions

section
open Finset

namespace D1Bound5

variable {F I : Type*} [Field F] [CharZero F]
variable [Fintype I] [DecidableEq I]








theorem _root_.D1Bound5.bennettClearedMatrix_det_constant
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) :
    (bennettClearedMatrix a k ν).det =
      Polynomial.C ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k)) := by sorry



end D1Bound5
end
