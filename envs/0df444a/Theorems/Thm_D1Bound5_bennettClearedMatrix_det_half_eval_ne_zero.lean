-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedMatrix_det_half_eval_ne_zero
-- name    : D1Bound5.bennettClearedMatrix_det_half_eval_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:28.768869+00:00
-- url     : https://prove2.me/theorems/1ee60bff-5f54-4d3b-9ea8-cb2d2d42804e
-- title:
--   Bennett Cleared Matrix det half eval ne zero
-- statement:
--   The actual cleared Bennett matrix is nonsingular at every specialization, for every positive order and every number of distinct nodes containing zero.
-- source:
--   D1Bound5/BennettDeterminantNonzero.lean, lines 31-40, SHA-256 164557a33c15c3cbb3b959546eec9a30e4643b3c84fcd2c4978c868aa62a1f8f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennettClearedMatrix_det_half_eval_ne_zero
    (n : ℕ) (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (k : ℕ) (hk : 1 ≤ k) (h0 : a 0 = 0) (N : F) :
    (bennettClearedMatrix a k (1 / 2 : F)).det.eval N ≠ 0 := by sorry



end D1Bound5
end
