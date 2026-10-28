-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedMatrix_det_eval_zero_formula
-- name    : D1Bound5.bennettClearedMatrix_det_eval_zero_formula
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:16.829988+00:00
-- url     : https://prove2.me/theorems/afa020d4-7ed0-425f-a7c1-e066df6800e2
-- title:
--   Bennett Cleared Matrix det eval zero formula
-- statement:
--   Exact all-order determinant evaluation. In the induction the final node is removed, retaining the distinguished zero node in every nonempty prefix.
-- source:
--   D1Bound5/BennettDeterminantFormula.lean, lines 62-104, SHA-256 f98a83f3277331ffd79b4bad983ece2c8026e08c5e60f13dc8b325624528de0f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]










theorem _root_.D1Bound5.bennettClearedMatrix_det_eval_zero_formula (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ) (a : Fin (n + 1) → F), Function.Injective a →
      ∀ (ν : F), a 0 = 0 →
        (bennettClearedMatrix a k ν).det.eval 0 =
          bennettBinomialProduct (n + 1) k ν * bennettDirectedProduct a k := by sorry





end D1Bound5
end
