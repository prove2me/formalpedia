-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_tail_hasSum
-- name    : D1Bound5.bennettPolynomialResidue_residual_tail_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:13.980369+00:00
-- url     : https://prove2.me/theorems/1f0288e4-c6fd-4ef2-adf3-aba348b857a8
-- title:
--   Bennett Polynomial Residue residual tail has Sum
-- statement:
--   After the proved cancellation, the actual analytic residual is exactly the high-degree residue-moment tail.
-- source:
--   D1Bound5/BennettResidualEvaluation.lean, lines 133-165, SHA-256 d030bc1b298c007855437a873b058dcac35949cc3daa110cf555bdf87d4fd831. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]






theorem _root_.D1Bound5.bennettPolynomialResidue_residual_tail_hasSum
    (a : I → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν x : ℂ) (i : I) (hx : ∀ j, ‖a j * x‖ < 1) :
    HasSum (fun t : ℕ =>
      (Ring.choose ((k : ℂ) + ν) (Fintype.card I * k + t) *
        ∑ j, bennettLocalResidue a
          (fun l => k + (if i = l then 1 else 0) - 1)
          (Polynomial.X ^ (Fintype.card I * k + t)) j) *
            x ^ (Fintype.card I * k + t))
      (∑ j, (bennettPolynomialResidue univ a k ν i j).eval x *
        (1 + a j * x) ^ ν) := by sorry

end Nodes

end D1Bound5
end
