-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_hasSum
-- name    : D1Bound5.bennettPolynomialResidue_residual_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:34.40246+00:00
-- url     : https://prove2.me/theorems/021a4b3e-7423-4a6e-bec6-a8f1e60a3b14
-- title:
--   Bennett Polynomial Residue residual has Sum
-- statement:
--   The actual finite row of residue polynomials times the complex powers is the sum of its actual formal coefficients. No residual identity is assumed.
-- source:
--   D1Bound5/BennettResidualEvaluation.lean, lines 78-95, SHA-256 d030bc1b298c007855437a873b058dcac35949cc3daa110cf555bdf87d4fd831. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]


theorem _root_.D1Bound5.bennettPolynomialResidue_residual_hasSum
    (a : I → ℂ) (k : ℕ) (ν x : ℂ) (i : I)
    (hx : ∀ j, ‖a j * x‖ < 1) :
    HasSum (fun r : ℕ => PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue univ a k ν i j : PowerSeries ℂ) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν)) * x ^ r)
      (∑ j, (bennettPolynomialResidue univ a k ν i j).eval x *
        (1 + a j * x) ^ ν) := by sorry





end Nodes

end D1Bound5
end
