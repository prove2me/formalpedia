-- Prove2me | Theorems.Thm_D1Bound5_unequalPolePolynomial_residual_hasSum
-- name    : D1Bound5.unequalPolePolynomial_residual_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:45.342721+00:00
-- url     : https://prove2.me/theorems/08dfc312-a0e7-4d84-a902-2c7fe64368c1
-- title:
--   Unequal Pole Polynomial residual has Sum
-- statement:
--   Auxiliary result `unequalPolePolynomial_residual_hasSum` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/UnequalPoleResidual.lean, lines 18-32, SHA-256 e46f9575bbcd97addd0307c7ad2e250b7b7f566707b1c1322ce262892ab0777e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_UnequalPoleResidual_Definitions

section
open Finset

namespace D1Bound5

variable {I : Type*} [Fintype I] [DecidableEq I]



theorem _root_.D1Bound5.unequalPolePolynomial_residual_hasSum
    (a : I → ℂ) (e : I → ℕ) (k : ℕ) (ν x : ℂ)
    (hx : ∀ j, ‖a j*x‖ < 1) :
    HasSum (fun r : ℕ => PowerSeries.coeff r
      (∑ j, (unequalPolePolynomial a e k ν j : PowerSeries ℂ)*
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries ℂ ν))*x^r)
      (∑ j, (unequalPolePolynomial a e k ν j).eval x*(1+a j*x)^ν) := by sorry









end D1Bound5
end
