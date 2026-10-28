-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoResidualRate_pos
-- name    : D1Bound5.bennettTwoResidualRate_pos
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:20:17.660804+00:00
-- url     : https://prove2.me/theorems/af0f40f6-0fe6-423b-ad90-a32ace4d4f1a
-- title:
--   Bennett Two Residual Rate pos
-- statement:
--   Auxiliary result `bennettTwoResidualRate_pos` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettTwoResidualRate.lean, lines 16-22, SHA-256 a959de125fdeac3f4cd04800acc29e3af47d9b0e2de609a39d3e257a4ba1c377. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
namespace D1Bound5





theorem _root_.D1Bound5.bennettTwoResidualRate_pos (A B C δ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (hAC : 1 < A * C) :
    0 < bennettTwoResidualRate A B C δ := by sorry







end D1Bound5
end
