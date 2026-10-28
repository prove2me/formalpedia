-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_residual_norm_lt_refined
-- name    : D1Bound5.finiteN3_residual_norm_lt_refined
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:56.357993+00:00
-- url     : https://prove2.me/theorems/c31fc4f6-86ba-4377-a9ae-1431f45607e4
-- title:
--   Finite N3 residual norm lt refined
-- statement:
--   A proved distance enclosure supplies the residual constant for the actual N3 family. This supports both fixed ab and relabeled bs anchors.
-- source:
--   D1Bound5/FiniteN3RefinedResidual.lean, lines 41-57, SHA-256 0295ce772ecf9751263aff0b8d27649f592a52d5790634adaaa8e26b884eb51a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN3Residual_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.finiteN3_residual_norm_lt_refined (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖)
    (R : ℝ)
    (hdistance : (3535/409600 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤
      R*‖y‖^6) (i : Fin 3) :
    ‖finiteN3Residual x y c i‖ < R*‖y‖^3/(‖x‖^4*‖c‖^6) := by sorry

end D1Bound5
end
