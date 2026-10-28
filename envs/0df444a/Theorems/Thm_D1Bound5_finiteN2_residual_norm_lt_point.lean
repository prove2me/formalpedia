-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_residual_norm_lt_point
-- name    : D1Bound5.finiteN2_residual_norm_lt_point
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:01.687989+00:00
-- url     : https://prove2.me/theorems/1b74cd78-17f1-43be-934f-d6b01668fab6
-- title:
--   Finite N2 residual norm lt point
-- statement:
--   The actual finite N2 point residual, preserving the distance factor needed by the fixed-anchor interval tables. This is exactly the paper's max(delta^4,u*delta^3) normalization, with denominators multiplied out.
-- source:
--   D1Bound5/FiniteN2Residual.lean, lines 72-115, SHA-256 09991a5abb38bf67b662f328fce0c115f0f5cfc405bf2c1077362baa797bfe9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions

section
namespace D1Bound5












theorem _root_.D1Bound5.finiteN2_residual_norm_lt_point (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteN2Residual x y c i‖ <
      (101/2560 : ℝ)*max (‖x-y‖^4) (‖x‖*‖x-y‖^3) /
        (‖x‖^3*‖y‖^2*‖c‖^4) := by sorry



end D1Bound5
end
