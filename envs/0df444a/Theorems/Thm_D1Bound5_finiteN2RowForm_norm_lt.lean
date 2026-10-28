-- Prove2me | Theorems.Thm_D1Bound5_finiteN2RowForm_norm_lt
-- name    : D1Bound5.finiteN2RowForm_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:10:17.488985+00:00
-- url     : https://prove2.me/theorems/55856ba1-23cb-4265-bada-aa18dc25fdf6
-- title:
--   Finite N2Row Form norm lt
-- statement:
--   Auxiliary result `finiteN2RowForm_norm_lt` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN2RowBound.lean, lines 43-55, SHA-256 6f0207b10b2a70e7967c5e96a3986e3a4d2212927188610be70b6ef039b6d4b8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
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
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions

section
namespace D1Bound5





theorem _root_.D1Bound5.finiteN2RowForm_norm_lt
    (x y c z sX sY : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0)
    (hxy : x ≠ y) (hz : z ≠ 0) (hXY : ‖x‖ ≤ ‖y‖)
    (hXC : 1000 ≤ ‖x‖*‖c‖)
    (herr : ∀ j : Fin 2,
      ‖(1+1/(![x,y] j*c))^(1/2 : ℂ)-![sX,sY] j/(![x,y] j*z)‖ ≤
        (101/100 : ℝ)*‖c‖/(‖![x,y] j‖*‖z‖^2)) (i : Fin 3) :
    ‖finiteN2RowForm x y c z sX sY i‖ <
      243*‖y‖^4*‖c‖^3/‖z‖ + (5/4 : ℝ)*‖y‖^2*‖z‖/(‖x‖^3*‖c‖^4) := by sorry



end D1Bound5
end
