-- Prove2me | Theorems.Thm_D1Bound5_finiteN2RowForm_norm_lt_refined
-- name    : D1Bound5.finiteN2RowForm_norm_lt_refined
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:53.412563+00:00
-- url     : https://prove2.me/theorems/29a268d5-294b-4971-b4dc-b12a2e36e7c5
-- title:
--   Finite N2Row Form norm lt refined
-- statement:
--   An explicit coefficient-height refinement for the actual finite N2 row. The full-ring application supplies the actual residual bound separately.
-- source:
--   D1Bound5/FiniteN2HeightRefinement.lean, lines 8-38, SHA-256 b1126c09dc8f65e44341e2b5079d83bdc6a616c2b86378feaae223739d8bfcb0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.finiteN2RowForm_norm_lt_refined
    (x y c z sX sY : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (i : Fin 3) (M : ℝ)
    (hheightScaled : (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      M*‖y‖^4*‖c‖^2)
    (herr : ∀ j : Fin 2,
      ‖(1+1/(![x,y] j*c))^(1/2 : ℂ)-![sX,sY] j/(![x,y] j*z)‖ ≤
        (101/100 : ℝ)*‖c‖/(‖![x,y] j‖*‖z‖^2))
    (R : ℝ) (hres : ‖finiteN2Residual x y c i‖ < R) :
    ‖finiteN2RowForm x y c z sX sY i‖ <
      M*‖y‖^4*‖c‖^3/‖z‖+R*‖z‖ := by sorry



end D1Bound5
end
