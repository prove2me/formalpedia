-- Prove2me | Theorems.Thm_D1Bound5_fiveRegion_common_overlap_bounds
-- name    : D1Bound5.fiveRegion_common_overlap_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:10:30.961386+00:00
-- url     : https://prove2.me/theorems/a43e7351-171a-4aad-8a25-45cb453f962b
-- title:
--   Five Region common overlap bounds
-- statement:
--   The sixteen exact overlap comparisons are checked at the rational lower corner A²=n, B=S=m, then transported monotonically. No numerical certificate is assumed at the endpoint.
-- source:
--   D1Bound5/FiveRegionOverlapBounds.lean, lines 19-112, SHA-256 c9fdaf0fa8a097761cb5dbeb7193ef7a655c5e9afed51f304ec575e825b4efde. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions

section
namespace D1Bound5



set_option maxHeartbeats 8000000 in

theorem _root_.D1Bound5.fiveRegion_common_overlap_bounds (r : Fin 5) (A B S : ℝ)
    (hAn : fiveRegionMinNorm r ≤ A^2)
    (hBm : fiveRegionMinB r ≤ B) (hBS : B ≤ S) :
    CommonOverlapBounds A B S (fiveRegionGap r) (fiveRegionCoupledGap r) 1
      (fiveRegionN2Height r) (fiveRegionN3Height r) (fiveRegionA3Height r)
      (fiveRegionA4Height r) (fiveRegionA5Height r) 4143
      (fiveRegionN2Residual r) (fiveRegionN3Residual r) (fiveRegionA3Residual r)
      (fiveRegionA4Residual r) (fiveRegionA5Residual r) (fiveRegionPResidual r) := by sorry

end D1Bound5
end
