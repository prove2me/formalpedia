-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_rational_first_pair_third_eq_eight
-- name    : D1Bound5.IsD1Tuple.rational_first_pair_third_eq_eight
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:03.158888+00:00
-- url     : https://prove2.me/theorems/c9fada30-d291-4ded-90c8-d3c6975644f2
-- title:
--   Is D1Tuple — rational first pair third eq eight
-- statement:
--   Every ordered actual sextuple beginning with the signed rational pair has the same signed8 as its third entry. The fixed field is unchanged.
-- source:
--   D1Bound5/RationalFirstTriple.lean, lines 9-63, SHA-256 ec1ac5de875e09a521e7a6eb080ad83829858bc64b6e20605fb5ad65cd1bb9b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.rational_first_pair_third_eq_eight
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (sgn : Bool) (hx : a 0 = if sgn then -1 else 1)
    (hy : a 1 = if sgn then -3 else 3) :
    a 2 = if sgn then -8 else 8 := by sorry

end D1Bound5
end
