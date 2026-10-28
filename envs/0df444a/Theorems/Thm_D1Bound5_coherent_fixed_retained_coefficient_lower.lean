-- Prove2me | Theorems.Thm_D1Bound5_coherent_fixed_retained_coefficient_lower
-- name    : D1Bound5.coherent_fixed_retained_coefficient_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:41:37.494428+00:00
-- url     : https://prove2.me/theorems/f0258166-9877-4533-8235-5629e3c91e08
-- title:
--   Coherent fixed retained coefficient lower
-- statement:
--   An upper enclosure for the normalized Vandermonde gives the conservative fixed-triple coefficient used in the cutoff table.
-- source:
--   D1Bound5/CoherentFixedCutoffGap.lean, lines 18-38, SHA-256 7b57e532eea2687c827f67852b4cd6905337d46cbb2737ea2584ace4cf557916. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.coherent_fixed_retained_coefficient_lower
    (A B R q : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hR : 0 < R)
    (hq : R ≤ q) (hsep : (51051/400000 : ℝ)/B^2 < 1/q) :
    (9999/100 : ℝ)*A^2*(1/q-(51051/400000 : ℝ)/B^2)^2 ≤
      (9999/100 : ℝ)*A^2*(1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by sorry



end D1Bound5
end
