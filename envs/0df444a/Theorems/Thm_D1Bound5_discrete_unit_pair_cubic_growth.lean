-- Prove2me | Theorems.Thm_D1Bound5_discrete_unit_pair_cubic_growth
-- name    : D1Bound5.discrete_unit_pair_cubic_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:31.397622+00:00
-- url     : https://prove2.me/theorems/33dabead-14cd-4872-ad99-c9e2c39e42ee
-- title:
--   Discrete unit pair cubic growth
-- statement:
--   The unit cubic gap in any discrete complex ring image. Both signs are selected among the original ring roots; the lower bound on the nonzero second-order form is derived from discreteness.
-- source:
--   D1Bound5/UnitPairCubic.lean, lines 51-119, SHA-256 16469c8d22e15a9b7e3513551fcffe914102a558214dd99c81069f9bf0bf3a9f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.discrete_unit_pair_cubic_growth
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (hdiscrete : ∀ x : R, x ≠ 0 → 1 ≤ ‖f x‖)
    (c d z u v : R) (hC : 9 ≤ ‖f c‖) (hCD : ‖f c‖ ≤ ‖f d‖)
    (hneq : f c+f d ≠ 0)
    (hz : z^2 = c*d+1) (hu : u^2 = (c+1)*(d+1))
    (hv : v^2 = (1-c)*(1-d)) : ‖f c‖^3/2 < ‖f d‖ := by sorry





end D1Bound5
end
