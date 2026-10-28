-- Prove2me | Theorems.Thm_D1Bound5_exists_integral_root_rational_envelope
-- name    : D1Bound5.exists_integral_root_rational_envelope
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:44.352344+00:00
-- url     : https://prove2.me/theorems/8eb8ca8d-3d27-4b3e-a09b-1d19b27ef5c9
-- title:
--   Exists integral root rational envelope
-- statement:
--   Select the sign inside the original ring while retaining its exact square equation. The source root is allowed to be zero.
-- source:
--   D1Bound5/FrontierFifteenRootError.lean, lines 31-50, SHA-256 24dc95017a8ebeb8c577aed5d93ddcda41177bb23f3f88798738501f0f343cfb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.exists_integral_root_rational_envelope
    {R : Type*} [CommRing R] (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b) (hr : r^2 = a*b+1)
    (m c k : ℝ) (hm : 0 < m) (hc : 0 ≤ c) (hk : 1/2 < k)
    (hgap : 1 < (1-c^2)*m) (hprecision : 1 ≤ 2*m*(1+c)^2*(k-1/2))
    (hab : m ≤ ‖f a*f b‖) :
    ∃ q : R, q^2 = a*b+1 ∧ ‖u*f q*v-f a*f b-(1/2 : ℂ)‖ ≤ k-1/2 := by sorry







end D1Bound5
end
