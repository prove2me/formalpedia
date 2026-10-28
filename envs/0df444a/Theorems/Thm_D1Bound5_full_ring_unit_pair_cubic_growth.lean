-- Prove2me | Theorems.Thm_D1Bound5_full_ring_unit_pair_cubic_growth
-- name    : D1Bound5.full_ring_unit_pair_cubic_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:38:12.046987+00:00
-- url     : https://prove2.me/theorems/71238614-e02f-4ba4-ad21-b9e946f577fa
-- title:
--   Full ring unit pair cubic growth
-- statement:
--   Actual common extensions of {-1,1} satisfy the manuscript cubic gap. All five square witnesses are in the full integer ring; no analytic branch, root nonvanishing, or auxiliary form estimate is a premise.
-- source:
--   D1Bound5/UnitPairCubic.lean, lines 121-153, SHA-256 16469c8d22e15a9b7e3513551fcffe914102a558214dd99c81069f9bf0bf3a9f. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.full_ring_unit_pair_cubic_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (c d : 𝓞 K) (hC : 9 ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖) (hneq : d ≠ -c)
    (hcp : ∃ r : 𝓞 K, r^2 = c+1) (hcm : ∃ r : 𝓞 K, r^2 = 1-c)
    (hdp : ∃ r : 𝓞 K, r^2 = d+1) (hdm : ∃ r : 𝓞 K, r^2 = 1-d)
    (hcd : ∃ r : 𝓞 K, r^2 = c*d+1) :
    ‖phi (c : K)‖^3/2 < ‖phi (d : K)‖ := by sorry



end D1Bound5
end
