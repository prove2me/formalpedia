-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_unit_pair_cubic_iteration
-- name    : D1Bound5.IsD1Tuple.unit_pair_cubic_iteration
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:37.650285+00:00
-- url     : https://prove2.me/theorems/111793d9-82f6-4099-9ac2-193c552b98f4
-- title:
--   Is D1Tuple — unit pair cubic iteration
-- statement:
--   The actual unit-pair sextuple already supplies every opposite-pair exclusion through the symmetric-five obstruction. Thus the three cubic steps require no extra hypothesis about signs of its four extensions.
-- source:
--   D1Bound5/UnitPairCubicIteration.lean, lines 21-73, SHA-256 a34fce4fbc0641e3fd4321f40ebb3bba4fb6d40eab6d0dad17f09e677f1ee8f7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.unit_pair_cubic_iteration
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hminus : a 0 = -1) (hplus : a 1 = 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hS : 9 ≤ ‖phi (a 2 : K)‖) :
    ‖phi (a 2 : K)‖^27/8192 < ‖phi (a 5 : K)‖ := by sorry

end D1Bound5
end
