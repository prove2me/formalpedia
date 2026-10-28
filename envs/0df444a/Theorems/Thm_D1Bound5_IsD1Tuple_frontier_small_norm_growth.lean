-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_frontier_small_norm_growth
-- name    : D1Bound5.IsD1Tuple.frontier_small_norm_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:30:43.157169+00:00
-- url     : https://prove2.me/theorems/067a5d73-330b-4f4c-83ac-7734e94a2dd0
-- title:
--   Is D1Tuple — frontier small norm growth
-- statement:
--   The five manuscript rows expressed using actual squared complex modulus, which the full-ring bridge identifies with the integral norm.
-- source:
--   D1Bound5/FrontierNormRows.lean, lines 8-63, SHA-256 ac2181984cc485611948ed65e1efa5572ea24edac09ef71b42dcdc907c5da46b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.frontier_small_norm_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let C := ‖phi (a 2 : K)‖
    let D := ‖phi (a 3 : K)‖
    (A^2 = 1 → 8 ≤ B → (27/8 : ℝ)*A*B*C < D) ∧
    (A^2 = 2 → 4 ≤ B → 3*A*B*C < D) ∧
    (A^2 = 3 → 3 ≤ B → (11/4 : ℝ)*A*B*C < D) ∧
    (A^2 = 4 → 3 ≤ B → (29/10 : ℝ)*A*B*C < D) ∧
    (5 ≤ A^2 → 3 ≤ B → 3*A*B*C < D) := by sorry

end D1Bound5
end
