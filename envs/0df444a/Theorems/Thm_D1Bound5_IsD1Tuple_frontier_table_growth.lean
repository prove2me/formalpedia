-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_frontier_table_growth
-- name    : D1Bound5.IsD1Tuple.frontier_table_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:38.858911+00:00
-- url     : https://prove2.me/theorems/62ac6ca7-f2df-4826-aff8-64fc5054d5df
-- title:
--   Is D1Tuple — frontier table growth
-- statement:
--   All five small-first-entry frontier table rows hold for actual ordered D(1)-quadruples. The rational lower bounds and row thresholds are explicit.
-- source:
--   D1Bound5/FrontierTableTuple.lean, lines 132-169, SHA-256 825d1a404b788cce31247867a1ebcc65335780ae7cffd51ce40acd5d2a05e230. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.frontier_table_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (alpha beta target : ℝ) (hrow : FrontierTableRow alpha beta target)
    (hA : alpha ≤ ‖phi (a 0 : K)‖) (hB : beta ≤ ‖phi (a 1 : K)‖)
    (hsmall : ‖phi (a 0 : K)‖ < 3) :
    target*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ := by sorry

end D1Bound5
end
