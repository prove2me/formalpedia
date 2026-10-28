-- Prove2me | Theorems.Thm_D1Bound5_frontier_fifteen_matrix_bounds
-- name    : D1Bound5.frontier_fifteen_matrix_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:49:21.699215+00:00
-- url     : https://prove2.me/theorems/292ff2fa-f749-4c04-af0c-7fe3fd49ef3b
-- title:
--   Frontier fifteen matrix bounds
-- statement:
--   Auxiliary result `frontier_fifteen_matrix_bounds` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FrontierFifteenNumeric.lean, lines 100-118, SHA-256 3122c98662e60a3fcf8105b6ce6ac200558a87cd3502de98958615f5f2e0f062. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FrontierFifteenCofactors_Definitions
import Definitions.Def_D1Bound5_FrontierFifteenRootError_Definitions

section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace D1Bound5



theorem _root_.D1Bound5.frontier_fifteen_matrix_bounds (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0) (hs : ∀ i j, F i j = F j i)
    (he : ∀ i j, i ≠ j → ‖F i j-(1/2 : ℂ)‖ ≤ frontierFifteenK i j-1/2) :
    ‖F.det‖ ≤ 1 ∧ ∀ i j, ‖F.adjugate i j‖ ≤ frontierFifteenG i j := by sorry



end D1Bound5
end
