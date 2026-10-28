-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_frontier_determinant_envelope
-- name    : D1Bound5.IsD1Tuple.frontier_determinant_envelope
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:02.917704+00:00
-- url     : https://prove2.me/theorems/efe55e87-78a7-4c0b-9a64-f349fdfb81fb
-- title:
--   Is D1Tuple — frontier determinant envelope
-- statement:
--   The actual scaled integral determinant obeys the complete frontier envelope, with constants evaluated at any positive lower bounds alpha,beta having alpha<=beta and alpha*beta>=5.
-- source:
--   D1Bound5/FrontierTableTuple.lean, lines 10-130, SHA-256 825d1a404b788cce31247867a1ebcc65335780ae7cffd51ce40acd5d2a05e230. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.frontier_determinant_envelope
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (halphabeta : alpha ≤ beta) (hprod : 5 ≤ alpha*beta)
    (hA : alpha ≤ ‖phi (a 0 : K)‖) (hB : beta ≤ ‖phi (a 1 : K)‖) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let C := ‖phi (a 2 : K)‖
    let D := ‖phi (a 3 : K)‖
    A*B*C*D ≤ 2*frontierK alpha beta*(A^2+B^2+C^2+D^2)+
      frontierL alpha beta*(A*B+A*C+A*D+B*C+B*D+C*D)+frontierQ alpha beta := by sorry



end D1Bound5
end
