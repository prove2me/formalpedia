-- Prove2me | Theorems.Thm_D1Bound5_frontier_fifteen_six_bounds
-- name    : D1Bound5.frontier_fifteen_six_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:46:31.979161+00:00
-- url     : https://prove2.me/theorems/54025305-67c4-4ca4-aa1f-d947acb3844b
-- title:
--   Frontier fifteen six bounds
-- statement:
--   Auxiliary result `frontier_fifteen_six_bounds` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FrontierFifteenCofactors.lean, lines 65-185, SHA-256 829c42be3230279544c3ada7eba6c524a34af4542d6dc0b41600e5c49f9ec39c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Matrix

namespace D1Bound5







theorem _root_.D1Bound5.frontier_fifteen_six_bounds (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ (5506/10000 : ℝ)-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ (5087/10000 : ℝ)-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ (5014/10000 : ℝ)-1/2)
    (hu : ‖u-(1/2 : ℂ)‖ ≤ (5029/10000 : ℝ)-1/2)
    (hv : ‖v-(1/2 : ℂ)‖ ≤ (5005/10000 : ℝ)-1/2)
    (hw : ‖w-(1/2 : ℂ)‖ ≤ (5001/10000 : ℝ)-1/2) :
    let F : Matrix (Fin 4) (Fin 4) ℂ := !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]
    ‖F.det‖ ≤ 1 ∧ ∀ i j, ‖F.adjugate i j‖ ≤ frontierFifteenG i j := by sorry

end D1Bound5
end
