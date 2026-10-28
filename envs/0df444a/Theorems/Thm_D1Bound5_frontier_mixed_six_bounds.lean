-- Prove2me | Theorems.Thm_D1Bound5_frontier_mixed_six_bounds
-- name    : D1Bound5.frontier_mixed_six_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:06.691149+00:00
-- url     : https://prove2.me/theorems/e9e10c8d-31b4-4934-9ff4-9b14f1912eff
-- title:
--   Frontier mixed six bounds
-- statement:
--   Exact mixed-envelope bounds for the normalized four-by-four matrix. Every cubic cofactor term has at least one later edge and at most two first-row edges, so K=k^2*l bounds all cubic products.
-- source:
--   D1Bound5/FrontierMixedCofactors.lean, lines 7-142, SHA-256 8b0b4e502bb0feb79ed7c1e76ce6284a21b166f5b473df451378ff6e7d9d01d8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.frontier_mixed_six_bounds (x y z u v w : ℂ) (k l : ℝ)
    (hl : (1/2 : ℝ) ≤ l) (hlk : l ≤ k)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ k-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ k-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ k-1/2)
    (hu : ‖u-(1/2 : ℂ)‖ ≤ l-1/2)
    (hv : ‖v-(1/2 : ℂ)‖ ≤ l-1/2)
    (hw : ‖w-(1/2 : ℂ)‖ ≤ l-1/2) :
    let F : Matrix (Fin 4) (Fin 4) ℂ := !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]
    ‖F.det‖ ≤ 9*k^2*l^2 ∧
    ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*(k^2*l) else 3*(k^2*l)-1/4 := by sorry

end D1Bound5
end
