-- Prove2me | Theorems.Thm_D1Bound5_OneSmallCutoffRow_start_overlap_real
-- name    : D1Bound5.OneSmallCutoffRow.start_overlap_real
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:22:22.257234+00:00
-- url     : https://prove2.me/theorems/d7b6eeb8-df83-48d2-b85b-2880e5f09519
-- title:
--   One Small Cutoff Row — start overlap real
-- statement:
--   The first table inequality is exactly the strict overlap of the retained direct-four start with the finite Q interval.
-- source:
--   D1Bound5/OneSmallCutoffReal.lean, lines 27-41, SHA-256 cfc21933cb4a82de4a9d5409cd9e6c6bc2d0d33f2b3a2f409c936a0b91b57d93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.OneSmallCutoffRow.start_overlap_real (r : OneSmallCutoffRow)
    (hv : r.Valid) (S T : ℝ) (hS : 0 < S)
    (hSsq : S^2 = (r.s0 : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ T^2) :
    1 < (1-1/4000 : ℝ)*(r.retainedCoefficient : ℝ)^4*T^10/(12100*S^10) := by sorry



end D1Bound5
end
