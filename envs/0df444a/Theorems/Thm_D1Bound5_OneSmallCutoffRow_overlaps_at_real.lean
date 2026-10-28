-- Prove2me | Theorems.Thm_D1Bound5_OneSmallCutoffRow_overlaps_at_real
-- name    : D1Bound5.OneSmallCutoffRow.overlaps_at_real
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:36.164725+00:00
-- url     : https://prove2.me/theorems/83de4497-a431-4ab9-bcdf-27d7ac663ed0
-- title:
--   One Small Cutoff Row — overlaps at real
-- statement:
--   Every strict rational overlap at the cutoff remains strict for all larger real squared fourth moduli.
-- source:
--   D1Bound5/OneSmallCutoffReal.lean, lines 6-25, SHA-256 cfc21933cb4a82de4a9d5409cd9e6c6bc2d0d33f2b3a2f409c936a0b91b57d93. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.OneSmallCutoffRow.overlaps_at_real (r : OneSmallCutoffRow)
    (hv : r.Valid) (x : ℝ) (hx : (r.triple.cutoff : ℝ) ≤ x)
    (e : ℚ × ℕ) (he : e ∈ r.overlaps) :
    1 < (e.1 : ℝ)*x^e.2 := by sorry





end D1Bound5
end
