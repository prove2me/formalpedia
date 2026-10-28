-- Prove2me | Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
-- name    : D1Bound5.oneSmallCutoffRows_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:19:57.623447+00:00
-- url     : https://prove2.me/theorems/b1ab9c9e-c6f4-45c2-b980-0b7b92c39380
-- title:
--   One Small Cutoff Rows valid
-- statement:
--   Every arithmetic row is kernel checked separately.
-- source:
--   D1Bound5/OneSmallCutoffArithmetic.lean, lines 500-561, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002

section
namespace D1Bound5
open QuadInt



namespace OneSmallCutoffRow



























end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0








































































































































































































































theorem _root_.D1Bound5.oneSmallCutoffRows_valid (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) : r.Valid := by sorry





end D1Bound5
end
