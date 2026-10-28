-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFixedRows_cutoff_member
-- name    : D1Bound5.oneSmallFixedRows_cutoff_member
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:25.279984+00:00
-- url     : https://prove2.me/theorems/725c2da8-ef4b-45ef-beef-1069de3e4d08
-- title:
--   One Small Fixed Rows cutoff member
-- statement:
--   The finite triple classifier supplies an actual member of the analytic cutoff table, rather than just an isolated valid record.
-- source:
--   D1Bound5/OneSmallFixedCutoffMember.lean, lines 5-15, SHA-256 f2b0eae3373284ad6a89b1f5f357c71fd0c3f3e32dcb1405a1ca20c02bc46741. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.oneSmallFixedRows_cutoff_member (r : OneSmallTripleRow)
    (hr : r ∈ oneSmallFixedRows) :
    ∃ c ∈ oneSmallCutoffRows, c.triple = r := by sorry

end D1Bound5
end
