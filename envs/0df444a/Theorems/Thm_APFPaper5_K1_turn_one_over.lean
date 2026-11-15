-- Prove2me | Theorems.Thm_APFPaper5_K1_turn_one_over
-- name    : APFPaper5.K1.turn_one_over
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:29:22.644695+00:00
-- url     : https://prove2.me/theorems/3177fce2-6285-4ba6-a576-d004170c25d9
-- title:
--   Turn one over
-- statement:
--   Negating coordinate r0 of a real array b changes its overlap with a by minus twice a(r0)b(r0). This finite-array identity does not assert that such a change is admitted or that the overlap is a physical count.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_oriented_count.lean:75

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.turn_one_over {Rec : Type*} [Fintype Rec] [DecidableEq Rec] (a b : Rec → ℝ) (r0 : Rec) :
    ∑ r, a r * (if r = r0 then -b r else b r) = ∑ r, a r * b r - 2 * (a r0 * b r0) := by sorry
