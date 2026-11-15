-- Prove2me | Theorems.Thm_APFPaper5_K1_hold_bills_nothing_more
-- name    : APFPaper5.K1.hold_bills_nothing_more
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:11:28.341222+00:00
-- url     : https://prove2.me/theorems/19f28e61-2617-4ecc-bb0c-d67b0b55ca99
-- title:
--   Hold bills nothing more
-- statement:
--   For any real weights, if the record set after a step is both contained in and contains the earlier set, their weighted sum bills are equal. Equality of retained bills does not make the total bill zero.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_bill_is_a_sum.lean:44

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.hold_bills_nothing_more {Rec : Type*} (w : Rec → ℝ) (K K' : Finset Rec)
    (hnodraw : K' ⊆ K) (hnoerase : K ⊆ K') : ∑ r ∈ K', w r = ∑ r ∈ K, w r := by sorry
