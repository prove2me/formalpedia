-- Prove2me | Theorems.Thm_APFPaper5_K1_overlap_between_bounds
-- name    : APFPaper5.K1.overlap_between_bounds
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:11:41.387654+00:00
-- url     : https://prove2.me/theorems/c340c904-e12d-415c-9f4c-326948183bea
-- title:
--   Overlap between bounds
-- statement:
--   For finite real arrays a,b, twice their dot product lies between minus and plus the sum of their square norms. This is the bound obtained from nonnegativity of the square norms of a+b and a-b, not a physical ledger or positivity supplier.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_oriented_count.lean:58

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

theorem APFPaper5.K1.overlap_between_bounds {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    -(∑ r, a r * a r + ∑ r, b r * b r) ≤ 2 * ∑ r, a r * b r ∧
      2 * ∑ r, a r * b r ≤ ∑ r, a r * a r + ∑ r, b r * b r := by sorry
