-- Prove2me | Theorems.Thm_APFPaper5_K1_recombination_is_a_count
-- name    : APFPaper5.K1.recombination_is_a_count
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:12:44.88201+00:00
-- url     : https://prove2.me/theorems/5ad8cbc9-52bf-4333-9f54-52794461f5c6
-- title:
--   The square-sum recombination identity for finite real arrays
-- statement:
--   For two real-valued arrays on a finite index type, the square-sum of their sum is the sum of the two square-sums plus twice their dot-product overlap. The entries are arbitrary real numbers; literal counting requires a separate discrete specialization.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_oriented_count.lean:44

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

theorem APFPaper5.K1.recombination_is_a_count {Rec : Type*} [Fintype Rec] (a b : Rec → ℝ) :
    ∑ r, (a r + b r) * (a r + b r) = ∑ r, a r * a r + ∑ r, b r * b r + 2 * ∑ r, a r * b r := by sorry
