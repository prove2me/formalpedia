-- Prove2me | Theorems.Thm_APFPaper5_K1_bill_of_repeated_draw
-- name    : APFPaper5.K1.bill_of_repeated_draw
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:10:45.283204+00:00
-- url     : https://prove2.me/theorems/8c737681-b163-4fa4-a336-aee549e371d1
-- title:
--   Bill of repeated draw
-- statement:
--   Suppose each record set K(n+1) is K(n) union a disjoint new set N(n), and every N(n) has the same weighted bill b. Then the bill of K(n) is the initial bill plus n b. The set-growth and constant-increment hypotheses are explicit.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_bill_is_a_sum.lean:52

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

theorem APFPaper5.K1.bill_of_repeated_draw {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (b : ℝ)
    (K N : ℕ → Finset Rec) (hstep : ∀ n : ℕ, K (n + 1) = K n ∪ N n)
    (hnew : ∀ n : ℕ, Disjoint (K n) (N n)) (hb : ∀ n : ℕ, ∑ r ∈ N n, w r = b) (n : ℕ) :
    ∑ r ∈ K n, w r = ∑ r ∈ K 0, w r + n * b := by sorry
