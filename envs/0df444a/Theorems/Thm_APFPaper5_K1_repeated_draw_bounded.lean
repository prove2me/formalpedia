-- Prove2me | Theorems.Thm_APFPaper5_K1_repeated_draw_bounded
-- name    : APFPaper5.K1.repeated_draw_bounded
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:13:16.595249+00:00
-- url     : https://prove2.me/theorems/ef1cf427-af84-4811-8fd1-dea63e1fedf7
-- title:
--   Repeated draw bounded
-- statement:
--   For nonnegative record weights, positive increment b, disjoint added record sets of bill b at each stage, and total stage-n bill at most C, n is at most C/b. This concerns the supplied weighted-set billing model.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_bill_is_a_sum.lean:63

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

theorem APFPaper5.K1.repeated_draw_bounded {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (b C : ℝ)
    (hw : ∀ r : Rec, 0 ≤ w r) (hbpos : 0 < b)
    (K N : ℕ → Finset Rec) (hstep : ∀ n : ℕ, K (n + 1) = K n ∪ N n)
    (hnew : ∀ n : ℕ, Disjoint (K n) (N n)) (hb : ∀ n : ℕ, ∑ r ∈ N n, w r = b) (n : ℕ)
    (hC : ∑ r ∈ K n, w r ≤ C) : (n : ℝ) ≤ C / b := by sorry
