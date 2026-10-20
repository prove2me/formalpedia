-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_ceiling_bracket
-- name    : AvramDividend.Classical.chat03_grid_ceiling_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:40:53.142363+00:00
-- url     : https://prove2.me/theorems/40fa8e8f-1e70-4131-bd54-c47ddb5823da
-- title:
--   First mesh point above a nonnegative time lies within one strictly positive step
-- statement:
--   For every nonnegative real time t and positive grid spacing h, define k=Nat.ceil(t/h). Then t≤k h<t+h. This is the exact deterministic ceiling construction of a grid sample from above, with a strict upper error bound h. In particular it applies to the dyadic mesh h=2^(-n), providing a clock point arbitrarily close after any finite strict-exit time, once h tends to zero. There is no probabilistic assumption, local Lean compilation or artificial continuity requirement.
-- source:
--   Exact pinned Mathlib Nat.le_ceil and Nat.ceil_lt_add_one (at revision 0df444a360eaa60ab8c11dca51a86af692955474). Motivation: Avram Dividend Chat03 strict dyadic exit convergence, 19 October 2026.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

theorem AvramDividend.Classical.chat03_grid_ceiling_bracket
    (t h : ℝ) (ht : 0 ≤ t) (hh : 0 < h) :
    t ≤ (Nat.ceil (t / h) : ℝ) * h ∧
      (Nat.ceil (t / h) : ℝ) * h < t + h := by sorry
