-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_renewal_finite_geometric_budget_identity
-- name    : AvramDividend.Classical.stopped_renewal_finite_geometric_budget_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:53:46.79667+00:00
-- url     : https://prove2.me/theorems/7f2418f2-fe98-4682-87a2-165f744ca635
-- title:
--   Exact finite geometric first-record renewal budget
-- statement:
--   The total finite geometric survival budget through n record intervals is exactly (1-p^n)/(1-p) when p is below one. The algebraic identity is valid without sign restrictions and is a reusable base for translating strong-Markov first-record weights to stopped-reflection dividend value bounds.
-- source:
--   Avram Dividend stopped first-record renewal reward, finite geometric sum step.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.stopped_renewal_finite_geometric_budget_identity (p : ℝ) (n : ℕ) :
  (1 - p) * (∑ i ∈ Finset.range n, p ^ i) = 1 - p ^ n := by sorry
