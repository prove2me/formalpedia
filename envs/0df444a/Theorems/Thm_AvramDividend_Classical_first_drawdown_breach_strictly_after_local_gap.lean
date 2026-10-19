-- Prove2me | Theorems.Thm_AvramDividend_Classical_first_drawdown_breach_strictly_after_local_gap
-- name    : AvramDividend.Classical.first_drawdown_breach_strictly_after_local_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:40:38.079396+00:00
-- url     : https://prove2.me/theorems/a408367b-ad0b-4a25-902b-41a456671ceb
-- title:
--   A positive no-breach time gap gives strict separation between contact and first ruin
-- statement:
--   For a time-indexed real path f, suppose no breach of the strict barrier a occurs at any time earlier than u+δ, with δ strictly positive. Then the extended nonnegative real first strict breach time inf{t | f(t)>a} is strictly later than u. This is the order-theoretic final step needed at a finite record contact: after establishing from right continuity and zero drawdown that a positive post-contact no-ruin interval exists, this lemma converts the gap into strict T_h < τ_a. It makes no continuity or stochastic hypothesis itself.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 1 strict reflected barrier ruin definition and record renewal; elementary order property of iInf and positive time offset.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.first_drawdown_breach_strictly_after_local_gap
    (f : ℝ≥0 → ℝ) (a : ℝ)
    (u δ : ℝ≥0) (hδ : 0 < δ)
    (hNoBreach : ∀ t : ℝ≥0, t < u + δ → f t ≤ a) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < f t), (t : ℝ≥0∞)) := by sorry
