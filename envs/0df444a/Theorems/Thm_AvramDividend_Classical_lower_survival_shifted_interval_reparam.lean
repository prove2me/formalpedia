-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_shifted_interval_reparam
-- name    : AvramDividend.Classical.lower_survival_shifted_interval_reparam
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:00:06.654241+00:00
-- url     : https://prove2.me/theorems/3001de90-3bac-4b52-b8b6-ea3d0fc035d1
-- title:
--   Reparameterise one-sided survival over a shifted closed time interval
-- statement:
--   For an arbitrary real path and nonnegative times s,u, shifted lower-barrier survival over the absolute interval [s,s+u] is equivalent to survival over elapsed times v in [0,u] for the increment f(s+v)-f(s). The equivalence uses exact closed endpoints and requires no stochastic assumptions.
-- source:
--   Direct time subtraction and addition in NNReal; serves to combine the already-Proved pathwise lower-survival split with the full-path Levy Markov-Tonelli theorem.

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

open scoped NNReal

theorem AvramDividend.Classical.lower_survival_shifted_interval_reparam
    (f : ℝ≥0 → ℝ) (x : ℝ) (s u : ℝ≥0) :
    (∀ v : ℝ≥0, s ≤ v → v ≤ s + u →
      0 ≤ (x + f s) + (f v - f s)) ↔
    (∀ v : ℝ≥0, v ≤ u →
      0 ≤ (x + f s) + (f (s + v) - f s)) := by sorry
