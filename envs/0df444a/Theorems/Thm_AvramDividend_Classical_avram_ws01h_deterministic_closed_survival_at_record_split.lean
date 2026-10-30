-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_deterministic_closed_survival_at_record_split
-- name    : AvramDividend.Classical.avram_ws01h_deterministic_closed_survival_at_record_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:13:31.63743+00:00
-- url     : https://prove2.me/theorems/f21cc0d0-1472-4a48-b3df-388ee6bf6e88
-- title:
--   Closed reserve survival across a finite record splits into the past and the exact shifted future
-- statement:
--   For any real-valued path indexed by nonnegative time, any finite record time τ no later than horizon t, and any initial reserve x, closed nonnegative-reserve survival on [0,t] is equivalent to survival on [0,τ] and survival of the exact shifted future reserve x+f(τ)+(f(τ+u)-f(τ)) on [0,t-τ]. This is the deterministic exact event splitting needed to instantiate the genuine killed first-record Qp renewal, without any probabilistic assumption or exit identity.
-- source:
--   Pathwise additive decomposition of the original Lévy trajectory at its actual capped first record; nonnegative real time tsub-add cancellation and strict clock past event proved in WS01H.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01h_deterministic_closed_survival_at_record_split
    (f : ℝ≥0 → ℝ) (x : ℝ) (τ t : ℝ≥0)
    (hτt : τ ≤ t) :
    (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + f s) ↔
      (∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + f s) ∧
      (∀ u : ℝ≥0, u ≤ t - τ →
        0 ≤ (x + f τ) + (f (τ + u) - f τ)) := by sorry
