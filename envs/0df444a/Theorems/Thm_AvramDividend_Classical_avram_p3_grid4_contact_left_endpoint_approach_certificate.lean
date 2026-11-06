-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
-- name    : AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_approach_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:55:25.45521+00:00
-- url     : https://prove2.me/theorems/58277187-7bac-42dd-97f5-92f4347c95eb
-- title:
--   Genuine physical contact-grid left endpoints increase strictly below and converge to positive stop
-- statement:
--   For positive actual stopped clock tau and positive physical horizon T, the exact truncated NNReal physical left endpoints tau-T/(n+1), coerced to real, are monotone, tend to tau and remain strictly below tau at every finite n. This packages all endpoint hypotheses required to instantiate the proved original dividendMeasure closed-crossing cash limit f01118ec and ruined contact zero limit 5a7cefb8, preserving the T-payment atom and strict pre-ruin mask.

import Mathlib.Order.Monotone.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_real_tendsto
open Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_approach_certificate
    (τ T : ℝ≥0) (hτ : 0 < τ) (hT : 0 < T) :
    let a : ℕ → ℝ := fun n =>
      ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)
    Monotone a ∧ Tendsto a atTop (𝓝 (τ : ℝ)) ∧
      (∀ n, a n < (τ : ℝ)) := by sorry
