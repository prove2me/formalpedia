-- Prove2me | Theorems.Thm_AvramDividend_Classical_tilted_scale_integrated_rep_of_C1_esscher_49ac_gap
-- name    : AvramDividend.Classical.tilted_scale_integrated_rep_of_C1_esscher_49ac_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:42:26.086627+00:00
-- url     : https://prove2.me/theorems/3d8e16bd-f23a-487b-bf09-56aed289e1e1
-- title:
--   Integrated scale representation from C1 log-derivative and Esscher relation
-- statement:
--   Let W = exp(phi .) * V on (0,inf) with V strictly positive and C1 there, deriv V = V * tail at every positive point, and tail continuous on (0,inf). Then W satisfies the integrated representation W b = W a * exp(integral of (phi + tail) over [a,b]) for all 0 < a <= b. This composes the proved tilted C1 log-derivative ratio step with the Esscher transfer step, yielding exactly the branch-5 analytic conclusion needed by the unbounded Esscher excursion representation, with no excursion measure assumed.
-- source:
--   Deterministic closure supporting AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation (49acdc06): Chan-Kyprianou-Savov equation (4) Esscher relation plus equations (5)-(6) log-derivative shape, integrated by the Fundamental Theorem of Calculus. Composes the already-proved tilted_scale_ratio_of_C1_log_deriv_49ac_gap and integrated_scale_rep_of_tilted_excursion_49ac_bridge patterns; pure Mathlib interval-integral calculus.

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.tilted_scale_integrated_rep_of_C1_esscher_49ac_gap
    (W V tail : ℝ → ℝ) (φ : ℝ)
    (hEsscher : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hder : ∀ x : ℝ, 0 < x → deriv V x = V x * tail x)
    (hcont : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + tail t) := by sorry
