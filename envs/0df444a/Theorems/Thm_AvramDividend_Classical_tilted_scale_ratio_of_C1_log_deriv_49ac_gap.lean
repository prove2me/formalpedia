-- Prove2me | Theorems.Thm_AvramDividend_Classical_tilted_scale_ratio_of_C1_log_deriv_49ac_gap
-- name    : AvramDividend.Classical.tilted_scale_ratio_of_C1_log_deriv_49ac_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:35:15.902989+00:00
-- url     : https://prove2.me/theorems/18db0847-fb54-4d2f-90c0-e0861aa7d461
-- title:
--   Tilted scale ratio from C1 log-derivative shape
-- statement:
--   Let V be strictly positive on (0,inf), C1 there, with logarithmic derivative tail continuous on (0,inf), i.e. deriv V x = V x * tail x at every positive x. Then V satisfies the exponential ratio identity V b = V a * exp(integral of tail over [a,b]) for all 0 < a <= b. This is the exact deterministic Fundamental-Theorem-of-Calculus step that turns the tilted C1 log-derivative shape into the q=0 excursion ratio premise needed by the Esscher transfer lemmas for the unbounded-variation integrated scale representation.
-- source:
--   Deterministic FTC/log-derivative step supporting AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation (49acdc06): Chan-Kyprianou-Savov equations (5)-(6) identify the excursion tail as the logarithmic derivative; the ratio identity is its integrated form. Uses only Mathlib interval-integral calculus, no excursion measure.

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.tilted_scale_ratio_of_C1_log_deriv_49ac_gap
    (V tail : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hder : ∀ x : ℝ, 0 < x → deriv V x = V x * tail x)
    (hcont : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, tail t) := by sorry
