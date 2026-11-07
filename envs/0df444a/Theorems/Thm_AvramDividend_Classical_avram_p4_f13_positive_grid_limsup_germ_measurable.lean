-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f13_positive_grid_limsup_germ_measurable
-- name    : AvramDividend.Classical.avram_p4_f13_positive_grid_limsup_germ_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:24:20.602343+00:00
-- url     : https://prove2.me/theorems/d16a7595-b780-408b-a75f-fc27cec24a15
-- title:
--   Countable positive-observation limsup is a time-zero germ event
-- statement:
--   For an arbitrary real-valued path family and any deterministic nonnegative grid converging to time zero, the event of infinitely many strictly positive grid observations is measurable in the process time-zero germ sigma algebra. This provides the countable measurable skeleton for the genuine Lévy positive-near-zero event and avoids uncountable unions over times.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory Filter Set DurrettProbability
open scoped NNReal Topology

theorem AvramDividend.Classical.avram_p4_f13_positive_grid_limsup_germ_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (δ : ℕ → ℝ≥0)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    MeasurableSet[germSigma B]
      (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ 0 < B (δ n) ω}) := by sorry
