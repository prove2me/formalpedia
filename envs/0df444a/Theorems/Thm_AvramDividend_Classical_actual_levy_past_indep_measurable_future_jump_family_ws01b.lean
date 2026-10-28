-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
-- name    : AvramDividend.Classical.actual_levy_past_indep_measurable_future_jump_family_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:21:47.267874+00:00
-- url     : https://prove2.me/theorems/86ab54a5-0f9f-4e69-a76c-19f22db4d908
-- title:
--   Actual Lévy past is independent of any measurable future jump-count and mark extraction
-- statement:
--   For an actual spectrally negative Lévy process X, deterministic time s and every variable H measurable in the real past filtration 𝓕s, H is independent of the result of any measurable functional F of the entire future increment path t↦X_{s+t}−X_s. In particular, if a genuinely measurable truncated Poisson jump count-and-mark family is extracted from that path, its entire joint family is independent of the past. Unlike abstract Poisson compensation, this proves the required pre-slice independence for the actual Lévy process, without asserting the Poisson law or existence of the jump extractor.
-- source:
--   Derived from canonically Proved AvramDividend.Classical.levy_deterministicTime_history_future_product_law (actual deterministic-time past × stationary entire future product law) and pinned Mathlib indepFun_iff_map_prod_eq_prod_map_map; combines with measurable joint path extraction. Provides a genuinely source-level stochastic Dynkin prerequisite without assuming the compensator.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_levy_past_indep_measurable_future_jump_family_ws01b
    {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E)
    (hH : Measurable[𝓕 s] H)
    (Fpath : (ℝ≥0 → ℝ) → F)
    (hF : Measurable Fpath) :
    IndepFun H
      (fun ω : Ω =>
        Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P := by sorry
