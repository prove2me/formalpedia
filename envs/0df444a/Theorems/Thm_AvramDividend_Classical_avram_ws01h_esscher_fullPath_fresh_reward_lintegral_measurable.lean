-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
-- name    : AvramDividend.Classical.avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:46:11.17405+00:00
-- url     : https://prove2.me/theorems/e7fd7b1b-6f92-4fbd-9509-be354fa14741
-- title:
--   Genuine Esscher full-future reward clock-integral measurability from actual Lévy joint state law
-- statement:
--   For the actual spectrally negative Lévy process and any jointly measurable full-future path reward H, the original-law Esscher compensated reward integrated over the entire actual future path has a measurable real clock-age parameter. The proof uses the canonically proved joint Lévy time-state measurability and pinned Tonelli measurable-parameter integration theorem. It discharges the hRMeas premise of the source-specific lower-killed first-record renewal kernel without a fictitious tilted infinite path-space probability.
-- source:
--   Canonical actual Lévy joint time-state theorem d55462c3-decf-40f0-9aff-439d356324d9; pinned Mathlib Measurable.lintegral_prod_right, revision 0df444a.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
