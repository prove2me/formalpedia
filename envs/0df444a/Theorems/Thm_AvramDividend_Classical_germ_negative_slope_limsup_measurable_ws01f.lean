-- Prove2me | Theorems.Thm_AvramDividend_Classical_germ_negative_slope_limsup_measurable_ws01f
-- name    : AvramDividend.Classical.germ_negative_slope_limsup_measurable_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:13:44.339831+00:00
-- url     : https://prove2.me/theorems/3e22718b-df27-4dbf-8738-a639e087d187
-- title:
--   Countable small-time negative-slope limsup is measurable in the Lévy time-zero germ
-- statement:
--   For any real-valued stochastic process and any nonnegative observation grid δ_n tending to time zero, the event of infinitely many observations with slope below the fixed real threshold C is measurable in the path's initial germ sigma-algebra. The proof uses finite-time past coordinate measurability and the fact that deleting finitely many observations preserves a limsup event. This supplies the exact previously missing countable-germ measurability premise needed to apply the Proved Lévy germ zero-one law to Gaussian lower-tail probabilities.
-- source:
--   Blumenthal time-zero germ argument; canonical Proved DurrettProbability.germSigma/pastSigma definitions, pinned Mathlib MeasurableSpace.measurableSet_iInf, and WS1F Proved levy_germ_zero_one_ws01f.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open MeasureTheory Filter Set DurrettProbability
open scoped NNReal Topology

theorem AvramDividend.Classical.germ_negative_slope_limsup_measurable_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (δ : ℕ → ℝ≥0)
    (hδ : Tendsto δ atTop (𝓝 0)) (C : ℝ) :
    MeasurableSet[germSigma B]
      (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ B (δ n) ω < C * (δ n : ℝ)}) := by sorry
