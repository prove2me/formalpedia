-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_finite_infinite_horizon_exhaustion
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_finite_infinite_horizon_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:17:54.311596+00:00
-- url     : https://prove2.me/theorems/ad0cf142-dfa4-4853-b37d-6d85756683de
-- title:
--   Original ruin clock saturates on finite ruin and follows horizon on infinite ruin
-- statement:
--   For the actual original ruinTime of X.X-rightLimit D, if ruin occurs at finite ENNReal time then every horizon beyond the real-valued ruin time makes the truncated NNReal clock equal that ruin time. If original ruin never occurs (ruinTime=top), then every truncated clock equals its deterministic horizon. This is exact pathwise finite/infinite ruin localisation, useful for terminal passage, without assuming BV boundary occupation zero.
-- source:
--   Actual original ruinTime; pinned Mathlib ENNReal.coe_toNNReal, min_eq_left and top_min coercion; original P3-G clock endpoint conventions.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_finite_infinite_horizon_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω : Ω,
      (ruinTime X x D ω ≠ ⊤ →
        ∀ T : ℝ≥0, (ruinTime X x D ω).toNNReal ≤ T →
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal =
            (ruinTime X x D ω).toNNReal) ∧
      (ruinTime X x D ω = ⊤ →
        ∀ T : ℝ≥0,
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal = T) := by sorry
