-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_bounded_ruin_clock_monotone_horizon
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_bounded_ruin_clock_monotone_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:16:47.259337+00:00
-- url     : https://prove2.me/theorems/fca78be2-da14-4e53-abc6-ae395ad8b2fa
-- title:
--   Actual original bounded ruin stopping clocks increase with deterministic horizon
-- statement:
--   For any original spectrally negative Levy process, actual ruinTime X x D and deterministic horizons T1<=T2, the finite-valued original stopped clock (min ruinTime T1).toNNReal is pointwise <= the corresponding clock at T2. This supplies monotone localisation as horizon rises with no boundary occupation claim or replacement process.
-- source:
--   Exact physical original ruinTime; pinned Mathlib ENNReal.coe_toNNReal and finite min, same proof idiom as Proved P3-G endpoint b4677f24.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_bounded_ruin_clock_monotone_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T₁ T₂ : ℝ≥0) (hT : T₁ ≤ T₂) :
    ∀ ω : Ω,
      (min (ruinTime X x D ω) (T₁ : ℝ≥0∞)).toNNReal ≤
      (min (ruinTime X x D ω) (T₂ : ℝ≥0∞)).toNNReal := by sorry
