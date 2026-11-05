-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:08:48.947871+00:00
-- url     : https://prove2.me/theorems/6fb43911-625c-4c97-88a1-cc30693800bf
-- title:
--   Original admissible ruined-stop has predictable positive interior, zero and cap contact regimes
-- statement:
--   For the original admissible spectrally negative Levy reserve stopped at min(ruinTime,T), all three source pre-reserve regimes are predictable: positive strict cap interior, exact zero contact, and exact cap contact. The finite ruin stop is the true right-continuous filtration stopping time bounded by T. This avoids conflating inclusive stopped-time contact with the strict pre-ruin terminal payoff and does not impose vanishing BV boundary occupation.
-- source:
--   Composes proved original ruin clock 712c7638, inclusive survival strongly predictable 69806d16, public P3-G source predictable boundary partition fd3dcf89, and the real admissibility projection hD.1.1.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Z p = 0} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        ENNReal.ofReal (Z p) = C} := by sorry
