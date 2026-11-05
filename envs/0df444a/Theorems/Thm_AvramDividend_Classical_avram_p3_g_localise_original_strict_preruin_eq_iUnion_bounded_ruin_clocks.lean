-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_eq_iUnion_bounded_ruin_clocks
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_bounded_ruin_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:20:02.508213+00:00
-- url     : https://prove2.me/theorems/ffec2da9-e076-453e-8ccf-9ebe8b88b29b
-- title:
--   Original strict pre-ruin region is exactly the union of all finite bounded ruin-clock regions
-- statement:
--   The genuine original strict pre-ruin space-time region t<ruinTime X x D equals the union over finite deterministic horizons T of strict truncated clock regions t<(min(ruinTime,T)).toNNReal, including paths with infinite ruin time. For any strict pre-ruin t choose T=t+1; the reverse follows from the exact original endpoint theorem. This is the source-exact time-horizon exhaustion needed for finite-to-global verification without boundary occupation assumptions.
-- source:
--   Proved P3-G original strict clock endpoint b4677f24, actual ruinTime and NNReal positive horizon extension.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_bounded_ruin_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} :
      Set (ℝ≥0 × Ω)) =
      ⋃ T : ℝ≥0,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) <
            (((min (ruinTime X x D p.2) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by sorry
