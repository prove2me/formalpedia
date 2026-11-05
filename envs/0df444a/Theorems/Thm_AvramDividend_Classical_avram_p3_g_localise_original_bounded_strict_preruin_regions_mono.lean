-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_bounded_strict_preruin_regions_mono
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_bounded_strict_preruin_regions_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:29:24.240148+00:00
-- url     : https://prove2.me/theorems/1b0c7f7e-3631-4304-b9ba-6bf521289764
-- title:
--   Actual original strict stopped pre-ruin masks increase with deterministic horizon
-- statement:
--   For the true original ruinTime, the space-time strict pre-ruin region stopped at deterministic T1 is included in that stopped at T2 whenever T1≤T2. This is an exact monotone family for finite-horizon-to-global limit passage. Follows by the Proved original strict endpoint equivalence; no dividend boundary occupation assumption.
-- source:
--   Proved P3-G original strict clock endpoint theorem b4677f24.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_bounded_strict_preruin_regions_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ T₁ T₂ : ℝ≥0, T₁ ≤ T₂ →
      ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) <
          (((min (ruinTime X x D p.2) (T₁ : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} :
        Set (ℝ≥0 × Ω)) ⊆
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) <
          (((min (ruinTime X x D p.2) (T₂ : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by sorry
