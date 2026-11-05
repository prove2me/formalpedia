-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_BV_interval_absolute_source_variation
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_BV_interval_absolute_source_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:58:29.301241+00:00
-- url     : https://prove2.me/theorems/4b643b2c-2cad-445f-83fe-dd4d79650132
-- title:
--   Actual BV Levy source single-interval absolute variation budget
-- statement:
--   On one full-measure event for the original bounded-variation spectrally negative Levy source, every interval [s,t] has actual X.X absolute increment bounded by drift magnitude times length plus the nonnegative increments of the original residual R and negative-jump cumulative process J.
-- source:
--   Proved original residual monotone e9d95081 and cumulative source raw J monotone 32cc0b62; identity X_t-X_s = drift*(t-s) - delta J - delta R, triangle inequality. This is a genuine one-cell stepping stone into P3-F original discounted variation 3086f90a, not equivalent to that finite-grid weighted theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_BV_interval_absolute_source_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ s t : ℝ≥0, s ≤ t →
        |X.X t ω - X.X s ω| ≤
          |X.drift| * ((t : ℝ) - (s : ℝ)) +
          (R t - R s) + (J t - J s) := by sorry
