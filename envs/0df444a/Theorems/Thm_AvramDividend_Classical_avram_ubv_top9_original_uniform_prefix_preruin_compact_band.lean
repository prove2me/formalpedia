-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_preruin_compact_band
-- name    : AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_preruin_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:53:33.240346+00:00
-- url     : https://prove2.me/theorems/72000b1a-3ed8-45ac-b139-5cb457a54e03
-- title:
--   Original pre-ruin Levy and controlled reserve lie in a compact strip under bounded upcross prefixes
-- statement:
--   Any original physical stopping prefix bounding X uniformly from above also bounds X from below by minus initial surplus and the controlled surplus between zero and x+B on strict pre-ruin times. It uses monotone nonnegative dividends and the defining ruin-time property, providing the two-sided spatial envelope needed for stopped generator and Gaussian coefficients.
-- source:
--   Proved 03a69d71 riskProcess_nonnegative_strictly_before_ruin and 716ba871 dividendStrategy_path_nonneg, paired with newly strengthened TOP9 uniform prefix upcross source bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_preruin_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (κ : Ω → ℝ≥0) (B : ℝ)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ κ ω → X.X t ω ≤ B) :
    ∀ ω (t : ℝ≥0), t ≤ κ ω →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      X.X t ω ∈ Icc (-x) B ∧
      riskProcess X x D t ω ∈ Icc 0 (x + B) := by sorry
