-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:58:10.254936+00:00
-- url     : https://prove2.me/theorems/ce07a61b-bc55-499c-a033-5d316fa72f40
-- title:
--   Original filtration predictable-weight centred future Levy increment exact L2 isometry
-- statement:
--   For actual X with integrable first and square moments, any source-past measurable W with finite square moment has exact E[(W(X(s+t)-X(s)-E[X(t)]))²] = E[W²] E[(X(t)-E[X(t)])²]. It uses the original source filtration sigma algebra, actual independent increments, and the proved stationary variance of centred future increments. It is a weighted entire-X-increment isometry, not a marked small-jump isometry.
-- source:
--   W7-06 original source predictable L2 variance control for stopped scalar weights.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (W : Ω → ℝ)
    (hWPast : Measurable[𝓕 s] W)
    (hWSq : Integrable (fun ω => (W ω)^2) P)
    (hXI : Integrable (X.X t) P)
    (hXSq : Integrable (fun ω => (X.X t ω)^2) P) :
    (∫ ω,
      (W ω * (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P)))^2 ∂P) =
      (∫ ω, (W ω)^2 ∂P) *
      (∫ ω, (X.X t ω - (∫ η, X.X t η ∂P))^2 ∂P) := by sorry
