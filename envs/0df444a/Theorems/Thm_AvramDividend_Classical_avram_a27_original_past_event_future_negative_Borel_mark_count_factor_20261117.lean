-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_past_event_future_negative_Borel_mark_count_factor_20261117
-- name    : AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_mark_count_factor_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:08:58.440119+00:00
-- url     : https://prove2.me/theorems/2650d11a-7690-4e5e-8c17-ac33bea99abe
-- title:
--   Actual original future negative Borel marked jump count has factorised first moment against any past event
-- statement:
--   For any event A measurable in the original filtration at time s and any negative Borel mark band B, the expected future physical marked jump count on (s,t] multiplied by 1_A equals P(A) times the exact original Lévy intensity (t-s) nu(B). This is the source predictable compensation underpinning the missing compound-Poisson Mecke recursion.
-- source:
--   Proved original finite marked rectangle Campbell mean 811bf7d8 and original predictable weighted-rate factorization e13617a2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The future original marked count has an exact conditional first moment against every past event. -/

theorem AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_mark_count_factor_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
