-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_past_event_future_negative_Borel_void_exact_exponential_20261117
-- name    : AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_void_exact_exponential_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:34:55.304194+00:00
-- url     : https://prove2.me/theorems/d91653dc-5fba-44bf-90bc-06cf2b596364
-- title:
--   Original future negative Borel physical void conditional factor has exact Lévy exponential intensity
-- statement:
--   For any event in the original filtration at s, the probability of that past event and no physical negative jump with mark in B during (s,s+T] equals the original past-event probability multiplied by exp(-T nu(B)). This gives exact source conditional marked-void probabilities, a finite-dimensional ingredient for the missing physical Mecke and independent mark-stream results.
-- source:
--   Proved original past/future void factor theorem wave7_06 and original shifted negative Borel void exact exponential theorem a25.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original future negative-mark void probability factors from each past event with its exact exponent. -/

theorem AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_void_exact_exponential_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (A : Set Ω) (hApast : MeasurableSet[𝓕 s] A)
    (hAraw : MeasurableSet A) :
    (P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B) = 0})).toReal =
      (P A).toReal * Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by sorry
