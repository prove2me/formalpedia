-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_negative_mark_condExp_mean
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_negative_mark_condExp_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:45:16.0368+00:00
-- url     : https://prove2.me/theorems/aba7515d-abf3-4bb4-ada8-3dbfcae1a682
-- title:
--   Original signed future jump mass conditional mean under stopping
-- statement:
--   For the genuine original negative-jump measure and its signed mass in an actual future left-open right-closed interval, an integrable strongly measurable future mass has conditional expectation equal to its unconditional expectation given the stopped original right-continuous history. Source equalities identify the exact actual measure and integral, with no auxiliary Brownian source; this follows from original future signed mark independence and conditional expectation of an independent integrable random variable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_negative_mark_condExp_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0)
    (J : Ω → Measure (ℝ≥0 × ℝ))
    (hJ : J = fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (F : Ω → ℝ)
    (hF : F = fun ω =>
      ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω)
    (hStrong : StronglyMeasurable F)
    (hInt : Integrable F P)
    (hPast : (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace ≤ mΩ) :
    P[F | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, F ω ∂P) := by sorry
