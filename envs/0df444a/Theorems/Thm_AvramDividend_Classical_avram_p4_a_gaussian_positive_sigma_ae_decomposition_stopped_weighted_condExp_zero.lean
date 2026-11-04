-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_ae_decomposition_stopped_weighted_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_decomposition_stopped_weighted_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:58:37.054016+00:00
-- url     : https://prove2.me/theorems/27a62af1-cb49-41e3-928a-341099910620
-- title:
--   Original positive Gaussian stopped residual conditional mean zero from almost-sure same-source Lévy–Itô extraction
-- statement:
--   Unlike a strict all-sample-path extraction, only one probability-one set on which the exact same-source Lévy-Ito decomposition holds simultaneously for every t is assumed. That is enough to transport L1 and the stopped-history conditional mean-zero identity from the original zero-jump Gaussian component Y to the actual X residual, even though τ depends on omega. This more faithful a.s. interface avoids strengthening the Lévy decomposition across exceptional sample paths. It still does not construct the decomposition or the continuous stochastic integral.
-- source:
--   Accepted source c9825ed7 stopped Gaussian conditional mean and pinned MeasureTheory.condExp_congr_ae; compares to accepted ab3e94b1 all-path hypothesis. Avram et al Eq (5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_decomposition_stopped_weighted_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
