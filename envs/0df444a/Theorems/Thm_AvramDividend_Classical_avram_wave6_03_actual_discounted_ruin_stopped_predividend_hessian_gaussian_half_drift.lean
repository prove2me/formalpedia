-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_predividend_hessian_gaussian_half_drift
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_hessian_gaussian_half_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:01:06.162124+00:00
-- url     : https://prove2.me/theorems/3625f420-68f5-49e7-8556-c0e6fd020135
-- title:
--   Discounted original controlled pre-dividend C2 Hessian has exact sigma-squared-over-two Gaussian Ito drift
-- statement:
--   For the original zero-jump spectrally negative Levy process and an admissible dividend strategy, set H exactly to the capped interior C2 Hessian w'' evaluated at the strict left-limit of the original controlled pre-dividend reserve x+X.X-rightLimit D, multiplied by exp(-q*t), inclusive ruin survival indicator and deterministic horizon T, then stopped at bounded right-continuous tau. Under explicit integrability of H and its multiplication by the true squared drift-centred source Gaussian increment over h, prove L1 for the half-quadratic Taylor term and the exact identity E[(1/2)H*(X.X_(tau+h)-X.X_tau-h*c)^2]=(h*sigma^2/2)*E[H]. This is the original-source discounted C2 Ito Gaussian second-order drift, including sigma=0, no standalone Brownian path; it is a localized stopped-cell identity rather than a full continuous-time Ito formula for general jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_hessian_gaussian_half_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHdef : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHI : Integrable H P)
    (hWeightedInt : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) := by
  sorry
