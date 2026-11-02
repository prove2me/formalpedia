-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_bounded_hessian_gaussian_compensator_zero
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_bounded_hessian_gaussian_compensator_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:02:39.176066+00:00
-- url     : https://prove2.me/theorems/fb2a7515-6ce4-4b8d-b6cd-7dcd2502df17
-- title:
--   Bounded actual discounted ruin-stopped Hessian has integrable centred Gaussian quadratic compensation
-- statement:
--   For the original spectrally negative Levy process with nu=0 and arbitrary sigma including zero, consider the strict pre-dividend capped C2 Hessian, with exponential discount, inclusive ruin survival and finite deterministic horizon. At any bounded right-continuous stopping time, assume only its stopped discounted weight H has a pointwise finite bound |H|<=K. Derive Integrable H and Integrable(H*(X_(tau+h)-X_tau-hc)^2) on the original probability space from stopped-history measurability, original Gaussian MemLp 2 and probability. Conclude the genuine stopped quadratic residual H*((Delta X-hc)^2-h sigma^2) is integrable and has exact mean zero. This is a localised finite-cell Ito Gaussian lemma for nu=0, not the arbitrary-nu continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_bounded_hessian_gaussian_compensator_zero
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
    (h : ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    Integrable (fun ω => H ω *
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
        (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  sorry
