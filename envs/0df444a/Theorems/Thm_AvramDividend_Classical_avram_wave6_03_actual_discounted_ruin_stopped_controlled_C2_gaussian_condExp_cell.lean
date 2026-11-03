-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_condExp_cell
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_condExp_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:39:18.087659+00:00
-- url     : https://prove2.me/theorems/3ac270eb-ec5a-4cb7-b4d8-fb7ea5134bea
-- title:
--   Conditional original controlled Gaussian C2 stopped Ito cell with zero stochastic gradient and exact half-variance Hessian drift
-- statement:
--   On the original zero-jump Lévy probability space and original right-continuous stopped history, prove the conditional Gaussian C2 Taylor cell for the actual dividend-regulated reserve. The bounded, discounted, horizon-truncated, inclusive-ruin gradient G and smooth-cap Hessian H are evaluated at the strict pre-dividend left limit of x+X.X-rightLimit D. Both G times the actual drift-centred source increment Y and half H times Y squared are integrable. Their conditional expectations given the physical stopped-history sigma algebra are respectively zero and (h*sigma^2/2)H, including sigma zero. This strengthens earlier expectation identities and uses the genuine stopped conditional first/second moments, actual predictable coefficients and Mathlib conditional product pull-out, with no independent Brownian copy. It does not claim the full pathwise continuous-time Ito-Meyer formula or arbitrary-jump continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_condExp_cell
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
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hGbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₁)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₂) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => G ω * Y ω) P ∧
    Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (P[(fun ω => G ω * Y ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    (P[(fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2 / 2) * H ω)) := by
  sorry
