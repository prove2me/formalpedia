-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:18:27.422196+00:00
-- url     : https://prove2.me/theorems/860a82a6-62e5-440d-bc7d-5f364aed4f8d
-- title:
--   Original discounted dividend-regulated C2 Gaussian stopped cell: centered martingale gradient plus sigma-squared-over-two Hessian drift
-- statement:
--   For the original same-Omega spectrally negative Levy process with nu=0 and arbitrary nonnegative Gaussian sigma including zero, admissible dividend strategy D, C2 test w on the smooth positive reserve cap and original right-continuous bounded stopping time tau, define G_tau=e^{-q tau} w'(U_(tau-)) with inclusive ruin/horizon masks, and H_tau=e^{-q tau} w''(U_(tau-)) restricted to the smooth cap, also with exact ruin/horizon masks, with pre-dividend reserve the left limit of x+X.X-rightLimit D. If localized |G|<=K1 and |H|<=K2, then both actual source Gaussian Taylor terms are L1; E[G*(X.X_(tau+h)-X.X_tau-hc)]=0 and E[(1/2)H*(X.X_(tau+h)-X.X_tau-hc)^2]=(h*sigma^2/2)*E[H]. This packages the Gaussian part of the stopped discounted controlled C2 Ito cell on original X, P, right-continuous filtration. It is not the complete continuous-time Itô-Meyer identity, does not include source jumps or Stieltjes dividends, and does not assume any Brownian copy or sigma positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_gradient_gaussian_integrable_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_bounded_predividend_hessian_gaussian_half_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
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
      (∫ ω, G ω * Y ω ∂P) = 0 ∧
    Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
      (∫ ω, (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
        ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) := by
  sorry
