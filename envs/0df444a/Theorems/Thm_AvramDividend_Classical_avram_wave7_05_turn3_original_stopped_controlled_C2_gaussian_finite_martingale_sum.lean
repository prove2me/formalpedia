-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_stopped_controlled_C2_gaussian_finite_martingale_sum
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_stopped_controlled_C2_gaussian_finite_martingale_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:13:10.117595+00:00
-- url     : https://prove2.me/theorems/7a080cc7-05ae-4cb8-835a-728ac49c9c13
-- title:
--   Finite genuine ruin-stopped controlled C2 Gaussian martingale residual has L1 and zero mean
-- statement:
--   On the exact canonical Ω/P/X/filtration, for the real controlled predividend reserve x+X.X-rightLimit D, discount and true ruin indicator, a finite collection of genuine source stopped horizons h_i has the complete Gaussian C² centred source martingale residual ∑[G(X_{τ+h_i}-X_τ-h_ic)+1/2 H((X_{τ+h_i}-X_τ-h_ic)^2-h_iσ²)]. Under ν=0 and explicitly bounded derivative plus integrable localised Hessian and weighted Hessian-square hypotheses, the full finite residual is integrable and has expectation zero. This combines the true derivative martingale cancellation and the true compensated Hessian Gaussian quadratic variation with coefficient σ²/2. It remains finite and ν=0, awaiting original mixed-jump Lévy-Itô and mesh convergence.
-- source:
--   Source physical stopped derivative gain b6e0c60e-f61a-42e4-b513-288adb62b442, compensated actual C² stopped Hessian source theorem 9dfe146a-0980-4ce7-a1d5-549498ef3b84; finite expectation linearity. No independent Brownian construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_stopped_controlled_C2_gaussian_finite_martingale_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (S : Finset ι) (h : ι → ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K)
    (hHI : Integrable (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) P)
    (hWeightedI : ∀ i ∈ S, Integrable (fun ω =>
      (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω *
        (X.X (τ ω + h i) ω - X.X (τ ω) ω -
          (h i : ℝ) * X.c) ^ 2) P) :
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
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
    Integrable (fun ω => Finset.sum S (fun i =>
      G ω * Y i ω +
        (1 / 2 : ℝ) * (H ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)))) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G ω * Y i ω +
        (1 / 2 : ℝ) * (H ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) =
      0 := by sorry
