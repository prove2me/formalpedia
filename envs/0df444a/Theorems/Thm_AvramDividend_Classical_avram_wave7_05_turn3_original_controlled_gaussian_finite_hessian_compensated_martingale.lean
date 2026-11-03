-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_gaussian_finite_hessian_compensated_martingale
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_gaussian_finite_hessian_compensated_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:35:51.704975+00:00
-- url     : https://prove2.me/theorems/9acf5254-14b1-4805-8623-a09aaf9a1181
-- title:
--   Finite original controlled C2 stopped Hessian Gaussian compensated quadratic has zero expectation
-- statement:
--   The original Gaussian (ν=0) source on the given Ω/P/X/filtration, actual x+X-rightLimit D reserve and true ruin time, has a finite family of bounded stopping times τ_i and source centred stopped increments Y_i. Under physically explicit L1 assumptions on each stopped discounted localised Hessian H_i and H_i Y_i², every martingale compensation H_i(Y_i²-h_iσ²) is L1 and mean zero; the actual finite source sum remains L1 with expectation exactly zero. This makes the Gaussian quadratic-variation compensation explicit and rigorous at finite C² mesh, with the exact original Hessian derivative and σ² factor, without a detached Brownian model. The mixed-ν stochastic Gaussian remainder awaits original Lévy-Itô decomposition.
-- source:
--   Finite-sum corollary, on the exact source and actual controlled reserve, of Proved Wave6 Hessian compensated quadratic stopped zero-mean theorem 9dfe146a-0980-4ce7-a1d5-549498ef3b84. It distinguishes each necessary integrability premise and the missing mesh-limit/mixed-jump bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_gaussian_finite_hessian_compensated_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B)
    (h : ι → ℝ≥0)
    (hHI : ∀ i ∈ S, Integrable (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) P)
    (hWeightedI : ∀ i ∈ S, Integrable (fun ω =>
      (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
          (h i : ℝ) * X.c) ^ 2) P) :
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    (∀ i ∈ S, Integrable (fun ω =>
      H i ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)) P) ∧
    Integrable (fun ω => ∑ i ∈ S,
      H i ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      H i ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by sorry
