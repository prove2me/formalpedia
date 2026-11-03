-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:46:06.200028+00:00
-- url     : https://prove2.me/theorems/0f006e3c-0422-4c38-b92a-ce77657548f3
-- title:
--   One genuine stopped controlled C2 Gaussian Ito martingale residual has L1 and exactly zero mean
-- statement:
--   On the actual original Gaussian-source Ω/P/X/𝓕, at one genuine bounded stopping time, the discounted, ruin-stopped gradient G of the left-limit controlled reserve x+X-rightLimit D and the clipped C² Hessian H satisfy the centred Gaussian one-cell Itô martingale identity: GY+1/2H(Y²-hσ²) is integrable with expectation zero, Y=X_(τ+h)-X_τ-hc. Requires explicit bounded gradient localisation and Hessian/Hessian-square integrability; ν=0. This is the mathematically distinct single-cell martingale unit for the finite-family C² extension and the source Itô limit.
-- source:
--   Combines proved actual-source controlled derivative stopped Gaussian L2 zero mean b6e0c60e-f61a-42e4-b513-288adb62b442 and proved actual stopped C² Hessian compensated quadratic mean zero 9dfe146a-0980-4ce7-a1d5-549498ef3b84. The finite sum will use this as genuine reusable child, within solver line budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
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
    (hWeightedI : Integrable (fun ω =>
      (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2) P) :
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
    Integrable (fun ω => G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 - (h : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 - (h : ℝ) * X.σ ^ 2)) ∂P) = 0 := by sorry
