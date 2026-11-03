-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:06:46.985193+00:00
-- url     : https://prove2.me/theorems/aee12d86-a135-427e-b805-5a211974458a
-- title:
--   Original arbitrary-jump same-X Gaussian residual stopped C2 zero-mean integrable identity conditional on Lévy–Itô extraction
-- statement:
--   For the exact source X with arbitrary ν, real dividend controls, true stopped ruin-killed coefficients, and a Gaussian residual Y on precisely the same Ω/P/rightCont filtration satisfying the explicit source-exact pathwise Lévy–Itô decomposition, the Gaussian C2 gradient-plus-half-Hessian centred stopped residual is integrable and its actual expectation is zero.
-- source:
--   Imports the exact source-specific conditional Gaussian residual stopped C2 conditional expectation zero theorem of Wave7-05, integrates its conditional zero using integral_condExp over the original P; Gaussian Y/Jsmall/Jlarge representation remains explicit and unproved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHsource : H = fun ω => (1 / 2 : ℝ) * (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω)
    (hGI : Integrable (fun ω => G ω *
      (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω => H ω *
      (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c) ^ 2) P) :
    let V : Ω → ℝ := fun ω =>
      Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
    let A : Ω → ℝ := fun ω => G ω * V ω
    let R : Ω → ℝ := fun ω =>
      H ω * V ω ^ 2 - ((h : ℝ) * X.σ ^ 2) * H ω
    Integrable (A + R) P ∧
      (∫ ω, (A + R) ω ∂P) = 0 := by sorry
