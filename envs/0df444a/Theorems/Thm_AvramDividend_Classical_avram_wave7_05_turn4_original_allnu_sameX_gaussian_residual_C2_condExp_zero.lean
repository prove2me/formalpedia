-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_condExp_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:55:14.490544+00:00
-- url     : https://prove2.me/theorems/d5c637bd-6ca4-400e-88eb-261d5cadec10
-- title:
--   Conditional same-original-source mixed-jump Gaussian stopped C2 local residual has zero conditional expectation
-- statement:
--   For arbitrary original source X with same Ω/P/filtration, assume a source-exact Gaussian residual Y with ν_Y=0, matching σ, and pathwise X_t=t*c_X+(Y_t-t*c_Y)+Jsmall_t+Jlarge_t. With actual ruin-killed discounted original reserve gradient G and half-Hessian H, genuine source stopping time, explicit stopped L1 localization of GΔY, H and HΔY², prove complete σ²/2 centred Gaussian C2 Taylor cell integrable and conditional expectation exactly zero in the original stopped sigma field. The same-path representation is an explicit remaining obligation.
-- source:
--   Proved arbitrary-ν source gradient/Hessian stopped predictability UUID 41b798ce-dc51-4499-a4c7-50320ffae570, Proved generic rightCont Gaussian stopped Taylor residual condExp zero UUID 32d08f0c-79ae-44fa-84f1-bf04ff639cf9, exact same-X pathwise decomposition hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_condExp_zero
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
      P[A + R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
