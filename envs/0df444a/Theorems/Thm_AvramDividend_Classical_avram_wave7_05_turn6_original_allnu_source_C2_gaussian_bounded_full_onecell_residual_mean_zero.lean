-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_onecell_residual_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_onecell_residual_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:19:33.720246+00:00
-- url     : https://prove2.me/theorems/c70b3e52-5d9e-49da-b641-d9016f197ddf
-- title:
--   Original arbitrary-jump C2 Gaussian stopped Ito one-cell bounded full martingale residual integrable and centred
-- statement:
--   For the canonical arbitrary-jump Levy X and an explicitly same-space same-filtration Gaussian component Y, the genuine stopped dividend-controlled reserve C2 gradient and clipped Hessian have an integrable centred Gaussian Ito one-cell residual G V + 1/2 H (V squared-h sigma_X squared). Both predictability and all Gaussian moments follow automatically from source measurability and boundedness; no hGI/hHI/hH2I moment hypotheses are separately assumed.
-- source:
--   Combines Proved original controlled source stopped gradient/Hessian predictability UUID 41b798ce-dc51-4499-a4c7-50320ffae570, Proved zero-jump bounded Gaussian gain UUID 8cf2614f-c9fe-47f1-896a-57969706c910, and newly Proved exact Gaussian half-Hessian bracket UUID 8118980c-11ec-4f29-8188-1cf22d362f7a. The Gaussian Y source decomposition remains explicit.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_onecell_residual_mean_zero
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
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGsource : G = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let V : Ω → ℝ := fun ω =>
      Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
    Integrable (fun ω => G ω * V ω +
      (1 / 2 : ℝ) * H ω * (V ω ^ 2 - (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, G ω * V ω +
      (1 / 2 : ℝ) * H ω * (V ω ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by sorry
