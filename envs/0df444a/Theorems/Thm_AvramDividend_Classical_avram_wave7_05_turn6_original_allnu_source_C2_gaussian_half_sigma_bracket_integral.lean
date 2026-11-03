-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:55:44.888605+00:00
-- url     : https://prove2.me/theorems/8118980c-11ec-4f29-8188-1cf22d362f7a
-- title:
--   Original-source controlled C2 stopped Gaussian Hessian half-sigma-squared bracket integral
-- statement:
--   On the original Levy X, its right-continuous filtration and the actual dividend-controlled prepayment reserve, the Gaussian component Y has a stopped Hessian-weighted quadratic increment. The weighted square is integrable and its expected half contribution is exactly half h times X.sigma squared times the Hessian expectation, assuming bounded Hessian and a same-source Gaussian decomposition.
-- source:
--   Proved original-source predictable clipped Hessian UUID 41b798ce-dc51-4499-a4c7-50320ffae570 plus Proved bounded stopped conditional Gaussian covariance UUID a52309b8-5be6-406f-befd-5921676b3177. Coefficient half from ring identity; no independent Brownian sample space.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral
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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHsource : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (BH : ℝ) (hBH : 0 ≤ BH)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let V : Ω → ℝ := fun ω =>
      Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
    Integrable (fun ω => (1 / 2 : ℝ) *
      (((1 : ℝ) * V ω) * (H ω * V ω))) P ∧
    (∫ ω, (1 / 2 : ℝ) *
      (((1 : ℝ) * V ω) * (H ω * V ω)) ∂P) =
      (((h : ℝ) * X.σ ^ 2) / 2) * (∫ ω, H ω ∂P) := by sorry
