-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:35:50.051228+00:00
-- url     : https://prove2.me/theorems/0e79ea15-1c86-4b75-8812-773c919be8c2
-- title:
--   Original all-jump source stopped C2 Hessian Gaussian compensated quadratic conditional expectation zero
-- statement:
--   For a canonical original spectrally negative Levy risk process X, actual dividend controlled C2 left-limit Hessian stopped at a bounded original-filtration stopping time, and explicitly assumed same-space Gaussian residual decomposition, the source Hessian-weighted centred Gaussian square minus h times X.sigma squared times the Hessian has conditional expectation zero given the stopping history. Integrability of H and its Gaussian squared product are explicit hypotheses.
-- source:
--   Transfers remotely Proved stopped Gaussian predictable compensated quadratic conditional-mean-zero law from a zero-jump Y to the actual original X-minus-jumps continuous residual, obtaining predictability of the actual C2 Hessian from a remotely Proved original-source theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_stopped_quadratic_condExp_zero
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
    (hHI : Integrable H P)
    (hProdI : Integrable (fun ω =>
      H ω * (Y.X (τ ω + h) ω - Y.X (τ ω) ω -
        (h : ℝ) * Y.c) ^ 2) P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    P[(fun ω =>
      H ω * (M (τ ω + h) ω - M (τ ω) ω) ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
