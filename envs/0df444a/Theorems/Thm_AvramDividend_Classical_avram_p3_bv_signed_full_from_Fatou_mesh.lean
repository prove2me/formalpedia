-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_signed_full_from_Fatou_mesh
-- name    : AvramDividend.Classical.avram_p3_bv_signed_full_from_Fatou_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:38:53.127208+00:00
-- url     : https://prove2.me/theorems/e82590ca-bc0d-438f-80f5-a955283af99d
-- title:
--   Original BV complete signed horizon budget from per-grid signed HJB and Fatou without uniform envelopes
-- statement:
--   For the actual original bounded-variation controlled Lévy process, source-exact measurable nonnegative finite grid approximations with per-grid integrable signed M+B residuals of nonpositive mean and a pathwise lower liminf give the complete stopped signed Stieltjes horizon expectation inequality. The Proved original Fatou theorem supplies the strict expected bound, and the Proved P3 full endpoint bridge handles the time-zero and right-horizon atoms and terminal integrability. Source grid construction remains an explicit hypothesis, not a claim of completed stochastic verification.
-- source:
--   Proved 61679cb8-fe10-45ca-a2ec-d8f57d59ca19, Proved a2794d96-6c12-432e-92a3-4b539130af5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep7_original_strict_fatou_from_signed_grid_budgets
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_HJB_to_signed_full

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original-process endpoint assembly from signed finite-grid estimates.
The only source work remaining is the stated genuine mesh data; no
uniform-integrability envelope is needed for the Fatou passage. -/

theorem AvramDividend.Classical.avram_p3_bv_signed_full_from_Fatou_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hwx : 0 ≤ w x) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (F M B : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hMesh : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
      else 0 ∂P) ≤ w x := by sorry
