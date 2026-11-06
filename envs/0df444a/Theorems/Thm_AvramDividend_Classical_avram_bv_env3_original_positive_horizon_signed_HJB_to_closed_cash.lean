-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
-- name    : AvramDividend.Classical.avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:54:53.344601+00:00
-- url     : https://prove2.me/theorems/473fd841-def3-42a5-b954-0122e80df665
-- title:
--   Original positive-horizon BV signed HJB expected budget yields exact closed Stieltjes ENNReal cash
-- statement:
--   Independent exact bridge: a signed finite-horizon expected budget with the actual post-payment terminal proves the closed-horizon original dividend value inequality. Post-payment terminal integrability follows from BV source theorem a849869c and pointwise nonnegativity from 28b04520; the full real-to-ENNReal conversion follows from cb8b9f9d. Only the genuine signed HJB budget remains as hypothesis, matching precisely the signed P3-2 theorem 9cd69d89; no stochastic calculus is postulated in the proof.
-- source:
--   Accepted Proved a849869c-3e67-4861-9bcf-5727858c3bc0; 28b04520-30d3-4e2d-9a85-5d54ae7dc1b0; cb8b9f9d-b41f-44c0-9a7e-66af192c9877. Signed budget formal statement matches pending 9cd69d89.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hSigned :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
      else 0) ∂P) ≤ w x) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
