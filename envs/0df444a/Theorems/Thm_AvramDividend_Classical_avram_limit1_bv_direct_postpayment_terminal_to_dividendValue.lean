-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_direct_postpayment_terminal_to_dividendValue
-- name    : AvramDividend.Classical.avram_limit1_bv_direct_postpayment_terminal_to_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:55:13.976608+00:00
-- url     : https://prove2.me/theorems/c1aebbc7-18ba-411a-b300-ffc76c085e03
-- title:
--   Direct BV postpayment gradient positivity and terminal L1 transfer stopped HJB budgets to true perpetual dividendValue
-- statement:
--   For a genuinely bounded-variation original spectrally negative Lévy dividend strategy with original C1 smoothness, cap, reserve and gradient hypotheses, the exact strict-survival post-rightpayment terminal is integrable by existing Proved a849869c and pointwise nonnegative from the direct Proved BV postpayment gradient theorem 28b04520. No separate jump-dominance hypothesis is required. If the genuine original signed finite positive closed-horizon cash plus terminal expectation is at most B for all T>0, the Proved exact signed-ENNReal fibre expectation identity f9800645 and the Proved original natural horizon bridge 96f0eeb7 bound the full original dividendValue by ENNReal.ofReal B. The finite stopped HJB budget remains an explicit hypothesis, so no P3 martingale or stochastic identity is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_bv_direct_postpayment_terminal_to_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (B : ℝ)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ B) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0)) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal B := by sorry
