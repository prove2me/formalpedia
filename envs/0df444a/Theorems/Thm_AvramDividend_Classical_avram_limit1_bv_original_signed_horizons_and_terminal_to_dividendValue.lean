-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
-- name    : AvramDividend.Classical.avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:42:28.476546+00:00
-- url     : https://prove2.me/theorems/b1112496-f39c-4c56-b640-af3d62f9444f
-- title:
--   Original BV post-payment terminal integrable, and signed finite-horizon HJB budgets imply full dividendValue
-- statement:
--   For a genuinely bounded-variation original spectrally negative Lévy dividend strategy satisfying the exact BV smoothness, gradient, cap, reserve and jump-dominance hypotheses, the P3 source post-right-payment strict-survival terminal is integrable at every positive real horizon by existing Proved a849869c. Existing Proved cf0ea4b5 establishes pathwise terminal nonnegativity. If the exact original expected ENNReal fibre-toReal signed stopped cash plus terminal is bounded above by a fixed real B for every positive closed real horizon, then the full original perpetual dividendValue is bounded by ENNReal.ofReal B. Use Proved f9800645 for the exact signed Stieltjes mean identity and Proved 96f0eeb7 for the natural-horizon supremum limit. Neither a P3 martingale identity nor hBudget is inferred: finite-HJB budget is explicit.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
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
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
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
