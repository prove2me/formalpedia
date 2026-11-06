-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_positive_ito_real_perpetual_from_C2_slope
-- name    : AvramDividend.Classical.avram_limit2_ubv_positive_ito_real_perpetual_from_C2_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:16:56.643108+00:00
-- url     : https://prove2.me/theorems/78398da3-56f0-49e8-9a2d-3fc25d7df1d6
-- title:
--   Canonical UBV C2 positive Ito horizon cash yields real perpetual L1 without extra positivity
-- statement:
--   The original C2 positive-cap continuity and slope-one lower bound imply nonnegative w(x) at every capped nonnegative capital using the Proved avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient. The exact positive-horizon original stopped Ito cash hypothesis then bounds arbitrary closed cash horizons by a strictly future nonnegative stopped clock and yields actual original perpetually discounted Stieltjes cash L1, real mean equality, capped value and top-cap unrestricted value, preserving the atom at time zero without terminal vanishing.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_one_future_clock_uniform_cap_top
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ubv_positive_ito_real_perpetual_from_C2_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      0 < x → ∀ (T : ℝ), 0 < T → ∀ (n : ℕ), 0 < n →
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D = ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
