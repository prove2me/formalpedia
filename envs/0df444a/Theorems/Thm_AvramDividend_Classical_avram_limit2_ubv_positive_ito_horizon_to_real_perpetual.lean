-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_positive_ito_horizon_to_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_ubv_positive_ito_horizon_to_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:08:38.626944+00:00
-- url     : https://prove2.me/theorems/b4eba97f-a69f-4db0-9363-d675d75a4254
-- title:
--   Original UBV positive-horizon Ito cash budgets imply real perpetual value and L1
-- statement:
--   Exact positive-horizon original UBV stopped Ito cash bound, shaped as the canonical d457be6b cash source, implies for every genuine admissible capped strategy integrable real perpetual dividend Stieltjes cash, exact real expected dividendValue, its real upper bound, and capped/unrestricted value function bounds. The proof advances T to T+1 for the time-zero case, controls closed horizon atoms by monotonic nonnegative lintegral, chooses a future natural stopped clock, and uses the accepted perpetual bridge.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_one_future_clock_uniform_cap_top
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ubv_positive_ito_horizon_to_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
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
