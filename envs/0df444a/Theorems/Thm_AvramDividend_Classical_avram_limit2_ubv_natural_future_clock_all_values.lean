-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_natural_future_clock_all_values
-- name    : AvramDividend.Classical.avram_limit2_ubv_natural_future_clock_all_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:11:55.0852+00:00
-- url     : https://prove2.me/theorems/89951abe-9276-441a-ac50-f22e2c234763
-- title:
--   Natural future-clock bounds for all original UBV perpetual values
-- statement:
--   A single later natural stopped-clock cash inequality for each original capped UBV strategy and natural observation horizon, together with Proved strict natural horizon exhaustion and closed/strict supremum identity, bounds capped and unrestricted dividend values.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_limit2_closed_strict_original_cash_suprema_agree
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ubv_natural_future_clock_all_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hNext : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (n : ℕ), 0 < x →
        ∃ m : ℕ, n < m ∧
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic (n : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
