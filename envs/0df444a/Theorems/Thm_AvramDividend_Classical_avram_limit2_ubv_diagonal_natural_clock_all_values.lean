-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_diagonal_natural_clock_all_values
-- name    : AvramDividend.Classical.avram_limit2_ubv_diagonal_natural_clock_all_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:20:41.418587+00:00
-- url     : https://prove2.me/theorems/2b04b481-ff33-466e-9ab5-2cfc11792188
-- title:
--   Diagonal natural ruin-stop original UBV cash budgets imply perpetual capped and unrestricted values
-- statement:
--   Uniform original UBV diagonal stopped cash bounds at each natural horizon imply the true perpetual dividend-value and capped/unrestricted value function upper bounds. The source is lifted to one future clock by monotonicity of nonnegative integrals, preserving horizon atoms and ruin stopping, then exact natural-horizon suprema and the top-cap identity apply.

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

theorem AvramDividend.Classical.avram_limit2_ubv_diagonal_natural_clock_all_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hDiag : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (m : ℕ), 0 < x →
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic (m : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
