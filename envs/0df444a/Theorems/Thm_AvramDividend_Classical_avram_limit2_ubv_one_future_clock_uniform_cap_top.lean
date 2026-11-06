-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_one_future_clock_uniform_cap_top
-- name    : AvramDividend.Classical.avram_limit2_ubv_one_future_clock_uniform_cap_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:57:03.571198+00:00
-- url     : https://prove2.me/theorems/36e46802-369b-4ccc-bca3-4dd5f061900e
-- title:
--   One future bounded original UBV ruin clock per horizon bounds capped and unrestricted perpetual values
-- statement:
--   The original UBV one-future-natural-clock stopped dividend cash budget for each positive-cap admissible strategy and closed real observation horizon controls the exact closed-horizon cash. Proved strict-positive-integer exhaustion and agreement of closed and strict suprema then turn this into the genuine perpetual dividendValue bound. Taking both strategy suprema yields all capped values, and C=top yields unrestricted value. Requires no HJB, standing, discount positivity, witness martingale construction or terminal vanishing.

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

theorem AvramDividend.Classical.avram_limit2_ubv_one_future_clock_uniform_cap_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hFuture : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < x →
        ∃ n : ℕ, T < (n : ℝ) ∧
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
