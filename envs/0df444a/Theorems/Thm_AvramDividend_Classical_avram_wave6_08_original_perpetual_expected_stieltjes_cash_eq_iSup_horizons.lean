-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_expected_stieltjes_cash_eq_iSup_horizons
-- name    : AvramDividend.Classical.avram_wave6_08_original_perpetual_expected_stieltjes_cash_eq_iSup_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:38:10.394267+00:00
-- url     : https://prove2.me/theorems/9cdc28e3-b58b-4a54-997c-e6cf5a17d2fc
-- title:
--   Original expected full Stieltjes cash is the supremum of finite source horizons for all real discounts
-- statement:
--   The actual source expectation of the entire ruin-stopped complete dividend Stieltjes integral is exactly the supremum of expectations at deterministic horizons n+1. This equality holds for any q∈ℝ and any admissible source, with no Standing, variation, cap finiteness or integrability hypothesis; it is an extended-real monotone convergence identity and preserves the original zero and ruin endpoint conventions.
-- source:
--   Extracts the genuine monotone-convergence equality used internally in the Proved θ=1 source expected perpetual budget 5969ca80, from Proved original pathwise cofinal cash exhaustion 21a1dc8d and original measurable random upper-clock cash 6c6... . No expected-rate or Ito assumption. Directly reusable for the finite-to-infinite clock step in corrected UBV verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_perpetual_expected_stieltjes_cash_eq_iSup_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) =
      ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) := by sorry
