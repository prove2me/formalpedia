-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
-- name    : AvramDividend.Classical.avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:23:38.880185+00:00
-- url     : https://prove2.me/theorems/76f6c03d-e5c2-4d07-b310-e1bcc04e27cf
-- title:
--   Original UBV zero-capital capped optimal value upper bound under canonical HJB
-- statement:
--   For the actual original spectrally negative Lévy X of unbounded variation, the canonical HJB maximum equality, zero-boundary nonnegativity, continuous candidate and interior C² regularity already imply the capped valueFunctionLe upper bound at initial reserve zero, without a generator-to-Itô stochastic step. For each genuine IsAdmissibleLe capped control, derive the original right-payment secant and gradient floor from the Proved HJB side-conditions lemma, apply the Proved Wave 6 Chat 10 zero-start full dividendValue bridge, and take the supremum using the Proved per-strategy-to-capped-value bound. All the original probability, filtration, dividend measure and t=0 payment conventions remain unchanged. This discharges exactly the x=0 branch of local_verification and does not claim the positive-capital case.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), zero-initial-capital capped-value verification. Formal corollary of Proved local_verification_stochastic_core_side_conditions (d307095e-a960-48c5-9b42-f2578aca7372), Proved local_verification_per_strategy_to_capped_value_bound (26cdad24-50a7-4f19-a856-90135afe6b6b), and the exact new zero-start full-value helper 449258df-da20-4bb1-85f1-1ff3b41d4e25.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    valueFunctionLe X q C 0 ≤ ENNReal.ofReal (w 0) := by sorry
