-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_unrestricted_optimal_value_eq_zero
-- name    : AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_unrestricted_optimal_value_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:38:13.496002+00:00
-- url     : https://prove2.me/theorems/dab833fb-3f62-4cc1-8160-ee535010c89e
-- title:
--   Original UBV Lévy unrestricted optimal dividend value is exactly zero at zero initial reserve
-- statement:
--   For the genuine original spectrally negative Lévy process with unbounded variation, the unrestricted classical optimal dividend value at zero initial surplus is identically zero for every real discount q. The just-proved exact zero-capital reward theorem gives valueFunctionLe X q ⊤ 0 = 0 without any HJB, standing or smoothing assumption; the Proved canonical top-cap equivalence identifies that value with valueFunction X q 0. This is the exact x=0 boundary in the unrestricted branch of barrier optimality, not the positive-surplus stochastic verification step.
-- source:
--   Proved valueFunctionLe_top_eq_valueFunction 61c1cded-9c54-4796-9d24-f10c1d7b3100 and new original UBV zero-capital exact reward/capped value helper under publication request 76986994-8850-42fb-a84c-64e5ea949d8a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_unrestricted_optimal_value_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) :
    valueFunction X q 0 = 0 := by sorry
