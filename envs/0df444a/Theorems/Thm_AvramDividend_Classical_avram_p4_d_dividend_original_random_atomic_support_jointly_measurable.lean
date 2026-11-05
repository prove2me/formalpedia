-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:29:00.800197+00:00
-- url     : https://prove2.me/theorems/1bcb4f1e-be46-49a2-85fa-54bd05f4b5ad
-- title:
--   True original dividend Stieltjes positive singleton-mass atomic graph is jointly measurable
-- statement:
--   For the original adapted dividend-control Stieltjes measure, the set of sample paths and real payment times with a strictly positive singleton mass is jointly measurable. Convert the already-Proved s-finite random diagonal singleton indicator integral into the exact original singleton measure using the indicator-integral identity. This identifies an explicit canonical measurable carrier for the random rightpayment atoms without selecting a diffuse kernel yet.
-- source:
--   Accepted original random singleton-diagonal integration theorem 33b061f9 and Mathlib singleton indicator lintegral, on the literal dividendMeasure D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : Ω × ℝ | 0 < dividendMeasure D p.1 {p.2}} := by sorry
