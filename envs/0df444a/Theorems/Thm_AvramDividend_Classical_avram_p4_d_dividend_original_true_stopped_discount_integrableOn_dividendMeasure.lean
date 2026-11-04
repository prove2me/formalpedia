-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:27:23.514623+00:00
-- url     : https://prove2.me/theorems/03a6d70a-ebcc-4095-aa17-425fd179e5da
-- title:
--   Source-exact stopped real dividend discount is integrable against original Stieltjes measure
-- statement:
--   For any original admissible dividend strategy, sample path, extended true ruin clock and finite observation horizon, the real source discount weight exp(-q s) is integrable with respect to the original Stieltjes dividend measure restricted exactly to actual payment times through the closed horizon when q≥0. The full restricted measure is finite by the original dividendMeasure total-mass right-limit theorem; the discount is continuous and bounded by one on these nonnegative payment times. Includes singular continuous dividend mass, time-zero and horizon right atoms.
-- source:
--   Mathlib IntegrableOn.of_bound; original paymentTimes support and dividendMeasure_Icc_zero_eq_rightLimit

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun u : ℝ => Real.exp (-(q * u)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
