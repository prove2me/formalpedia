-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
-- name    : AvramDividend.Classical.avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:37:46.394688+00:00
-- url     : https://prove2.me/theorems/bc08088f-e831-4ce8-b12a-050035ea3c2c
-- title:
--   Exact original postpayment reserve jointly measurable in physical time and sample path
-- statement:
--   For every original spectrally negative Levy source and an original adapted dividend strategy, the actual postpayment reserve random field x+X(t)-rightLimit D(t) is jointly measurable in nonnegative physical time and sample outcome. This follows from the source and dividend adaptedness, their right-continuous paths, and an already Proved joint evaluation lemma. It supplies the missing Tonelli hypothesis for the original prescribed fixed-level finite-cap Gaussian occupation theorem B100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by sorry
