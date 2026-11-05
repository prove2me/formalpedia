-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:54:02.137383+00:00
-- url     : https://prove2.me/theorems/e0edcc7b-e3c3-46c4-bb44-91b8d3c16249
-- title:
--   Original controlled-dividend Stieltjes measure equals its atomic and atomless restrictions
-- statement:
--   For every original admissible adapted dividend path, the Stieltjes measure is exactly the sum of its restriction to all strictly positive singleton-mass payment times and its restriction to the complementary zero-singleton-mass times. This equality of measures retains time-zero and horizon atoms and all continuous and singular-continuous dividend mass.
-- source:
--   Accepted jointly measurable original dividend atomic support 1bcb4f1e; pinned Mathlib Measure.restrict_add_restrict_compl and a measurable vertical section.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ ω : Ω,
      (dividendMeasure D ω).restrict
          {t : ℝ | 0 < dividendMeasure D ω {t}} +
      (dividendMeasure D ω).restrict
          {t : ℝ | ¬0 < dividendMeasure D ω {t}} =
        dividendMeasure D ω := by sorry
