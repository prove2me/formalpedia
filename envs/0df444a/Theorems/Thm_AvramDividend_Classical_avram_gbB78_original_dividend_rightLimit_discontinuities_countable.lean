-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB78_original_dividend_rightLimit_discontinuities_countable
-- name    : AvramDividend.Classical.avram_gbB78_original_dividend_rightLimit_discontinuities_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:13:43.36799+00:00
-- url     : https://prove2.me/theorems/bf524c10-dc22-4871-8940-8860d86ba308
-- title:
--   Original admissible dividend right-limit path has only countably many discontinuities
-- statement:
--   For the unchanged original dividend strategy D and right-continuous filtration, the path t to rightLimit D t omega is nondecreasing. Its discontinuity set is therefore countable for every omega, hence negligible under Lebesgue time. This is a physical-source prerequisite for almost-everywhere left-grid postpayment coefficient convergence in B61.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB78_original_dividend_rightLimit_discontinuities_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => rightLimit D s ω) t} := by sorry
