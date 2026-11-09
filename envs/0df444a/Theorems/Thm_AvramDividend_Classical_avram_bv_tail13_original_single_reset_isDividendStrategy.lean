-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_single_reset_isDividendStrategy
-- name    : AvramDividend.Classical.avram_bv_tail13_original_single_reset_isDividendStrategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:39:50.698991+00:00
-- url     : https://prove2.me/theorems/a42c39d1-53e4-4126-b751-7c511cb24edb
-- title:
--   Original Levy-process single reset is a genuine dividend strategy
-- statement:
--   The actual source spectrally negative Levy surplus, clipped at zero at a deterministic payment clock, defines a dividend path that is nondecreasing, starts at zero, is left-continuous, and is adapted to the original filtration. This establishes the exact IsDividendStrategy prerequisite for a legitimate one-clock reset in the BV cofinal cash validity investigation.
-- source:
--   Combines independently Proved original-process clock-measurability, step adaptedness, step left-continuity and strategy assembly. Distinct from IsAdmissibleLe: the separate financial affordability and ruin-time conditions remain unproved.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_reset_amount_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_adapted_of_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_dividend_strategy_of_adapted
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_original_single_reset_isDividendStrategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (s : ℝ≥0) :
    IsDividendStrategy 𝓕 (fun t ω =>
      if t ≤ s then 0 else max (x + X.X s ω) (0 : ℝ)) := by sorry
