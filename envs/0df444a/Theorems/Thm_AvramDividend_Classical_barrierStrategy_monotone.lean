-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
-- name    : AvramDividend.Classical.barrierStrategy_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T07:50:39.855678+00:00
-- url     : https://prove2.me/theorems/d571f0aa-b205-43eb-b82e-d1d9cb252fa7
-- title:
--   Barrier dividend strategy is pathwise monotone for every spectrally negative Levy process
-- statement:
--   For every spectrally negative Levy process with the stated path regularity, cumulative barrier dividends at initial reserve c and barrier c are nondecreasing in time. The regularity assumptions imply compact-interval path boundedness, discharging the bounded-supremum assumption of the previously published monotonicity theorem.
-- source:
--   Unconditional bridge to the dividend-strategy monotonicity obligation of AvramDividend.Classical.valueFunctionLe_above_cap. Imports the conditionally bounded monotonicity and compact-path boundedness helpers, whose remote proof verdicts must be canonical Proved before compiling this bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_bddAbove

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_monotone {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) := by
  sorry
