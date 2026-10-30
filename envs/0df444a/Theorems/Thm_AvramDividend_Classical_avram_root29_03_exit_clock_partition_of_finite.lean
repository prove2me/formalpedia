-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_clock_partition_of_finite
-- name    : AvramDividend.Classical.avram_root29_03_exit_clock_partition_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:09:13.356911+00:00
-- url     : https://prove2.me/theorems/0002b530-bafb-4c6a-9612-398605f177c5
-- title:
--   Strict two-sided exit order partitions precisely paths with at least one finite clock
-- statement:
--   For a genuine spectrally negative Lévy process and any strictly positive upper barrier a, along every path exactly one strict passage occurs first whenever at least one of its two actual exit clocks is finite. Neither clock finite means both are infinite; finite ties are excluded by an already Proved original-Lévy pathwise no-tie theorem. No Standing or discount hypothesis.
-- source:
--   Original-clock strict-order endpoint adapter for corrected two-sided exit equation (3.6). Depends only on Proved theorem chat03_official_strict_passage_no_finite_ties, not Open UBV/BV killed stochastic identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exit_clock_partition_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    (twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω ∨
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω) ↔
    (twoSidedExitUpTime X (a - x) ω < ⊤ ∨
      twoSidedExitDownTime X (-x) ω < ⊤) := by sorry
