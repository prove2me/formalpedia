-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_adapted_of_clock_measurable
-- name    : AvramDividend.Classical.avram_bv_tail13_single_step_adapted_of_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:25:24.113478+00:00
-- url     : https://prove2.me/theorems/935d4fec-6669-4327-9cb3-5236a3fd1675
-- title:
--   Adapted original single-clock dividend step from payment measurability
-- statement:
--   For any filtration and deterministic clock, an amount measurable at that clock gives an adapted dividend path that is zero through the clock and equal to the amount strictly thereafter. This discharges the adaptedness component of the exact source IsDividendStrategy for a one-payment reserve reset.
-- source:
--   Source-adaptedness uses 𝓕.mono to lift measurability at s to every later time, and is constant zero earlier. Same pattern proved in original avram_e0_initial_step_adapted_solution for clock zero.

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_single_step_adapted_of_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (K : Ω → ℝ) (hK : Measurable[𝓕 s] K) :
    Adapted 𝓕 (fun t ω => if t ≤ s then (0 : ℝ) else K ω) := by sorry
