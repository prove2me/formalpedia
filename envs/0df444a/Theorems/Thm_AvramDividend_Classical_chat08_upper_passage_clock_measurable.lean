-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
-- name    : AvramDividend.Classical.chat08_upper_passage_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:02:11.351741+00:00
-- url     : https://prove2.me/theorems/7ded075d-5f3b-4922-8042-2b4d00edb46e
-- title:
--   Actual upper first-passage clock is measurable for every threshold
-- statement:
--   For every spectrally negative Lévy model in the standing formalisation and every real upper threshold, the named continuous strict first-upcrossing time is measurable as an ENNReal-valued random variable. Choose the explicit strictly positive grid spacing 1/(n+1), use its convergence to zero, apply the canonically verified sampled clock measurability and pointwise clock convergence, then use Mathlib's measurable-of-tendsto theorem. This unconditional result makes the passage-time component of first-record stopped-renewal weights measurable.
-- source:
--   Prove2Me chat03_uniform_grid_passage_clocks_measurable and chat03_official_upper_grid_clock_tendsto; Mathlib tendsto_one_div_add_atTop_nhds_zero_nat and ENNReal.measurable_of_tendsto.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_upper_passage_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (upper : ℝ) :
    Measurable (twoSidedExitUpTime X upper) := by sorry
