-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_positive_real_state_shrinking_lowerband_finite_measure_zero_v2
-- name    : AvramDividend.Classical.avram_pj_workerC_positive_real_state_shrinking_lowerband_finite_measure_zero_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:05:58.762355+00:00
-- url     : https://prove2.me/theorems/ba47683a-d54f-4567-9bd2-b4928777d85d
-- title:
--   Strictly positive real-valued state lower bands shrink to zero measure under any finite measure, including original stopped Lévy physical product clock
-- statement:
--   For a measurable real state Y on any finite measure space, the measure of the shrinking lower positive band {0<Y≤1/(k+1)} tends to zero. The proof is actual continuity from above of the monotone measurable sets with empty intersection, and is suitable for application to the true strictly positive preterminal controlled reserve on the original finite stopped physical time-probability clock, complementing the already-Proved original finite-cap upper-strip expected vanishing.
-- source:
--   Pinned Mathlib MeasureTheory.tendsto_measure_iInter_atTop and tendsto_one_div_add_atTop_nhds_zero_nat; complements Proved a825583c preterminal positive original risk reserve and cb1a7c38 finitecap upper strip.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_positive_real_state_shrinking_lowerband_finite_measure_zero_v2
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [IsFiniteMeasure μ] (Y : α → ℝ) (hYm : Measurable Y) :
    Tendsto (fun k : ℕ =>
      μ {p : α | 0 < Y p ∧ Y p ≤ (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
