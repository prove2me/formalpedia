-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
-- name    : AvramDividend.Classical.bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:23:11.214742+00:00
-- url     : https://prove2.me/theorems/4becefd5-3b97-4689-8d07-36a14ff99ed6
-- title:
--   Dyadic drift-deficit Cauchy event has stationary probability at every Lévy shift
-- statement:
--   For the actual spectrally negative Lévy process, the event that all dyadic drift-deficit increment slopes form a Cauchy sequence has the same probability when computed after any deterministic positive starting time as at time zero. The full shifted-future path equality in law and the measurable countable Cauchy cylinder transfer the entire joint event, not just individual one-dimensional marginals.
-- source:
--   Causal re-publication of failed job 9a2a4fe7-6d7b-4a94-8caa-d06f11b85c88. Its only publication error was import of bv_cauchyseq_real_event_measurable_ws01c, then Open, now independently Proved UUID 8589b747-d286-4519-a1f4-6cb73fdcf826. Exact statement/preamble and source work/avram_ws01c_actual_stationary_cauchy_solution_direct.lean unchanged.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_bv_cauchyseq_real_event_measurable_ws01c

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) :
    P {ω | CauchySeq (fun n : ℕ =>
      X.drift -
        (X.X (s + ((1 : ℝ≥0) / 2) ^ n) ω - X.X s ω) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ))} =
    P {ω | CauchySeq (fun n : ℕ =>
      X.drift -
        (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ))} := by sorry
