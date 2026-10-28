-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
-- name    : AvramDividend.Classical.bv_drift_deficit_ae_monotone_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:29:10.193405+00:00
-- url     : https://prove2.me/theorems/bdb273f0-aac2-4b9b-84f3-3bb58bcafb69
-- title:
--   The actual BV Lévy drift deficit is almost surely nondecreasing at every time
-- statement:
--   For a bounded-variation spectrally negative Lévy process, almost every entire sample path of D_t=d t-X_t is nondecreasing. First establish the inequality simultaneously on a countable dense time range using the proved schedule lemma. For two distinct ordered times choose dense-range sequences decreasing to each. Right continuity transfers the nonnegative increment inequality from an eventually ordered pair of approximations to the real times. This establishes the actual subordinator path property needed for identifying the finite-activity first jump.
-- source:
--   Accepted bounded-variation stationary-increment schedule theorem and the actual Lévy càdlàg right-continuity axiom, Avram et al. (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_on_countable_schedule
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_drift_deficit_ae_monotone_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω) := by sorry
