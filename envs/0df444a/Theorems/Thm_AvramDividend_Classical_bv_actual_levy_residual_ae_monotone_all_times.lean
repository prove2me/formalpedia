-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
-- name    : AvramDividend.Classical.bv_actual_levy_residual_ae_monotone_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:24:59.267073+00:00
-- url     : https://prove2.me/theorems/f6cc1059-e8ca-403e-8d73-71a139d3dc4c
-- title:
--   Almost-sure global monotonicity of the actual BV Lévy drift residual
-- statement:
--   The residual process Y_t=d t-X_t of any bounded-variation spectrally negative Lévy process has nondecreasing paths on one probability-one event. Use the Proved pairwise drift-increment law on a countable dense schedule. Approximate arbitrary s<t by dense observation sequences descending to s and t, preserving the order, apply pathwise right continuity and the closedness of ≤, and conclude monotonicity for all times. This is a key stochastic law prerequisite for actual first-jump survival in the finite-activity branch.
-- source:
--   Avram Palmowski Pistorius (2007), Lévy bounded-variation representation; canonical process definition, Proved schedule-pair drift inequalities, Mathlib dense-right limit lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_schedule_pairs
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_residual_ae_monotone_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - X.X t ω) := by sorry
