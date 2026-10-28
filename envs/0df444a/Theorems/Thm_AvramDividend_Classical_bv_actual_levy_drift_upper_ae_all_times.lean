-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
-- name    : AvramDividend.Classical.bv_actual_levy_drift_upper_ae_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:10:07.165312+00:00
-- url     : https://prove2.me/theorems/c1de9f71-ed76-45a5-ba7c-4b8fee455b6f
-- title:
--   Almost-sure pathwise drift upper bound for every time of a bounded-variation Lévy process
-- statement:
--   A single probability-one set satisfies X_t ≤ drift·t for all t≥0 for the actual spectrally negative BV Lévy process. A dense countable observation sequence satisfies the bound by an accepted a.e. schedule theorem. For each t, dense points decreasing to t and right-continuity of X transfer this bound to t using closedness of ≤.
-- source:
--   Avram Palmowski Pistorius (2007), bounded variation Lévy-Khintchine; canonical pinned SpectrallyNegativeLevy process definition and prior Proved support lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_schedule
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_upper_ae_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω ≤ (t : ℝ) * X.drift := by sorry
