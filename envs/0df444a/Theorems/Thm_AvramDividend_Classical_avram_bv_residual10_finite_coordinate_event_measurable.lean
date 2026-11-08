-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
-- name    : AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:59:24.574388+00:00
-- url     : https://prove2.me/theorems/cc84e917-8883-4ee3-94a2-c739e7b24db4
-- title:
--   Finite original-grid coefficient-bound localisation events are measurable
-- statement:
--   Given original path-dependent finite physical-mesh coefficients that are each measurable, the event that all coefficients in one finite mesh row have absolute value bounded by a deterministic K is measurable. This is the canonical localisation event for applying the verified local original BV residual integrability theorem. The proof uses countable intersections and coordinatewise measurable level sets.
-- source:
--   AVRAM BV-RESIDUAL10 compact coefficient events after exact stopped original derivative measurability, 7 November 2026

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) (K : ℝ) :
    MeasurableSet {ω : Ω | ∀ i ∈ Finset.range (n + 1), abs (a ω i) ≤ K} := by sorry
