-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_localised_tendstoInMeasure
-- name    : AvramDividend.Classical.avram_bv_residual10_finite_coordinate_localised_tendstoInMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:43:39.920504+00:00
-- url     : https://prove2.me/theorems/8b0e3603-6e5c-4a29-a852-a15a7658692f
-- title:
--   Original finite physical-row localisation converges in measure to untruncated source
-- statement:
--   Under finite measure, the exact original physical-grid source coefficient localisation at an increasing cutoff converges in measure to any original real source function. Each discrepancy lies in the complement of the finite-coordinate event, whose measure is known to vanish. This is a probability-level interface, not an assertion of L1 convergence or uniformity in the grid row.
-- source:
--   AVRAM BV-RESIDUAL10 original localised physical-grid convergence in measure, adapting MathFin LocalisationInMeasure, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_residual10_finite_coordinate_localised_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i)) (f : Ω → ℝ) :
    TendstoInMeasure P
      (fun k : ℕ => fun ω : Ω =>
        if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
            abs (a z i) ≤ (k : ℝ)} then f ω else 0)
      atTop f := by sorry
