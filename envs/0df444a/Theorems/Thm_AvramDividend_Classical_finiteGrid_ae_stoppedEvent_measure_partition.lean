-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_ae_stoppedEvent_measure_partition
-- name    : AvramDividend.Classical.finiteGrid_ae_stoppedEvent_measure_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:51:47.528314+00:00
-- url     : https://prove2.me/theorems/2a6998ef-2f85-4009-9fe3-f73c711af375
-- title:
--   Almost-sure finite fibres partition arbitrary event mass without global event measurability
-- statement:
--   Let τ take values in a finite grid outside a μ-null exceptional set, and suppose the intersections E∩{τ=s} are measurable for each grid point. Then μ(E) is the sum of the measures of those disjoint fibres. No measurability of τ or of E outside the finite grid is required. This is a reusable almost-sure partition tool for tilted finite stopping-time events, including stopped future-increment events whose global measurability can be delicate.
-- source:
--   Pinned Mathlib MeasureTheory.measure_congr, measure_biUnion_finset and Set.disjoint_left. This improves the accepted everywhere-grid finiteGrid_stoppedEvent_measure_partition (5edb1a0c-5d8b-4d2e-bab5-01b6b88e542e) by allowing null exceptional grid failures and assuming only measurable event fibres.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

open AvramDividend.Classical MeasureTheory Set
open scoped BigOperators ENNReal

theorem AvramDividend.Classical.finiteGrid_ae_stoppedEvent_measure_partition
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (τ : Ω → ι) (grid : Finset ι) (E : Set Ω)
    (hgrid : ∀ᵐ ω ∂μ, τ ω ∈ grid)
    (hcell : ∀ s ∈ grid, MeasurableSet (E ∩ {ω : Ω | τ ω = s})) :
    μ E = ∑ s ∈ grid, μ (E ∩ {ω : Ω | τ ω = s}) := by sorry
