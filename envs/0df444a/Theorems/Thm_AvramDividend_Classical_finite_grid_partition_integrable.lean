-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_partition_integrable
-- name    : AvramDividend.Classical.finite_grid_partition_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:22:59.202809+00:00
-- url     : https://prove2.me/theorems/554478df-4062-4bcc-b62e-e87285a23386
-- title:
--   Integrability of a measurable finite-grid random-time partition
-- statement:
--   An observable sampled at a finite-valued random time is integrable when each fixed-time observable is integrable and each time fibre is measurable. Decompose the sampled function as a finite sum of fibre indicators.
-- source:
--   Mathlib MeasureTheory.integrable_finset_sum and Integrable.indicator; reusable bounded Lévy stopping-time helper.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.finite_grid_partition_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P) :
    Integrable (fun ω => f (τ ω) ω) P := by sorry
