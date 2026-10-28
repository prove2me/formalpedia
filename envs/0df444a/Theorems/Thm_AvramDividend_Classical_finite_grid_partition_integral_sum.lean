-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_partition_integral_sum
-- name    : AvramDividend.Classical.finite_grid_partition_integral_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:33:54.96504+00:00
-- url     : https://prove2.me/theorems/578ffb8d-b03e-43ff-9921-abb2bcf39c7c
-- title:
--   Expectation at finite-grid random time splits over measurable fibres
-- statement:
--   If a random time takes values in a finite set with measurable fibres, the expectation of an integrable random-time observable equals the finite sum of expectations of its deterministic-time observables restricted to each fibre. This is a reusable finite-grid stopping-time step in the Lévy verification calculations.
-- source:
--   Finite measurable partition plus integrability of restricted observables and Bochner integral_finset_sum.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.finite_grid_partition_integral_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P) :
    ∫ ω, f (τ ω) ω ∂P =
      ∑ s ∈ grid, ∫ ω,
        ({ω : Ω | τ ω = s}).indicator (f s) ω ∂P := by sorry
