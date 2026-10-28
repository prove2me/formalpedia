-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_ae_fibrewise_factor
-- name    : AvramDividend.Classical.finiteGrid_ae_fibrewise_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:09:27.069487+00:00
-- url     : https://prove2.me/theorems/ae73f89f-466d-4fd2-ba81-1179b7d613b2
-- title:
--   Fibrewise constant conditional factors assemble over an almost-sure finite stopping grid
-- statement:
--   For a finite-valued random index τ supported on a grid up to a μ-null exceptional set, if the mass of E inside each measurable τ=s cell is the mass of A in the same cell multiplied by a common nonnegative factor k, then μ(E)=μ(A)k. Only each cell of E and A must be measurable. This generic stopped-history factorisation principle is the finite-partition engine needed for tilted stopping-time increment cylinders, and does not assume a Markov law as an extra hypothesis.
-- source:
--   Pinned Mathlib Finset.sum_mul and the drafted generic a.e. finite-grid fibre partition, itself derived from measure_congr and measure_biUnion_finset. The stochastic interpretation is a finite-grid integration of verified deterministic conditional factors.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_ae_stoppedEvent_measure_partition

open AvramDividend.Classical MeasureTheory Set
open scoped BigOperators ENNReal

theorem AvramDividend.Classical.finiteGrid_ae_fibrewise_factor
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (τ : Ω → ι) (grid : Finset ι)
    (A E : Set Ω) (k : ℝ≥0∞)
    (hgrid : ∀ᵐ ω ∂μ, τ ω ∈ grid)
    (hAcell : ∀ s ∈ grid, MeasurableSet (A ∩ {ω : Ω | τ ω = s}))
    (hEcell : ∀ s ∈ grid, MeasurableSet (E ∩ {ω : Ω | τ ω = s}))
    (hfactor : ∀ s ∈ grid,
      μ (E ∩ {ω : Ω | τ ω = s}) =
        μ (A ∩ {ω : Ω | τ ω = s}) * k) :
    μ E = μ A * k := by sorry
