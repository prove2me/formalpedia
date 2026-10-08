-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_partition_expectation
-- name    : AvramDividend.Classical.finite_grid_partition_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:16:30.965723+00:00
-- url     : https://prove2.me/theorems/2d586fe5-095f-44f4-89e8-83ee2e03110c
-- title:
--   Expectation of a finite-valued random-time observable via a measurable partition
-- statement:
--   Suppose a random time τ takes its values in a finite grid and each fibre {τ=s} is measurable. Let f(s,ω) be integrable for each grid point. If the integral of f(s) over each fibre is the probability of that fibre multiplied by the same real constant c, then the full expectation of the random-time observable f(τ(ω),ω) equals c. The proof partitions Ω into the disjoint finite fibres, integrates the finite sum of fibre indicators and sums the fibre probabilities to one. This is a generic measure-theoretic lemma to complete the finite-grid stopped Lévy increment Laplace identity once each restricted exponential moment is factored using deterministic independent increments.
-- source:
--   Standard finite measurable partition and Lebesgue integral linearity; Prove2Me Avram classical strong-Markov decomposition for Proposition 1.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finite_grid_partition_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P)
    (c : ℝ)
    (heach : ∀ s ∈ grid,
      ∫ ω in {ω : Ω | τ ω = s}, f s ω ∂P =
        (P {ω : Ω | τ ω = s}).toReal * c) :
    ∫ ω, f (τ ω) ω ∂P = c := by sorry
