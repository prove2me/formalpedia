-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23b_finite_step_indicator_integral
-- name    : AvramDividend.Classical.avram_bvb23b_finite_step_indicator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:16:09.238189+00:00
-- url     : https://prove2.me/theorems/8d6460bb-c08c-4bbd-9f3c-04d4c23ec356
-- title:
--   Finite Riemann-step integral equals weighted cell masses
-- statement:
--   For a finite measure and arbitrary measurable time cells, the integral of a finite simple step weight equals its finite sum of cell values times cell measures, even if the sets overlap. This is the exact Lebesgue step-function identity required to turn the original BV finite-cap uniform physical grid into a time integral before dominated convergence. No stochastic source substitution.
-- source:
--   Pinned Mathlib integral_finset_sum, integral_indicator, integral_const; intended source-exact original finite-cap compensator grid 7ccc2a1a

import Mathlib
open MeasureTheory Set
noncomputable section
open scoped BigOperators

theorem AvramDividend.Classical.avram_bvb23b_finite_step_indicator_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hs : ∀ i, MeasurableSet (s i))
    (w : ℕ → ℝ) (n : ℕ) :
    (∫ x, ∑ i ∈ Finset.range n, (s i).indicator (fun _ => w i) x ∂μ) =
      ∑ i ∈ Finset.range n, w i * (μ (s i)).toReal := by sorry
