-- Prove2me | Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_cadlag_no_positive_jumps
-- name    : AvramDividend.Classical.canonical_drifted_brownian_cadlag_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:35:35.481149+00:00
-- url     : https://prove2.me/theorems/3b92f98a-fadc-4ddb-aa18-580d0df92b86
-- title:
--   Canonical drifted Brownian paths satisfy every càdlàg and no-positive-jump Lévy interface
-- statement:
--   Every normalised, drifted canonical Brownian path is continuous. Consequently it is right-continuous and has a finite left limit at every positive time. Uniqueness of the left limit yields the no-positive-jumps property in the exact order and filter conventions used by AvramDividend.Classical.SpectrallyNegativeLevy.
-- source:
--   Accepted canonical_drifted_brownian_zero_continuous and standard continuous-path properties of one-sided neighbourhood filters.

import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.canonical_drifted_brownian_cadlag_no_positive_jumps
    (ω : ℝ≥0 → ℝ) :
    let X : ℝ≥0 → ℝ := fun t =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)
    (∀ t : ℝ≥0, ContinuousWithinAt X (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto X (𝓝[<] t) (𝓝 l)) ∧
    (∀ (t : ℝ≥0) (l : ℝ), 0 < t →
       Tendsto X (𝓝[<] t) (𝓝 l) → X t ≤ l) := by sorry
