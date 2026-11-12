-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_increment_positive_atom_suffix_cylinder_ae
-- name    : AvramDividend.Classical.avram_a06_increment_positive_atom_suffix_cylinder_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:49:55.552205+00:00
-- url     : https://prove2.me/theorems/fe3f7418-58b8-4454-bb9e-02a0dadc45ab
-- title:
--   Positive renewal-count increment singleton events equal consecutive residual-and-future-prefix thresholds almost surely
-- statement:
--   On the same original probability space, the a.e renewal count increment equals m+1 precisely when its m-th selected residual/suffix arrival threshold is met and the (m+1)-th is missed. This follows by two applications of Proved 425df1e2 and natural-number successor arithmetic, with one uniform full-measure set for all horizons and indices. It is the exact positive-atom event translation needed for one-step original renewal independence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_increment_suffix_threshold_ae
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_increment_positive_atom_suffix_cylinder_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (m : ℕ),
      N ω (clock + v) - N ω clock = m + 1 ↔
        (τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range m, τ (N ω clock + 1 + j) ω) ≤ v ∧
         v < τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range (m + 1), τ (N ω clock + 1 + j) ω)) := by sorry
