-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
-- name    : AvramDividend.Classical.avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:57:47.535384+00:00
-- url     : https://prove2.me/theorems/bb203114-19aa-43ba-b113-879468bf81e8
-- title:
--   Raw filtration predictability of previous compensated Poisson-cell prefix
-- statement:
--   For the given filtration on the actual source space, a finite predictable coefficient H_i and a cell count K_i known by the next grid endpoint make the sum of all preceding compensated products measurable in the raw past at the current grid time. Requires only the explicit grid-filtration monotonicity and source adapted-count measurability, with no independent Poisson model, usual conditions, or moment assumptions.
-- source:
--   Finite measurable sum, Measurable.mono and monotone filtration interfaces at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

open MeasureTheory Set
open scoped NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hFilt : ∀ {i j : ℕ}, i ≤ j →
      𝓕 (grid i) ≤ 𝓕 (grid j))
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hKpast : ∀ i, Measurable[𝓕 (grid (i + 1))]
      (fun ω => (K i ω : ℝ)))
    (n : ℕ) :
    Measurable[𝓕 (grid n)] (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((K i ω : ℝ) - (r i : ℝ))) := by sorry
