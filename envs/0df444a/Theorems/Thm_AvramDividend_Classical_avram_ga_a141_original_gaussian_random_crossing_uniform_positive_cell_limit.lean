-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
-- name    : AvramDividend.Classical.avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:42:38.592133+00:00
-- url     : https://prove2.me/theorems/e1842b78-deec-4c32-814d-4e9f0f8b86a4
-- title:
--   One true randomly selected original Gaussian crossing cell has vanishing positive spatial residual sum from a uniform pathwise modulus
-- statement:
--   For the true physically clipped Gaussian grid, suppose every actual stop-straddling cell has a positive spatial error bounded by a single nonnegative m-dependent random pathwise modulus B_m, and B_m tends to zero almost surely. The original stop-straddling cell cardinality bound ga98 shows the entire positive crossing-cell error sum is bounded by B_m, with no factor of the mesh size and no predictability assumption on the crossing index. The stopped sum therefore converges to zero almost surely.
-- source:
--   Certified original uniformly stopped Gaussian crossing-cardinality ga98; source-specific pathwise compact modulus and HJB compensator ga106, ga112.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (f : ℕ → ℕ → Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hB : ∀ m ω, 0 ≤ B m ω)
    (hBound : ∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
      ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
      max (f m i ω) 0 ≤ B m ω)
    (hBae : ∀ᵐ ω ∂P, Tendsto (fun m => B m ω)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
          ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
        then max (f m i ω) 0 else 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
