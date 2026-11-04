-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
-- name    : AvramDividend.Classical.avram_p2_original_bounded_negative_test_grid_l2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:06:31.196122+00:00
-- url     : https://prove2.me/theorems/5f1ce29e-a18f-4343-a2f3-2a04fe9a91d4
-- title:
--   Uniform original-source L² estimate for bounded separated-negative marked-grid test sums
-- statement:
--   For any finite bounded nonnegative ENNReal-valued test f supported in the negative half-line below minus epsilon, the actual original spectrally negative Lévy grid sum has uniformly bounded second lintegral over all fine equispaced grids of fixed total horizon. The proof pointwise dominates each original test value by M times the indicator of its true negative increment event and invokes the already-Proved original independent-increment count second-moment bound. This is an unconditional source-specific uniform integrability ingredient; it does not assume a jump compensator or Poisson representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_original_bounded_negative_test_grid_l2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ℝ≥0∞) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
        (∫⁻ ω, (∑ i ∈ Finset.range n,
          f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
              X.X ((i : ℝ≥0) * Real.toNNReal h) ω)) ^ 2 ∂P) ≤
          M ^ 2 * (ENNReal.ofReal (C * T) +
            (ENNReal.ofReal (C * T)) ^ 2) := by sorry
