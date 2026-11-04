-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_grid_second_moment_bound
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_second_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:26:54.506471+00:00
-- url     : https://prove2.me/theorems/299e1bf8-d738-462d-acce-585ddc658157
-- title:
--   Quantitative original signed Lévy grid second-moment bound from the actual nonnegative supported test
-- statement:
--   Uniformly over all sufficiently small positive mesh widths and grid counts whose endpoint lies before T, the actual original-process signed sum of g(increments) has a bounded ENNReal second moment, under pointwise domination of |g| by a bounded negative-mark test f. Derives the estimate directly from the previously proved original X.X L2 bound and finite-sum e-norm triangle inequality. No a.e. grid convergence or rate claim required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_signed_grid_second_moment_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
          (∫⁻ ω, ‖(∑ i ∈ Finset.range n,
            g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) ω -
               X.X ((i : ℝ≥0) * Real.toNNReal h) ω))‖ₑ ^ (2 : ℕ) ∂P)
          ≤ M ^ 2 * (ENNReal.ofReal (C * T) +
                         (ENNReal.ofReal (C * T)) ^ 2) := by sorry
