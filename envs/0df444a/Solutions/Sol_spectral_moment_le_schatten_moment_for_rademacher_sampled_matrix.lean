-- Prove2me | solution 1 for spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T04:51:10.403046+00:00
-- url     : https://prove2.me/submissions/06951f50-53dc-45ff-82bc-77c87e678537

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_spectral_norm_le_schatten_norm
import Theorems.Thm_rademacher_expectation_monotone

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∀ (β : ℝ), 2 < β →
    ∀ (n₁ n₂ m q : ℕ)
      (Omega : Finset (Fin n₁ × Fin n₂))
      (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      1 ≤ q →
      (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
      rademacherExpectation
          (fun eps =>
            spectralNorm
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        rademacherExpectation
          (fun eps =>
            schattenNorm (q : ℝ)
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) := by
  intro β _ n₁ n₂ m q Omega X hq _
  apply rademacher_expectation_monotone
  intro S
  -- Pointwise: spectralNorm A ^ q ≤ schattenNorm q A ^ q.
  set A := rademacherSampledMatrix Omega S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X with hA
  have hsp : spectralNorm A ≤ schattenNorm (q : ℝ) A :=
    spectral_norm_le_schatten_norm q A hq
  have hnn : 0 ≤ spectralNorm A := by
    unfold spectralNorm; positivity
  exact pow_le_pow_left₀ hnn hsp q
