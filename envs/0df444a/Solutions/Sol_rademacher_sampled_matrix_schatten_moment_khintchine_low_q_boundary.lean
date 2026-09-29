-- Prove2me | solution 1 for rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T20:55:48.160259+00:00
-- url     : https://prove2.me/submissions/29f95a64-1a5c-4ce9-b509-b6624b1f0f09

import Theorems.Thm_khintchine_low_q_window_forces_unit_dimension
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound

open MatrixCompletion

/-- Source: Candes-Recht 2008, Section 6.1, Lemma 6.1, p. 24.

The source Khintchine inequality applies for `q ≥ 2`.  The uploaded parent also
mentions integer `q` with `1 ≤ q`, so the low-`q` child is reduced to two
formal residues: the logarithmic window forces `max n₁ n₂ ≤ 1`, and the
remaining one-dimensional Schatten/variance estimate handles that corner. -/
theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        ¬ 2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  rcases rademacher_sampled_matrix_schatten_moment_khintchine_low_q_unit_dimension_bound with
    ⟨Ckh, hCkh, hUnit⟩
  refine ⟨Ckh, hCkh, ?_⟩
  intro C' hC' β hβ n₁ n₂ m q Omega X hqOne hqNotTwo hqlog
  have hdim : max n₁ n₂ ≤ 1 :=
    khintchine_low_q_window_forces_unit_dimension
      β hβ n₁ n₂ q hqOne hqNotTwo hqlog
  exact hUnit C' hC' β hβ n₁ n₂ m q Omega X
    hqOne hqNotTwo hdim hqlog
