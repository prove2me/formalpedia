-- Prove2me | solution 1 for rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T21:25:22.677412+00:00
-- url     : https://prove2.me/submissions/d3362e2d-e37b-4bac-8d29-9664a7b96d39

import Theorems.Thm_schatten_norm_even_pow_eq_trace_row_gram_pow
import Theorems.Thm_buchholz_evenq_trace_pairbound

open MatrixCompletion
open scoped BigOperators

-- Reduction of the even-q Schatten-moment node onto K-even-id (Proved) + K-pairbound (Open).
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  -- Step 1: rewrite the integrand via K-even-id, pointwise inside the expectation.
  have hpt : ∀ eps : Finset (Fin n1 × Fin n2),
      schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n)
        = Matrix.trace ((rademacherSampledMatrix Omega eps p X *
            (rademacherSampledMatrix Omega eps p X).transpose) ^ n) := by
    intro eps
    have h := schatten_norm_even_pow_eq_trace_row_gram_pow n hn
      (rademacherSampledMatrix Omega eps p X)
    -- the cast (2*n : ℝ) vs (2*n : ℕ) on schattenNorm
    simpa using h
  have hrw :
      rademacherExpectation
          (fun eps =>
            schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
        = rademacherExpectation
          (fun eps =>
            Matrix.trace ((rademacherSampledMatrix Omega eps p X *
              (rademacherSampledMatrix Omega eps p X).transpose) ^ n)) := by
    unfold rademacherExpectation
    apply Finset.sum_congr rfl
    intro eps _
    simp only [hpt eps]
  rw [hrw]
  -- Step 2: apply K-pairbound.
  exact buchholz_evenq_trace_pairbound n hn Omega p hp X
