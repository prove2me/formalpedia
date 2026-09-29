-- Prove2me | solution 1 for rademacher_sampled_trace_moment_eq_buchholz_signed_walk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T23:19:34.365499+00:00
-- url     : https://prove2.me/submissions/e7dde069-b588-4f86-ac26-f5a735ffbbc1

import Theorems.Thm_rademacher_sampled_trace_eq_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Section 2; Candès--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

Reduction: prove the trace expansion pointwise for each sign assignment, then
apply the finite Rademacher expectation to the resulting function equality.
-/
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      =
    rademacherExpectation
        (fun eps => buchholzSignedWalkSum n Omega p X eps) := by
  congr 1
  funext eps
  exact rademacher_sampled_trace_eq_buchholz_signed_walk_sum n hn Omega eps p hp X
