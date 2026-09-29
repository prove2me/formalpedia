-- Prove2me | solution 1 for rademacher_sampled_trace_eq_buchholz_signed_walk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T01:32:23.172325+00:00
-- url     : https://prove2.me/submissions/148f3a52-95f7-4924-9824-3ba0313df8d3

import Theorems.Thm_trace_row_gram_power_eq_alternating_walk_sum
import Theorems.Thm_rademacher_sampled_walk_product_eq_buchholz_signed_walk_term

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Section 2, expands
`trace ((S Sᵀ)^n)` over closed alternating walks.  Candes--Recht use this
expansion in Section 6.1, Lemma 6.1, PDF p. 25, after setting `S` to the
sampled Rademacher coordinate matrix.  This sketch is a purely formal bridge:
first apply the row-Gram closed-walk trace expansion, then rewrite every
expanded walk product as the named Buchholz signed term.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ) (_hp : 0 < p)
    (X : RealMatrix n1 n2) :
    Matrix.trace
        ((rademacherSampledMatrix Omega eps p X *
            (rademacherSampledMatrix Omega eps p X).transpose) ^ n)
      = buchholzSignedWalkSum n Omega p X eps := by
  rw [trace_row_gram_power_eq_alternating_walk_sum n hn
      (rademacherSampledMatrix Omega eps p X)]
  unfold buchholzSignedWalkSum
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  exact rademacher_sampled_walk_product_eq_buchholz_signed_walk_term
    Omega eps p X rows cols
