-- Prove2me | Theorems.Thm_FiniteLattice_weighted_weisner_cancellation
-- name    : FiniteLattice.weighted_weisner_cancellation
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-22T14:41:08.941935+00:00
-- url     : https://prove2.me/theorems/7aaef4ef-b6d4-43f6-82ae-d8ea5f8a4dc1
-- title:
--   Weighted Weisner cancellation in a finite lattice
-- statement:
--   Let $L$ be a finite lattice, let $d,a,b\in L$ with $a\le b$, and let $w:L\to\mathbb Q$. Suppose that for every $x$ in the interval $[a,b]$, the weighted prefix sum
--   $$\sum_{d\le c\le x} w(c)=0.$$
--   Then the weighted join fibre at $b$ vanishes:
--   $$\sum_{\substack{d\le c\le b\\c\vee a=b}}w(c)=0.$$
--   No relation between $d$ and $a$ is assumed. This is a complete finite-lattice statement, not a conditional reduction.
-- source:
--   A proved weighted prefix-cancellation form whose mechanism is the order-dual of Weisner's theorem. It is our weighted generalization, not a verbatim formula in the source. See Richard P. Stanley, Enumerative Combinatorics, Volume 1, author manuscript, Corollary 3.9.3 (p. 313), applied in the order dual: https://math.mit.edu/~rstan/ec/ec1.pdf.

import Mathlib
open Finset
attribute [local instance] Classical.propDecidable

namespace FiniteLattice

theorem weighted_weisner_cancellation {L : Type*} [Lattice L] [Fintype L] [DecidableEq L]
    (d a b : L) (w : L → ℚ) (hab : a ≤ b)
    (hzero : ∀ x : L, a ≤ x → x ≤ b →
      (∑ c ∈ (Finset.univ : Finset L).filter (fun c => d ≤ c ∧ c ≤ x), w c) = 0) :
    (∑ c ∈ (Finset.univ : Finset L).filter
      (fun c => d ≤ c ∧ c ≤ b ∧ c ⊔ a = b), w c) = 0 := by
  sorry

end FiniteLattice
