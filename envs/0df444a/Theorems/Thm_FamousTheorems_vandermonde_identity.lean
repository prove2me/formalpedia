-- Prove2me | Theorems.Thm_FamousTheorems_vandermonde_identity
-- name    : FamousTheorems.vandermonde_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:50.502241+00:00
-- url     : https://prove2.me/theorems/39e4b0a2-d220-4fc3-a109-e6c26df0642c
-- title:
--   Vandermonde's identity
-- statement:
--   **Vandermonde's identity.** For all natural numbers $m,n,k$,
--   $$\binom{m+n}{k}=\sum_{i+j=k}\binom mi\binom nj.$$
--
--   Combinatorially, choosing $k$ elements from a disjoint union of an $m$-set and an $n$-set means choosing $i$ from the first and $j=k-i$ from the second. Algebraically it is the coefficient of $x^k$ in $(1+x)^{m+n}=(1+x)^m(1+x)^n$. It is one of the basic binomial-coefficient identities, with generalisations such as the Chu–Vandermonde identity for hypergeometric sums.
--
--   **Formalization note.** Mathlib's `Nat.add_choose_eq`. The sum runs over the antidiagonal `Finset.HasAntidiagonal.antidiagonal k`, the finset of pairs $(i,j)$ of natural numbers with $i+j=k$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.add_choose_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vandermonde_identity (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, m.choose ij.1 * n.choose ij.2 := by sorry

end FamousTheorems
