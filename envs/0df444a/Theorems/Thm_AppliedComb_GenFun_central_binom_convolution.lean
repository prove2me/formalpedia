-- Prove2me | Theorems.Thm_AppliedComb_GenFun_central_binom_convolution
-- name    : AppliedComb.GenFun.central_binom_convolution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:13:44.846505+00:00
-- url     : https://prove2.me/theorems/6f433390-eab6-48c8-9859-43b712930cc9
-- title:
--   Corollary 8.14 — 2^{2n} = Σ C(2k, k) C(2n − 2k, n − k)
-- statement:
--   For every integer $n \ge 0$,
--
--   $$2^{2n} = \sum_{k=0}^{n} \binom{2k}{k} \binom{2n-2k}{n-k}.$$
--
--   The self-convolution of the central binomial coefficients is the sequence of powers of $4$. For example, at $n = 2$: $1\cdot 6 + 2 \cdot 2 + 6 \cdot 1 = 16$. The identity has no evident one-line combinatorial proof, and in the chapter it is the end point of the chain Lemma 8.11 → Lemma 8.12 (with Newton's Binomial Theorem 8.10) → Theorem 8.13 → Corollary 8.14 (with Proposition 8.3).
--
--   **Formalization Note.** An identity of natural numbers, with `Nat.choose`. Throughout the sum $0 \le k \le n$, so the subtractions $2n - 2k$ and $n - k$ are exact.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 168, Corollary 8.14

import Mathlib

namespace AppliedComb.GenFun

/-- Keller–Trotter, Corollary 8.14 (p. 168): for all `n ≥ 0`,
`2^(2n) = ∑_{k=0}^{n} C(2k, k) · C(2n - 2k, n - k)`, an identity of natural numbers
(`k ≤ n` throughout the sum, so both subtractions are exact). -/
theorem central_binom_convolution (n : ℕ) :
    2 ^ (2 * n) = ∑ k ∈ Finset.range (n + 1),
      Nat.choose (2 * k) k * Nat.choose (2 * n - 2 * k) (n - k) := by sorry

end AppliedComb.GenFun
