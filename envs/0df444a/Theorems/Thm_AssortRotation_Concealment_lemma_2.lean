-- Prove2me | Theorems.Thm_AssortRotation_Concealment_lemma_2
-- name    : AssortRotation.Concealment.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:14.487627+00:00
-- url     : https://prove2.me/theorems/4bfb15c0-6a45-48c2-9fd3-b7260cf94b56
-- title:
--   Lemma 2, p. 13 — one extra past purchase costs at most the highest remaining price: $R_{k+1}(n)\le R_k(n)\le\rho^*_n+R_{k+1}(n)$
-- statement:
--   Products are offered sequentially; a consumer who has already bought $k$ items buys the current product $(p,X)$ iff $v(k)+X-p\ge 0$, where $v$ is nonnegative and decreasing. Let $R_k(n)$ be the revenue from the last $n$ products when the consumer enters them having bought $k$ items. Let $\rho^*_n$ be the highest price among those $n$ products, with $\rho^*_0=0$. If all prices are nonnegative, then for every $k$
--   $$
--   R_{k+1}(n)\ \le\ R_k(n)\ \le\ \rho^*_n+R_{k+1}(n).
--   $$
--
--   A consumer with one more past purchase is less willing to buy. She nonetheless buys at most one product fewer, so she costs the retailer at most one remaining price. This bound drives the interchange argument (Lemma 4) behind Theorem 1.
--
--   **Formalization Note.** The last $n$ products are an arbitrary list $L$ of (price, shock) pairs, and the statement holds for every realization. The paper's "with probability 1" is thus strengthened to "always". The paper restricts to $k\le N-n-1$; the Lean statement holds for every $k$. The purchase rule uses $\ge 0$ (as in (5)–(6)) where (7) prints $>0$. The printed "$\rho^*_n=\max\{\dots\}$ if $n>1$" is read as $n\ge 1$, with $\rho^*_0=0$.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 13, Lemma 2, (7)–(8)

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Lemma 2, p. 13. For any list `L` of products (the last `n` products of the sequence) with
nonnegative prices and any number `k` of past purchases,
`R_{k+1}(n) ≤ R_k(n) ≤ ρ*_n + R_{k+1}(n)`, where `R_k(n) = seqRev v L k` and
`ρ*_n = rhoStar L` is the highest remaining price (`0` for `n = 0`). -/
theorem lemma_2 (v : ℕ → ℝ) (hv : MarginalUtility v) (L : List (ℝ × ℝ))
    (hp : ∀ a ∈ L, 0 ≤ a.1) (k : ℕ) :
    seqRev v L (k + 1) ≤ seqRev v L k ∧ seqRev v L k ≤ rhoStar L + seqRev v L (k + 1) := by sorry

end AssortRotation.Concealment
