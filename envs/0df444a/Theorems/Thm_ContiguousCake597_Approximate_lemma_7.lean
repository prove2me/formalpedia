-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_7
-- name    : ContiguousCake597.Approximate.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:41.636962+00:00
-- url     : https://prove2.me/theorems/6de9d367-220f-4214-8cea-605bb70e8fcf
-- title:
--   Lemma 7 — assignment-independent price range
-- statement:
--   Let $N\ge1$ be arbitrary. Let $\pi$ and $\sigma$ be arbitrary permutations of $[N]$, with $\pi$ a single cycle traversing every index. Let $\eta\ge0$ and let $q_1,\ldots,q_N$ be arbitrary real prices. If
--   $$q_{\sigma(i)}\ge\max\{q_i,q_{\pi(i)}\}-\eta\quad\text{for every }i,$$
--   then
--   $$\max_jq_j-\min_jq_j\le N\eta.$$
--   Equivalently, every ordered pair satisfies $q_j-q_i\le N\eta$. The singleton case and zero error are included; no positivity or rationality of prices is required. This is a standalone combinatorial lemma, with no cake-specific parameters or assignment restriction.
--
--   Differences from the source:
--   - encoding: the finite maximum minus minimum is at most Nη → every ordered pair satisfies q_j−q_i≤Nη; reason: on a nonempty finite set the largest pairwise difference is exactly the maximum minus minimum; this avoids default extrema and includes N=1
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 9 (PDF 10), Lemma 7

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 7, printed p.9 (PDF 10). Pairwise differences are equivalent
to the finite maximum-minus-minimum bound; n=1 and eta=0 are included. -/
theorem lemma_7 (n : ℕ) (hn : 1 ≤ n) (p sigma : Equiv.Perm (Fin n))
    (hp : SingleCycle p) (e : ℝ) (he : 0 ≤ e) (q : Fin n → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    ∀ i j : Fin n, q j - q i ≤ (n : ℝ) * e := by sorry

end ContiguousCake597.Approximate
