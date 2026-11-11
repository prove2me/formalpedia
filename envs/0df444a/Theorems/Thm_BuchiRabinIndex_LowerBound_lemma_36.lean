-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_36
-- name    : BuchiRabinIndex.LowerBound.lemma_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:52.1302+00:00
-- url     : https://prove2.me/theorems/5c7c4a1d-3672-4e47-a176-cde573c8b89e
-- title:
--   Lemma 36 — small cliques and the recursion
-- statement:
--   For $n\ge1$, write $g(n,c)$ for the largest clique of $G_n$ with all weights at most $c$. For $0\le c\le\lfloor n/2\rfloor$,
--   $$g(n,c)=2^c.$$
--   For $n\ge2$ and $1\le c\le n-1$,
--   $$g(n,c)=\max_{0\le a,b\le c-1,\ a+b\le n-2}\bigl(g(n-1,a)+g(n-1,b)\bigr).$$
--
--   The maximum ranges over a nonempty finite set, including $(a,b)=(0,0)$. Both the small-weight formula and the complete recursion are stated.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 36, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 36; statement only. -/
theorem lemma_36 (n : ℕ) (hn : 1 ≤ n) :
    (∀ c, c ≤ n / 2 → g n c = 2 ^ c) ∧
    (2 ≤ n → ∀ c, 1 ≤ c → c ≤ n - 1 →
      g n c = (((Finset.range c).product (Finset.range c)).filter
        (fun ab => ab.1 + ab.2 ≤ n - 2)).sup
          (fun ab => g (n - 1) ab.1 + g (n - 1) ab.2)) := by sorry

end BuchiRabinIndex.LowerBound
