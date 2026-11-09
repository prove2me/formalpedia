-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_4_6
-- name    : ChangingCache.UpperBound.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:05.835913+00:00
-- url     : https://prove2.me/theorems/01d17d2a-62ae-4a72-9889-8e43d40095f1
-- title:
--   Lemma 4.6 — Inserting a miss
-- statement:
--   Fix $(a,s)$ augmentation and a memory profile $m$. Let $A$ be a run of LRU on a request sequence $\sigma$, and let $B$ be the same run with a request to a page $x$ inserted at some point $i$ (after the first $i$ requests), where LRU does not hold $x$ at that point. Then after every request of $A$'s sequence LRU has missed at least as often in $B$ as in $A$: for every $0\le t\le n$,
--   $$F^{B}_{LRU}(t')\ \ge\ F^{A}_{LRU}(t),\qquad t'=\begin{cases}t,& t\le i,\\ t+1,& t>i,\end{cases}$$
--   where $t'$ is the position in $B$ of $A$'s $t$-th request.
--
--   This yields the greedy clause of Lemma 4.3: a request that hits in OPT and misses in LRU may be moved as early as possible.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$, an integer number of pages → real $a$ and $s\ge1$, and LRU's capacity law is any `C : ℕ → ℕ` with $C(k)=a\cdot m(\lfloor k/s\rfloor)$ as real numbers for every $k$ (hypothesis `hC`); reason: Eq. (1) stated as an equation on integer page counts, with no rounding; it covers every $(a,s)$ for which Eq. (1) gives page counts on $m$, and nothing else
--   - encoding: a run of LRU; after every request of $A$'s sequence → LRU from the empty cache over $\sigma$; request $t$ of $A$ is compared with request $t'$ of $B$, $t'=t$ for $t\le i$ and $t'=t+1$ for $t>i$; reason: a run from any point of a run is the tail of a run from the empty cache; the inserted request shifts the later requests by one
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 4.6, p. 10

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-- Throughout, `(a, s)` augmentation is encoded by LRU's capacity law `C`, an integer page count
with `C k = a · m(⌊k / s⌋)` (Eq. (1), p. 7) for real `a` and `s ≥ 1`.

**Lemma 4.6 (Inserting a miss)**, p. 10. Let `A` be the run of LRU under `(a, s)` augmentation on
the memory profile `m` over `σ`, and let `B` be the same run with a request to a page `x` inserted
after the first `i` requests, where LRU does not hold `x` at that point. Then after every request of
`A`'s sequence (the `t`-th request of `A` is the `t`-th of `B` for `t ≤ i` and the `(t+1)`-th for
`t > i`), LRU has missed at least as often in `B` as in `A`. -/
theorem lemma_4_6 {α : Type*} [DecidableEq α] (a s : ℝ) (hs : 1 ≤ s) (m : ℕ → ℕ)
    (hm : IsMemoryProfile m)
    (C : ℕ → ℕ) (hC : ∀ k, (C k : ℝ) = a * (m ⌊(k : ℝ) / s⌋₊ : ℝ))
    (σ : List α) (i : ℕ) (hi : i ≤ σ.length) (x : α)
    (hx : x ∉ (lruRun C (σ.take i)).cache) :
    ∀ t ≤ σ.length, (lruRun C (σ.take t)).misses ≤
      (lruRun C
        ((σ.take i ++ x :: σ.drop i).take (if t ≤ i then t else t + 1))).misses := by sorry

end ChangingCache.UpperBound
