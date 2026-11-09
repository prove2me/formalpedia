-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lru_three_speed_upper_bound
-- name    : ChangingCache.UpperBound.lru_three_speed_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:07.888815+00:00
-- url     : https://prove2.me/theorems/e2e1d732-c8da-4e2d-95a5-eda823e5d8af
-- title:
--   Theorem 1.1 — LRU with twice the memory and three times the speed finishes no later than OPT
-- statement:
--   Let $m$ be any memory profile: positive integers $m(0),m(1),\dots$ with $m(j+1)\le m(j)+1$. Let $\sigma$ be any finite request sequence over any set of pages. Both caches start empty and load only requested pages. OPT is the fewest misses of a legal policy with capacity $m(j)$ after its $j$-th miss. LRU runs under $(2,3)$ augmentation, so its capacity after $k$ misses is $2m(\lfloor k/3\rfloor)$ and each of its misses takes time $1/3$. Then LRU incurs at most three times as many misses as OPT, so its makespan is at most OPT's:
--   $$F_{LRU}(\sigma)\ \le\ 3\,F_{OPT}(\sigma),\qquad\text{equivalently}\qquad \frac{F_{LRU}(\sigma)}{3}\ \le\ F_{OPT}(\sigma).$$
--
--   In other words, under $(2,3)$ augmentation LRU's makespan competitive ratio is at most 1. The bound improves the $(4,4)$ guarantee of Bender et al. (2014); Theorem 1.2 of the same paper shows that $(2,2)$ augmentation does not suffice.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: OPT, the legal policy with the fewest misses → `optMisses m σ`, the infimum over legal policies of their miss count (attained, the set being nonempty for a memory profile); reason: Lean convention; the minimum of a nonempty set of natural numbers
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: LRU has a makespan competitive ratio of at most 1 (supremum of LRU's makespan over OPT's) → for every profile and sequence, $F_{LRU}\le 3F_{OPT}$ and $F_{LRU}/3\le F_{OPT}$ in $\mathbb R$; reason: the supremum is at most 1 iff every ratio is; the time inequality also covers the empty sequence, where the ratio $0/0$ is undefined
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Theorem 1.1, p. 2 (repeated p. 12); proof via Corollary 4.2 and Theorem 5.1, pp. 8–16

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-- **Theorem 1.1 (Upper bound)**, p. 2 (repeated p. 12). Under `(2, 3)` augmentation LRU has a
makespan competitive ratio of at most 1: for every memory profile `m` and finite request sequence
`σ`, both caches starting empty, LRU (capacity `2 m(⌊k/3⌋)` after `k` misses) incurs at most three
times as many misses as OPT, so its makespan `F_LRU / 3` is at most OPT's makespan `F_OPT`. -/
theorem lru_three_speed_upper_bound {α : Type*} [DecidableEq α] (m : ℕ → ℕ)
    (hm : IsMemoryProfile m) (σ : List α) :
    (lruRun (augCap 2 3 m) σ).misses ≤ 3 * optMisses m σ ∧
      ((lruRun (augCap 2 3 m) σ).misses : ℝ) / 3 ≤ (optMisses m σ : ℝ) := by sorry

end ChangingCache.UpperBound
