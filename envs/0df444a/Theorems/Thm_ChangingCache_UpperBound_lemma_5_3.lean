-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_3
-- name    : ChangingCache.UpperBound.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:17.592485+00:00
-- url     : https://prove2.me/theorems/e5c678ce-a717-41ca-b87d-3982e0dd1717
-- title:
--   Lemma 5.3 — LRU is full at positions $3i+1$
-- statement:
--   Consider a reduced run of length $n$ under $(2,3)$ augmentation, and let $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ be LRU's capacity after $k$ misses. Then for every integer $i\ge1$ with $3i+1\le n$,
--   $$|P_{LRU}(3i+1)|=2m(i)=m_{LRU}(3i+1).$$
--   That is, LRU is full after every request at a position $\equiv1\pmod 3$, from position $4$ on.
--
--   This is why the invariant Eq. (4) is stated only at positions $\equiv1\pmod3$.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.3, p. 12

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- **Lemma 5.3**, p. 12. In a reduced run of length `n` under `(2, 3)` augmentation,
`|P_LRU(3i + 1)| = 2 m(i) = m_LRU(3i + 1)` for every integer `i ≥ 1` with `3i + 1 ≤ n`, where
`m_LRU(k) = 2 m(⌊k/3⌋)` is LRU's capacity after `k` misses (Eq. (3)): LRU is full after every
request at a position `≡ 1 (mod 3)` from position `4` on. -/
theorem lemma_5_3 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ i : ℕ, 1 ≤ i → 3 * i + 1 ≤ σ.length →
      (lruCache (augCap 2 3 m) σ (3 * i + 1)).card = 2 * m i ∧
        2 * m i = augCap 2 3 m (3 * i + 1) := by sorry

end ChangingCache.UpperBound
