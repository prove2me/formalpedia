-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_2
-- name    : ChangingCache.UpperBound.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:02.384444+00:00
-- url     : https://prove2.me/theorems/8f7eee61-cbaf-433b-ace3-0a6f877990bc
-- title:
--   Lemma 5.2 — LRU's cache is a window of distinct recent requests
-- statement:
--   Consider a reduced run of length $n$ under $(2,3)$ augmentation, and write $c(i)=|P_{LRU}(i)|$.
--   1. After request $\sigma_i$ ($0\le i\le n$), LRU holds exactly the pages $\sigma_{i-c(i)+1},\dots,\sigma_i$, which are distinct.
--   2. $i-c(i)$ is nondecreasing in $i$.
--   3. Consequently, a page requested at a step $i'$ with $i-c(i)<i'\le i$ is in LRU after every step $u$ with $i'\le u\le i$.
--
--   This is the window property that replaces Sleator and Tarjan's fixed-cache phases: in normal form LRU's cache is always a block of the most recent requests.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
--   - encoding: LRU holds exactly the pages $\sigma_{i-c(i)+1},\dots,\sigma_i$, which are distinct; $i-c(i)$ → $c(i)\le i$, the list `(σ.take i).drop (i - c i)` has no duplicates and its set of entries is $P_{LRU}(i)$; $i-c(i)$ is compared in $\mathbb Z$; reason: the window $\sigma_{i-c(i)+1},\dots,\sigma_i$ presupposes $c(i)\le i$; the integer form avoids truncated subtraction
--   - encoding: a page requested at step $i'$ → the entry `σ[i' - 1]`, for $1\le i'\le i$; reason: 0-based list indexing
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.2, p. 12

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- **Lemma 5.2**, p. 12. In a reduced run under `(2, 3)` augmentation, write `c(i) = |P_LRU(i)|`.
1. After request `σ_i` (`0 ≤ i ≤ n`), LRU holds exactly the pages `σ_{i-c(i)+1}, …, σ_i`, which are
   distinct (in particular `c(i) ≤ i`);
2. `i - c(i)` is nondecreasing in `i`;
3. consequently, a page requested at a step `i'` with `i - c(i) < i' ≤ i` is in LRU after every step
   `u` with `i' ≤ u ≤ i`. -/
theorem lemma_5_2 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    (∀ i ≤ σ.length,
      (lruCache (augCap 2 3 m) σ i).card ≤ i ∧
      ((σ.take i).drop (i - (lruCache (augCap 2 3 m) σ i).card)).Nodup ∧
      lruCache (augCap 2 3 m) σ i =
        ((σ.take i).drop (i - (lruCache (augCap 2 3 m) σ i).card)).toFinset) ∧
    (∀ i j, i ≤ j → j ≤ σ.length →
      (i : ℤ) - ((lruCache (augCap 2 3 m) σ i).card : ℤ) ≤
        (j : ℤ) - ((lruCache (augCap 2 3 m) σ j).card : ℤ)) ∧
    (∀ i ≤ σ.length, ∀ i', 1 ≤ i' → i' ≤ i →
      (i : ℤ) - ((lruCache (augCap 2 3 m) σ i).card : ℤ) < (i' : ℤ) →
      ∀ u, i' ≤ u → u ≤ i → ∀ p ∈ σ[i' - 1]?, p ∈ lruCache (augCap 2 3 m) σ u) := by sorry

end ChangingCache.UpperBound
