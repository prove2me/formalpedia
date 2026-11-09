-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_4_3
-- name    : ChangingCache.UpperBound.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:05.770251+00:00
-- url     : https://prove2.me/theorems/f86c9a85-d9f8-4beb-a26d-ffcbca936527
-- title:
--   Lemma 4.3 — Request-sequence reduction (with the greedy clause)
-- statement:
--   Fix $(a,s)$ augmentation with $s\ge1$. If a memory profile $m$ and a finite request sequence $\sigma$ give LRU more than $s$ times as many misses as OPT,
--   $$F_{LRU}(\sigma)\ >\ s\,F_{OPT}(\sigma),$$
--   then the same memory profile has a finite request sequence $\sigma'$ on which LRU still has more than $s$ times as many misses as OPT and which satisfies Properties (R1) and (R2) for some OPT of $\sigma'$. Moreover, $\sigma'$ can be chosen so that whenever OPT holds a page absent from LRU, the next request is to such a page.
--
--   The lemma removes the requests that help LRU: non-cold misses of OPT are renamed to new pages and hits in both caches are deleted. The greedy clause is the shape of the adversary used by the lower bound.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: OPT, the legal policy with the fewest misses → `optMisses m σ`, the infimum over legal policies of their miss count (attained, the set being nonempty for a memory profile); reason: Lean convention; the minimum of a nonempty set of natural numbers
--   - encoding: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$, an integer number of pages → real $a$ and $s\ge1$, and LRU's capacity law is any `C : ℕ → ℕ` with $C(k)=a\cdot m(\lfloor k/s\rfloor)$ as real numbers for every $k$ (hypothesis `hC`); reason: Eq. (1) stated as an equation on integer page counts, with no rounding; it covers every $(a,s)$ for which Eq. (1) gives page counts on $m$, and nothing else
--   - encoding: new pages are always available (renamings to a new page) → the page type is `Infinite`; reason: the source's pages are unbounded identifiers; the statement asks for a sequence built from new pages, which a finite page type cannot supply
--   - encoding: the sequence satisfies (R1) and (R2); whenever OPT holds a page absent from LRU, the next request is to such a page → an optimal legal policy $S'$ for $\sigma'$ is exhibited; (R1) for LRU, (R2) and the greedy clause hold for $S'$, the greedy clause at the positions $0\le i<n$ that have a next request; reason: the properties refer to OPT of the run; there is no next request after the last one
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 4.3, p. 8 (proof pp. 9–11)

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- Throughout, `(a, s)` augmentation is encoded by LRU's capacity law `C`, an integer page count
with `C k = a · m(⌊k / s⌋)` (Eq. (1), p. 7) for real `a` and `s ≥ 1`.

**Lemma 4.3 (Request-sequence reduction)**, p. 8. Fix `(a, s)` augmentation. If a memory profile
`m` and a finite request sequence `σ` give LRU more than `s` times as many misses as OPT, then the
same profile has a finite request sequence `σ'`, with an OPT `S'`, on which LRU still has more than
`s` times as many misses as OPT and which satisfies Properties (R1) and (R2); moreover, whenever
OPT holds a page absent from LRU, the next request is to such a page. -/
theorem lemma_4_3 {α : Type*} [DecidableEq α] [Infinite α] (a s : ℝ) (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : IsMemoryProfile m)
    (C : ℕ → ℕ) (hC : ∀ k, (C k : ℝ) = a * (m ⌊(k : ℝ) / s⌋₊ : ℝ))
    (σ : List α)
    (hce : s * (optMisses m σ : ℝ) < ((lruRun C σ).misses : ℝ)) :
    ∃ (σ' : List α) (S' : ℕ → Finset α),
      IsOptimal m σ' S' ∧
      s * (optMisses m σ' : ℝ) < ((lruRun C σ').misses : ℝ) ∧
      LRUAlwaysMisses C σ' ∧
      AllMissesCold σ' S' ∧
      IsGreedy C σ' S' := by sorry

end ChangingCache.UpperBound
