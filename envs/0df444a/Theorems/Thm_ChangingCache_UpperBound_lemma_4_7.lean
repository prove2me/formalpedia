-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_4_7
-- name    : ChangingCache.UpperBound.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:55.962206+00:00
-- url     : https://prove2.me/theorems/24165a31-a7db-41c4-b24c-05ccb697e6a8
-- title:
--   Lemma 4.7 — Tight profile
-- statement:
--   Fix $(a,s)$ augmentation with $s\ge1$, and let OPT and LRU run on a memory profile $m$ over a request sequence $\sigma$ satisfying Properties (R1) and (R2), with OPT discarding eagerly. Let $F$ be the number of misses of OPT, and let $m'$ be the tight profile: for $1\le j\le F$, $m'(j)$ is one more than the number of pages OPT loaded at its first $j-1$ misses that are requested after its $j$-th miss; $m'(0)=1$; and $m'(j)=\min\{m(j),m'(F)\}$ for $j>F$. Then
--   1. $m'$ is a memory profile;
--   2. $m'(j)\le m(j)$ for every $j$;
--   3. OPT has the same hits and misses on $m'$ as on $m$;
--   4. the run on $m'$ satisfies Properties (R1) to (R3).
--
--   Lowering the profile removes the capacity OPT never uses; LRU only loses capacity, so it keeps missing on every request.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - reading: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$; no range is stated for $a$ → $a\in\mathbb N$ (any natural number), $s\in\mathbb R$ with $s\ge1$, capacity `augCap a s m k` $=a\cdot m(\lfloor k/s\rfloor)$; reason: capacities are page counts, and this result applies Eq. (1) to a new profile $m'$ that the source constructs (Lemma 4.7 sets $m'(0)=1$, so LRU's capacity $a\,m'(0)=a$ is a page count only when $a$ is an integer); Lemmas 4.3–4.6, which keep the profile fixed, are instead stated for every real $a$ with integral capacities; the paper uses $a=2$ throughout; no lower bound on $a$ is imposed since the source states none
--   - encoding: OPT has the same hits and misses on $m'$ as on $m$; the run on $m'$ satisfies (R1)–(R3) → the same policy $S$ is legal on $m'$ (so its hits and misses are literally the same), and `IsReduced a s m' σ S`, which also records that $m'$ is a memory profile and that $S$ is optimal on $m'$; reason: Definition 4.1 is a property of a run of OPT and LRU; OPT on $m'$ is the same policy
--   - encoding: $m'(F)$ in $m'(j)=\min\{m(j),m'(F)\}$ → $m'(F)=m'(0)=1$ when $F=0$; reason: the source's own value of $m'(0)$
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 4.7, p. 11

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- **Lemma 4.7 (Tight profile)**, p. 11. Fix `(a, s)` augmentation, and let OPT `S` and LRU run on
a memory profile `m` over `σ` satisfying (R1) and (R2), with OPT discarding eagerly. Then the tight
profile `m' = tightProfile m σ S` is a memory profile with `m' ≤ m` pointwise, OPT (the same policy
`S`, hence with the same hits and misses) is legal on `m'`, and the run on `m'` satisfies (R1) to
(R3), i.e. is reduced. -/
theorem lemma_4_7 {α : Type*} [DecidableEq α] (a : ℕ) (s : ℝ) (hs : 1 ≤ s) (m : ℕ → ℕ)
    (hm : IsMemoryProfile m) (σ : List α) (S : ℕ → Finset α) (hopt : IsOptimal m σ S)
    (hR1 : LRUAlwaysMisses (augCap a s m) σ) (hR2 : AllMissesCold σ S)
    (heager : DiscardsEagerly σ S) :
    IsMemoryProfile (tightProfile m σ S) ∧
      (∀ j, tightProfile m σ S j ≤ m j) ∧
      IsLegal (tightProfile m σ S) σ S ∧
      IsReduced a s (tightProfile m σ S) σ S := by sorry

end ChangingCache.UpperBound
