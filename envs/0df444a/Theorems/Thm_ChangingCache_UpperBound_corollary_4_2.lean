-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_corollary_4_2
-- name    : ChangingCache.UpperBound.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:01.763929+00:00
-- url     : https://prove2.me/theorems/72be0dbc-a015-45bf-9b57-45a01135d8eb
-- title:
--   Corollary 4.2 — Reduction suffices
-- statement:
--   Fix $(a,s)$ augmentation with $s\ge1$. If some memory profile $m$ and finite request sequence $\sigma$ give LRU more than $s$ times as many misses as OPT, then some reduced run of some length $n$ (on some memory profile $m'$, with some OPT) has
--   $$n\ >\ s\,F_{OPT}(n).$$
--
--   In a reduced run LRU misses on every request, so $F_{LRU}(n)=n$; the corollary therefore says that every counterexample to an upper bound with speed $s$ can be assumed to be in normal form.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - reading: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$; no range is stated for $a$ → $a\in\mathbb N$ (any natural number), $s\in\mathbb R$ with $s\ge1$, capacity `augCap a s m k` $=a\cdot m(\lfloor k/s\rfloor)$; reason: capacities are page counts, and this result applies Eq. (1) to a new profile $m'$ that the source constructs (Lemma 4.7 sets $m'(0)=1$, so LRU's capacity $a\,m'(0)=a$ is a page count only when $a$ is an integer); Lemmas 4.3–4.6, which keep the profile fixed, are instead stated for every real $a$ with integral capacities; the paper uses $a=2$ throughout; no lower bound on $a$ is imposed since the source states none
--   - encoding: new pages are always available (renamings to a new page) → the page type is `Infinite`; reason: the source's pages are unbounded identifiers; the statement asks for a sequence built from new pages, which a finite page type cannot supply
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Corollary 4.2, p. 8

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- **Corollary 4.2 (Reduction suffices)**, p. 8. Fix `(a, s)` augmentation. If some memory profile
`m` and finite request sequence `σ` give LRU more than `s` times as many misses as OPT, then some
reduced run (profile `m'`, sequence `σ'` of length `n`, OPT `S'`) has `n > s · F_OPT(n)`. -/
theorem corollary_4_2 {α : Type*} [DecidableEq α] [Infinite α] (a : ℕ) (s : ℝ) (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : IsMemoryProfile m) (σ : List α)
    (hce : s * (optMisses m σ : ℝ) < ((lruRun (augCap a s m) σ).misses : ℝ)) :
    ∃ (m' : ℕ → ℕ) (σ' : List α) (S' : ℕ → Finset α),
      IsReduced a s m' σ' S' ∧
      s * (policyMisses σ' S' σ'.length : ℝ) < (σ'.length : ℝ) := by sorry

end ChangingCache.UpperBound
