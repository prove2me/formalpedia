-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_4_5
-- name    : ChangingCache.UpperBound.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:04.430203+00:00
-- url     : https://prove2.me/theorems/e4012901-67f3-4101-a13c-c67d80e916c1
-- title:
--   Lemma 4.5 — Coupling held pages
-- statement:
--   Fix $(a,s)$ augmentation and a memory profile $m$. Consider two runs $A$ and $B$, each of LRU and a legal policy $P$ on $m$. Suppose that at some point
--   1. LRU has missed at least as often in $B$ as in $A$;
--   2. $P$ has missed equally often in $A$ and in $B$;
--   3. $P$ holds $q$ pages in both, at stack depths $d_1<\dots<d_q$ in $A$ and $e_1<\dots<e_q$ in $B$, with $d_i\le e_i$ for every $i$.
--
--   Let $A$ continue with a request sequence $\tau$ on which every miss of $P$ is cold. Then $B$ can continue with a sequence $\tau'$ of the same length, obtained from $\tau$ by renaming pages, served by a legal policy $P'$ that hits and misses exactly where $P$ does and has only cold misses, so that after every request
--   $$F^{B}_{LRU}\ \ge\ F^{A}_{LRU}.$$
--
--   The lemma is what allows a request that hits in both caches to be deleted: the depths of the pages $P$ holds are compared rank by rank, not page by page.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$, an integer number of pages → real $a$ and $s\ge1$, and LRU's capacity law is any `C : ℕ → ℕ` with $C(k)=a\cdot m(\lfloor k/s\rfloor)$ as real numbers for every $k$ (hypothesis `hC`); reason: Eq. (1) stated as an equation on integer page counts, with no rounding; it covers every $(a,s)$ for which Eq. (1) gives page counts on $m$, and nothing else
--   - encoding: new pages are always available (renamings to a new page) → the page type is `Infinite`; reason: the source's pages are unbounded identifiers; the statement asks for a sequence built from new pages, which a finite page type cannot supply
--   - encoding: runs $A$ and $B$ at some point; $A$ continues with $\tau$ → $A$ has served $\sigma_A$ with a policy $S_A$ legal on $\sigma_A\tau$; $B$ has served $\sigma_B$ with a legal policy $S_B$; the continuation of $B$ is $\sigma_B\tau'$ with a legal policy $S_B'$ that agrees with $S_B$ up to that point; reason: a continuation of a run is the run on the extended sequence that keeps its past
--   - reading: obtained from $\tau$ by renaming pages → $\tau'=f(\tau)$ entrywise for a map $f$ injective on the pages of $\tau$; reason: renaming relabels distinct pages by distinct names; the source's partner pairing is such a map, since a page keeps its partner and a page $P$ discards is never requested again
--   - encoding: depths $d_1<\dots<d_q$ and $e_1<\dots<e_q$ with $d_i\le e_i$ → the two sorted lists of stack depths of the held pages (`Multiset.sort`), with equal numbers of held pages and entrywise $\le$; reason: the held pages are distinct requested pages, so their depths are distinct and finite and the sorted lists are $d$ and $e$
--   - encoding: $P'$ hits and misses exactly where $P$ does and has only cold misses → stated for the requests of the continuation; reason: the past of $B$ is given, only the continuation is chosen
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 4.5, p. 10

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-- Throughout, `(a, s)` augmentation is encoded by LRU's capacity law `C`, an integer page count
with `C k = a · m(⌊k / s⌋)` (Eq. (1), p. 7) for real `a` and `s ≥ 1`.

**Lemma 4.5 (Coupling held pages)**, p. 10. Runs `A` and `B` each consist of LRU under `(a, s)`
augmentation and a legal policy on the same memory profile `m`. Run `A` has served `σA` with the
policy `SA`, legal on the whole sequence `σA ++ τ`; run `B` has served `σB` with the legal policy
`SB`. At that point LRU has missed at least as often in `B` as in `A`, the policy has missed equally
often in both, and it holds `q` pages in both, whose sorted stack depths `d₁ < ⋯ < d_q` in `A` and
`e₁ < ⋯ < e_q` in `B` satisfy `dᵢ ≤ eᵢ`. If every miss of the policy on the continuation `τ` of `A`
is cold, then `B` can continue with a sequence `τ'` of the same length obtained from `τ` by an
injective renaming of pages, served by a legal policy `SB'` that extends `SB`, hits and misses
exactly where `SA` does on the continuation and has only cold misses there, so that after every
request LRU has missed at least as often in `B` as in `A`. -/
theorem lemma_4_5 {α : Type*} [DecidableEq α] [Infinite α] (a s : ℝ) (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : IsMemoryProfile m)
    (C : ℕ → ℕ) (hC : ∀ k, (C k : ℝ) = a * (m ⌊(k : ℝ) / s⌋₊ : ℝ))
    (σA σB τ : List α) (SA SB : ℕ → Finset α)
    (hSA : IsLegal m (σA ++ τ) SA) (hSB : IsLegal m σB SB)
    (hlru : (lruRun C σA).misses ≤ (lruRun C σB).misses)
    (hpol : policyMisses (σA ++ τ) SA σA.length = policyMisses σB SB σB.length)
    (hq : (SA σA.length).card = (SB σB.length).card)
    (hdepth : ∀ (k : ℕ)
      (hkA : k < (Multiset.sort ((SA σA.length).val.map
          (stackDepth (lruRun C σA).stack)) (· ≤ ·)).length)
      (hkB : k < (Multiset.sort ((SB σB.length).val.map
          (stackDepth (lruRun C σB).stack)) (· ≤ ·)).length),
      (Multiset.sort ((SA σA.length).val.map
          (stackDepth (lruRun C σA).stack)) (· ≤ ·))[k] ≤
        (Multiset.sort ((SB σB.length).val.map
          (stackDepth (lruRun C σB).stack)) (· ≤ ·))[k])
    (hcold : ∀ t < τ.length, missB (σA ++ τ) SA (σA.length + t) = true →
      IsColdAt (σA ++ τ) (σA.length + t)) :
    ∃ (f : α → α) (SB' : ℕ → Finset α),
      Set.InjOn f {p | p ∈ τ} ∧
      IsLegal m (σB ++ τ.map f) SB' ∧
      (∀ i ≤ σB.length, SB' i = SB i) ∧
      (∀ t < τ.length, missB (σB ++ τ.map f) SB' (σB.length + t) =
        missB (σA ++ τ) SA (σA.length + t)) ∧
      (∀ t < τ.length, missB (σB ++ τ.map f) SB' (σB.length + t) = true →
        IsColdAt (σB ++ τ.map f) (σB.length + t)) ∧
      (∀ t ≤ τ.length, (lruRun C (σA ++ τ.take t)).misses ≤
        (lruRun C (σB ++ (τ.map f).take t)).misses) := by sorry

end ChangingCache.UpperBound
