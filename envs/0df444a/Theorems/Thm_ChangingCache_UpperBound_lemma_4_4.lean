-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_4_4
-- name    : ChangingCache.UpperBound.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:56.933349+00:00
-- url     : https://prove2.me/theorems/3494b0c8-558c-44e8-829e-d2dfd5c1e5ec
-- title:
--   Lemma 4.4 — Dominating Stack Depths
-- statement:
--   Fix $(a,s)$ augmentation and a memory profile $m$, and let LRU have capacity $C(k)=a\,m(\lfloor k/s\rfloor)$ after $k$ misses. Consider two runs $A$ and $B$ of LRU on $m$, each starting from some point of a run of LRU on $m$ and each continuing with its own request sequence of length $\ell$. Suppose that $A$ begins with at least as many misses as $B$. Call an index $i$ **tied** if $A$ and $B$ have equal miss counts just before their $i$-th requests, and suppose that at every tied index the page $A$ requests is at least as deep in $A$'s stack as the page $B$ requests is in $B$'s. Then after every index $0\le i\le\ell$,
--   $$F_A(i)\ \ge\ F_B(i).$$
--
--   This is the stack-depth comparison behind every reduction of Section 4: editing a request sequence so that requests land at least as deep in LRU's stack can only add LRU misses, whatever the profile.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: $(a,s)$ augmentation, $C(k)=a\,m(\lfloor k/s\rfloor)$ for every real $s\ge 1$, an integer number of pages → real $a$ and $s\ge1$, and LRU's capacity law is any `C : ℕ → ℕ` with $C(k)=a\cdot m(\lfloor k/s\rfloor)$ as real numbers for every $k$ (hypothesis `hC`); reason: Eq. (1) stated as an equation on integer page counts, with no rounding; it covers every $(a,s)$ for which Eq. (1) gives page counts on $m$, and nothing else
--   - encoding: each run starts from some point of a run of LRU on $m$ → run $A$ (resp. $B$) starts from the state of LRU after the requests $\rho_A$ (resp. $\rho_B$) from the empty cache, i.e. it serves $\rho_A$ followed by $\tau_A$; reason: the points of runs of LRU on $m$ are exactly these states
--   - encoding: stack depth, $\infty$ for a page never requested → `stackDepth`, valued in `ℕ∞` with `⊤` for a page not in the stack; reason: Lean convention; same order
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 4.4, p. 8

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-- Throughout, `(a, s)` augmentation is encoded by LRU's capacity law `C`, an integer page count
with `C k = a · m(⌊k / s⌋)` (Eq. (1), p. 7) for real `a` and `s ≥ 1`.

**Lemma 4.4 (Dominating Stack Depths)**, p. 8. Two runs `A` and `B` of LRU under `(a, s)`
augmentation on the same memory profile `m` start from points of runs of LRU on `m` (the states
reached after the requests `ρA`, resp. `ρB`, from the empty cache), with `A` having at least as many
misses as `B`. Each continues with its own sequence (`τA`, `τB`) of the same length `ℓ`. If at every
tied index `i` (equal miss counts just before the `i`-th continuation request) the page `A`
requests is at least as deep in `A`'s stack as the page `B` requests is in `B`'s, then after every
index `A` has at least as many misses as `B`. -/
theorem lemma_4_4 {α : Type*} [DecidableEq α] (a s : ℝ) (hs : 1 ≤ s) (m : ℕ → ℕ)
    (hm : IsMemoryProfile m)
    (C : ℕ → ℕ) (hC : ∀ k, (C k : ℝ) = a * (m ⌊(k : ℝ) / s⌋₊ : ℝ))
    (ρA ρB τA τB : List α) (hlen : τA.length = τB.length)
    (hstart : (lruRun C ρB).misses ≤ (lruRun C ρA).misses)
    (htied : ∀ (i : ℕ) (hA : i < τA.length) (hB : i < τB.length),
      (lruRun C (ρA ++ τA.take i)).misses =
          (lruRun C (ρB ++ τB.take i)).misses →
        stackDepth (lruRun C (ρB ++ τB.take i)).stack τB[i] ≤
          stackDepth (lruRun C (ρA ++ τA.take i)).stack τA[i]) :
    ∀ i ≤ τA.length,
      (lruRun C (ρB ++ τB.take i)).misses ≤
        (lruRun C (ρA ++ τA.take i)).misses := by sorry

end ChangingCache.UpperBound
