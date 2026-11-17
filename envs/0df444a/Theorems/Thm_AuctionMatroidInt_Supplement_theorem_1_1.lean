-- Prove2me | Theorems.Thm_AuctionMatroidInt_Supplement_theorem_1_1
-- name    : AuctionMatroidInt.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:22:47.539505+00:00
-- url     : https://prove2.me/theorems/9a47a05d-c9d4-4ba3-a929-7efad1ce438b
-- title:
--   Theorem 1.1 — deterministic $(1-\varepsilon)$-approximation for unweighted matroid intersection with $O(n\log n/\varepsilon)$ rank queries
-- statement:
--   There are an absolute constant $C$ and a deterministic algorithm $A$ that, given $n$ and $\varepsilon$, and given access to two matroids $M_1=([n],\mathcal I_1)$ and $M_2=([n],\mathcal I_2)$ only through their rank oracles, has the following properties for every $n$, every $0<\varepsilon<1$ and all matroids $M_1,M_2$ (loops allowed). Let $X$ be its output and $r$ the maximum size of a common independent set. Then
--
--   1. $X\in\mathcal I_1\cap\mathcal I_2$;
--   2. $|X|\ge(1-\varepsilon)\,r$;
--   3. the number of rank queries is at most
--   $$
--   C\,\frac{n\log(n+2)}{\varepsilon}.
--   $$
--
--   This is the auction-based warm-up of the paper; the same rank-query bound was obtained earlier by augmenting-path methods, and the auction approach extends to the weighted problem (Theorem 1.2).
--
--   **Formalization Note** The algorithm is a `RankQueryTree (Fin 2) (Fin n) (Finset (Fin n))` chosen from $(n,\varepsilon)$ alone; one rank query counts once. $C$ is chosen before $n$, $\varepsilon$ and the matroids. No assumption of §2.1 ($1/\varepsilon$ an integer, $1/\varepsilon\le n+1$, no loops, bounded ranks) is made.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset (Fin n) → Prop (ground set = Fin n); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: a deterministic algorithm using O(n log(n)/ε) rank queries → ∃ C (absolute) and A : (n : ℕ) → ℝ → RankQueryTree (Fin 2) (Fin n) (Finset (Fin n)), with queries counted along the oracle's path and bounded by C·n·log(n+2)/ε; reason: the rank-oracle model of §2.1: the matroids are seen only through rank_M(X), one answer per query, computation between queries free; E = [n] is Fin n
--   - reading: log n → log(n + 2) (natural logarithm); reason: log n ≤ 0 for n ≤ 1, while the bound must allow queries once n ≥ 1; the two agree up to a factor 2 for n ≥ 2
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Theorem 1.1, p.4 (PDF p.6); restated p.15 (PDF p.17), proof §3.3

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_maxCommonCard
import Definitions.Def_AuctionMatroidInt_Supplement_RankQueryTree

namespace AuctionMatroidInt.Supplement

/-- **Theorem 1.1 (unweighted, rank queries).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Theorem 1.1, p.4 (PDF p.6),
restated p.15: "Let 0 < ε < 1. For the unweighted matroid intersection problem, there exists a
deterministic (1 − ε)-approximation algorithm using O(n log(n)/ε) rank queries."

There are an absolute constant `C` and one deterministic rank-query algorithm `A`, which receives
`n` and `ε` and accesses the two matroids only through their rank oracles, such that for every
`n`, every `0 < ε < 1` and all matroids `M₁ = ([n], I₁)`, `M₂ = ([n], I₂)` (loops allowed), the
output `X` is common independent, `(1 − ε) r ≤ |X|` where `r` is the maximum size of a common
independent set, and the number of rank queries is at most `C n log(n+2)/ε`.

**Formalization Note.** The ground set `E = [n]` is `Fin n`. The algorithm is a
`RankQueryTree (Fin 2) (Fin n) (Finset (Fin n))` (`0 ↦ M₁`, `1 ↦ M₂`) chosen from `(n, ε)`
alone; one rank query is one query. `C` is chosen before `n`, `ε` and the matroids. `log n` is
read as `log(n + 2)` (natural log), since `log n ≤ 0` for `n ≤ 1`. No assumption of §2.1
(`1/ε` an integer, `1/ε ≤ n + 1`, no loops, bounded ranks) is made. -/
theorem theorem_1_1 :
    ∃ C : ℝ, ∃ A : (n : ℕ) → ℝ → RankQueryTree (Fin 2) (Fin n) (Finset (Fin n)),
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ I : Fin 2 → Finset (Fin n) → Prop,
        CombOpt.MatroidPolytope.IsMatroid (I 0) → CombOpt.MatroidPolytope.IsMatroid (I 1) →
        I 0 ((A n ε).run (rankOracle I)) ∧ I 1 ((A n ε).run (rankOracle I)) ∧
        (1 - ε) * (maxCommonCard (I 0) (I 1) : ℝ) ≤ ((A n ε).run (rankOracle I)).card ∧
        ((A n ε).queries (rankOracle I) : ℝ) ≤ C * n * Real.log (n + 2) / ε := by sorry

end AuctionMatroidInt.Supplement
