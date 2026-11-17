-- Prove2me | Theorems.Thm_AuctionMatroidInt_Supplement_theorem_1_2
-- name    : AuctionMatroidInt.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:23:24.296347+00:00
-- url     : https://prove2.me/theorems/051ae57c-1833-4d96-8639-07a4c66cbb27
-- title:
--   Theorem 1.2 — deterministic $(1-\varepsilon)$-approximation for weighted matroid intersection with $O(n\log n/\varepsilon)$ rank queries
-- statement:
--   There are an absolute constant $C$ and a deterministic algorithm $A$ that, given $n$, weights $w\in\mathbb R_{\ge0}^{n}$ and $\varepsilon$, and given access to two matroids $M_1=([n],\mathcal I_1)$ and $M_2=([n],\mathcal I_2)$ only through their rank oracles, has the following properties for every $n$, every $w\ge0$, every $0<\varepsilon<1$ and all matroids $M_1,M_2$ (loops allowed). Let $X$ be its output. Then
--
--   1. $X\in\mathcal I_1\cap\mathcal I_2$;
--   2. $w(X)\ge(1-\varepsilon)\,w(\mathrm{OPT}_w)$, where $\mathrm{OPT}_w$ is a maximum-weight common independent set;
--   3. the number of rank queries is at most
--   $$
--   C\,\frac{n\log(n+2)}{\varepsilon},
--   $$
--   independently of the weights.
--
--   This is the first $(1-\varepsilon)$-approximation for weighted matroid intersection whose rank-query complexity is nearly linear in $n$ and polynomial in $1/\varepsilon$; it matches the best known bound for the unweighted problem.
--
--   **Formalization Note** The algorithm is a `RankQueryTree (Fin 2) (Fin n) (Finset (Fin n))` chosen from $(n,w,\varepsilon)$ alone; one rank query counts once. $C$ is chosen before $n$, $\varepsilon$, $w$ and the matroids. Weights are arbitrary nonnegative reals (zeros allowed); no assumption of §2.1 is made.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset (Fin n) → Prop (ground set = Fin n); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: a deterministic algorithm using O(n log(n)/ε) rank queries → ∃ C (absolute) and A : (n : ℕ) → (Fin n → ℝ) → ℝ → RankQueryTree (Fin 2) (Fin n) (Finset (Fin n)), with queries counted along the oracle's path and bounded by C·n·log(n+2)/ε; reason: the rank-oracle model of §2.1: the matroids are seen only through rank_M(X), one answer per query, computation between queries free; E = [n] is Fin n
--   - reading: log n → log(n + 2) (natural logarithm); reason: log n ≤ 0 for n ≤ 1, while the bound must allow queries once n ≥ 1; the two agree up to a factor 2 for n ≥ 2
--   - encoding: w(OPT_w) for a maximum-weight common independent set OPT_w → the bound against w(Y) for every common independent Y; reason: equivalent, since OPT_w maximizes w over common independent sets (which exist: ∅)
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Theorem 1.2, p.5 (PDF p.7); restated p.18 (PDF p.20), proof §4

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_Supplement_RankQueryTree

namespace AuctionMatroidInt.Supplement

/-- **Theorem 1.2 (weighted, rank queries).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Theorem 1.2, p.5 (PDF p.7),
restated p.18: "Let 0 < ε < 1. For the weighted matroid intersection problem, there exists a
deterministic (1 − ε)-approximation algorithm using O(n log(n)/ε) rank queries."

There are an absolute constant `C` and one deterministic rank-query algorithm `A`, which receives
`n`, the weights `w` and `ε` and accesses the two matroids only through their rank oracles, such
that for every `n`, every `w : [n] → ℝ_{≥0}`, every `0 < ε < 1` and all matroids
`M₁ = ([n], I₁)`, `M₂ = ([n], I₂)` (loops allowed), the output `X` is common independent,
`(1 − ε) w(Y) ≤ w(X)` for every common independent `Y`, and the number of rank queries is at most
`C n log(n+2)/ε`, independently of `w`.

**Formalization Note.** The ground set `E = [n]` is `Fin n`. The algorithm is a
`RankQueryTree (Fin 2) (Fin n) (Finset (Fin n))` (`0 ↦ M₁`, `1 ↦ M₂`) chosen from `(n, w, ε)`
alone; one rank query is one query. `C` is chosen before `n`, `ε`, `w` and the matroids. `log n`
is read as `log(n + 2)` (natural log). Weights are arbitrary nonnegative reals (zeros allowed);
no assumption of §2.1 (`1/ε` an integer, positive weights, no loops, bounded ranks) is made.
"w(X) ≥ (1 − ε) w(OPT_w)" is stated against every common independent set. -/
theorem theorem_1_2 :
    ∃ C : ℝ, ∃ A : (n : ℕ) → (Fin n → ℝ) → ℝ → RankQueryTree (Fin 2) (Fin n) (Finset (Fin n)),
      ∀ (n : ℕ) (w : Fin n → ℝ) (ε : ℝ), (∀ e, 0 ≤ w e) → 0 < ε → ε < 1 →
      ∀ I : Fin 2 → Finset (Fin n) → Prop,
        CombOpt.MatroidPolytope.IsMatroid (I 0) → CombOpt.MatroidPolytope.IsMatroid (I 1) →
        I 0 ((A n w ε).run (rankOracle I)) ∧ I 1 ((A n w ε).run (rankOracle I)) ∧
        (∀ Y : Finset (Fin n), I 0 Y → I 1 Y →
          (1 - ε) * CombOpt.MatroidPolytope.weight w Y ≤
            CombOpt.MatroidPolytope.weight w ((A n w ε).run (rankOracle I))) ∧
        ((A n w ε).queries (rankOracle I) : ℝ) ≤ C * n * Real.log (n + 2) / ε := by sorry

end AuctionMatroidInt.Supplement
