-- Prove2me | Theorems.Thm_AuctionMatroidInt_theorem_1_3
-- name    : AuctionMatroidInt.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:21.124243+00:00
-- url     : https://prove2.me/theorems/cc2f4934-885b-4f3e-9639-68335ad99bc1
-- title:
--   Theorem 1.3 — deterministic $(1-\varepsilon)$-approximation for weighted matroid intersection with $O(n\log r\,(\varepsilon^{-1}\log r+\varepsilon^{-2}))$ independence queries
-- statement:
--   There are an absolute constant $C$ and a deterministic algorithm $A$ that, given $n$, weights $w\in\mathbb R_{\ge0}^{n}$ and $\varepsilon$, and given access to two matroids $M_1=([n],\mathcal I_1)$ and $M_2=([n],\mathcal I_2)$ only through their independence oracles, has the following properties for every $n$, every $w\ge0$, every $0<\varepsilon<1$ and all matroids $M_1,M_2$ (loops allowed). Let $X$ be its output and $r$ the maximum size of a common independent set. Then
--
--   1. $X\in\mathcal I_1\cap\mathcal I_2$;
--   2. $w(X)\ge(1-\varepsilon)\,w(\mathrm{OPT}_w)$, where $\mathrm{OPT}_w$ is a maximum-weight common independent set;
--   3. the number of independence queries is at most
--   $$
--   C\,n\log(r+2)\Bigl(\frac{\log(r+2)}{\varepsilon}+\frac1{\varepsilon^{2}}\Bigr);
--   $$
--   4. if $w\equiv1$ (the unweighted problem), the number of independence queries is at most $C\,n\log(r+2)/\varepsilon^{2}$.
--
--   This is the first deterministic $(1-\varepsilon)$-approximation for weighted matroid intersection whose independence-query complexity is nearly linear in $n$ and polynomial in $1/\varepsilon$; for fixed $\varepsilon$ it uses $O(n\log^2 r)$ queries.
--
--   **Formalization Note** The ground set is `Fin n`; the algorithm is a `QueryTree (Fin 2) (Fin n) (Finset (Fin n))` chosen from $(n,w,\varepsilon)$ alone, and `queries` counts the oracle calls along the path the oracles select. $C$ is chosen before $n$, $\varepsilon$, $w$ and the matroids. No assumption of §2.1 (integral $1/\varepsilon$, positive weights, no loops, bounded ranks) is made: those are reductions the algorithm must perform within the budget.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: a deterministic algorithm using O(·) independence queries → ∃ C (absolute) and A : (n : ℕ) → (Fin n → ℝ) → ℝ → QueryTree (Fin 2) (Fin n) (Finset (Fin n)), with queries counted along the oracle's path; reason: the query model of §2.1: the matroids are seen only through their independence oracles and computation between queries is free; E = [n] is Fin n
--   - reading: log r → log(r + 2) (natural logarithm) in both query bounds; reason: log r ≤ 0 for r ≤ 1 while a correct algorithm must query once n ≥ 1; the two agree up to a factor 2 for r ≥ 2
--   - generalization: a (1−ε)-approximation algorithm; “in the unit-weight case … the number of independence queries improves to O(n log(r)/ε²)” → one algorithm A satisfying both query bounds; reason: the paper's proof uses the same Algorithm 4 for both; a single algorithm meeting both bounds gives each of the source's claims
--   - encoding: w(OPT_w) for a maximum-weight common independent set OPT_w → the bound against w(Y) for every common independent Y; reason: equivalent, since OPT_w maximizes w over common independent sets (which exist: ∅)
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Theorem 1.3, p.5 (PDF p.7); proof p.30 (PDF p.32)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_QueryTree
import Definitions.Def_AuctionMatroidInt_maxCommonCard

namespace AuctionMatroidInt

/-- **Theorem 1.3 (main result).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Theorem 1.3, p.5:
"Let 0 < ε < 1. For the weighted matroid intersection problem, there exists a deterministic
(1−ε)-approximation algorithm using O(n log r (ε⁻¹ log r + ε⁻²)) independence queries. In the
unit-weight case, that is, for the unweighted problem, the number of independence queries
improves to O(n log(r)/ε²)."

There are an absolute constant `C` and one deterministic independence-query algorithm `A`, which
receives `n`, the weights `w` and `ε` and accesses the two matroids only through their
independence oracles, such that for every `n`, every `w : [n] → ℝ_{≥0}`, every `0 < ε < 1` and every
two matroids `M₁ = ([n], I₁)`, `M₂ = ([n], I₂)` (loops allowed), the output `X` satisfies:
`X ∈ I₁ ∩ I₂`; `(1 − ε) w(Y) ≤ w(X)` for every common independent `Y`; the number of queries is at
most `C n log(r+2) (ε⁻¹ log(r+2) + ε⁻²)`; and, if `w ≡ 1`, at most `C n log(r+2)/ε²`. Here `r` is
the maximum size of a common independent set.

**Formalization Note.** The ground set `E = [n]` is `Fin n`. The algorithm is a `QueryTree`
(`0 ↦ M₁`, `1 ↦ M₂`) chosen from `(n, w, ε)` alone; computation between queries is free, and
`queries` counts the queries along the path the oracles select. `C` is chosen before `n`, `ε`,
`w` and the matroids. `log r` is read as `log(r + 2)` (natural log), since `log r ≤ 0` for
`r ≤ 1` while a correct algorithm must query once `n ≥ 1`. "w(X) ≥ (1 − ε) w(OPT_w)" is stated
against every common independent set. -/
theorem theorem_1_3 :
    ∃ C : ℝ, ∃ A : (n : ℕ) → (Fin n → ℝ) → ℝ → QueryTree (Fin 2) (Fin n) (Finset (Fin n)),
      ∀ (n : ℕ) (w : Fin n → ℝ) (ε : ℝ), (∀ e, 0 ≤ w e) → 0 < ε → ε < 1 →
      ∀ I : Fin 2 → Finset (Fin n) → Prop,
        CombOpt.MatroidPolytope.IsMatroid (I 0) → CombOpt.MatroidPolytope.IsMatroid (I 1) →
        I 0 ((A n w ε).run (indepOracle I)) ∧ I 1 ((A n w ε).run (indepOracle I)) ∧
        (∀ Y : Finset (Fin n), I 0 Y → I 1 Y →
          (1 - ε) * CombOpt.MatroidPolytope.weight w Y ≤
            CombOpt.MatroidPolytope.weight w ((A n w ε).run (indepOracle I))) ∧
        ((A n w ε).queries (indepOracle I) : ℝ) ≤
          C * n * Real.log (maxCommonCard (I 0) (I 1) + 2) *
            (Real.log (maxCommonCard (I 0) (I 1) + 2) / ε + 1 / ε ^ 2) ∧
        ((∀ e, w e = 1) → ((A n w ε).queries (indepOracle I) : ℝ) ≤
          C * n * Real.log (maxCommonCard (I 0) (I 1) + 2) / ε ^ 2) := by sorry

end AuctionMatroidInt
