-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_no_competitive_below_harmonic
-- name    : CompetitivePaging.LowerBound.no_competitive_below_harmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:21:22.629704+00:00
-- url     : https://prove2.me/theorems/f751c37c-51ca-4742-8bf5-563ed9b835b2
-- title:
--   Corollary 5: no randomized paging algorithm with $k$ servers is $c$-competitive for $c < H_k$
-- statement:
--   Let $1\le k\le n-1$ and let $M$ be a set of $n$ vertices with the uniform metric: any two distinct vertices are at distance $1$. Consider the uniform $k$-server problem on $M$, that is, paging with a cache of $k$ pages out of $n$. Let $H_k=1+\tfrac12+\dots+\tfrac1k$ be the $k$-th harmonic number.
--
--   For every randomized on-line algorithm $A$ with $k$ servers on $M$, every initial configuration $C_0$ and every real $c<H_k$, the algorithm $A$ is **not** $c$-competitive from $C_0$: there is no constant $a$ such that for every request sequence $\sigma$
--
--   $$
--   C_A(\sigma)\ \le\ c\cdot \mathrm{OPT}_{C_0}(\sigma)+a ,
--   $$
--
--   where $C_A(\sigma)$ is the expected cost of $A$ on $\sigma$ against an oblivious adversary and $\mathrm{OPT}_{C_0}(\sigma)$ is the optimal off-line cost of serving $\sigma$ from $C_0$.
--
--   This is the lower bound matching, up to the factor $2$, the $2H_k$ upper bound for the marking algorithm, and exactly for $k=n-1$.
--
--   **Formalization Note** Randomized algorithms and competitiveness are the published `KServer.RandomizedAlgorithm` and `IsCompetitiveFrom` (every drawn deterministic algorithm starts at $C_0$; the right-hand side is clamped at $0$ by `ENNReal.ofReal`, which only weakens the property being refuted). No laziness or injectivity is assumed of $A$ or $C_0$. The uniform metric is a hypothesis on an abstract space $M$ with $n$ points; $H_k$ is Mathlib's `harmonic k` cast to $\mathbb R$.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 8, Corollary 5

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

theorem no_competitive_below_harmonic (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (M : Type)
    [MetricSpace M] (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm k M) (C₀ : KServer.Config k M) (c : ℝ)
    (hc : c < (harmonic k : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by sorry

end CompetitivePaging.LowerBound
