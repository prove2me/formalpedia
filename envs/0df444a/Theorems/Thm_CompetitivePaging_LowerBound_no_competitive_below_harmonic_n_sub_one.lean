-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_no_competitive_below_harmonic_n_sub_one
-- name    : CompetitivePaging.LowerBound.no_competitive_below_harmonic_n_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:20:56.134769+00:00
-- url     : https://prove2.me/theorems/7559513d-e3c3-4809-ad90-4436a1aefaa5
-- title:
--   Theorem 4: no randomized $(n-1)$-server algorithm on $n$ uniform vertices is $c$-competitive for $c < H_{n-1}$
-- statement:
--   Let $n\ge2$ and let $M$ be a set of $n$ vertices with the uniform metric: any two distinct vertices are at distance $1$. Consider the uniform $(n-1)$-server problem on $M$ (paging with a cache of $n-1$ pages and $n$ pages in total). Let $H_{n-1}=1+\tfrac12+\dots+\tfrac1{n-1}$ be the $(n-1)$-st harmonic number.
--
--   For every randomized on-line algorithm $A$ with $n-1$ servers on $M$, every initial configuration $C_0$ and every real $c<H_{n-1}$, the algorithm $A$ is **not** $c$-competitive from $C_0$: there is no constant $a$ such that for every request sequence $\sigma$
--
--   $$
--   C_A(\sigma)\ \le\ c\cdot \mathrm{OPT}_{C_0}(\sigma)+a ,
--   $$
--
--   where $C_A(\sigma)$ is the expected cost of $A$ on $\sigma$ (against an oblivious adversary) and $\mathrm{OPT}_{C_0}(\sigma)$ the optimal off-line cost of serving $\sigma$ from $C_0$.
--
--   Together with the marking algorithm's upper bound this shows that the marking algorithm is strongly competitive when $k=n-1$.
--
--   **Formalization Note** Competitiveness is the published `KServer.RandomizedAlgorithm.IsCompetitiveFrom`: every drawn deterministic algorithm starts at $C_0$, and the right-hand side is clamped at $0$ (`ENNReal.ofReal`). The clamp only weakens the property being refuted, so the statement is at least as strong as the paper's. The uniform metric is a hypothesis on an abstract space $M$ with $n$ points.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, Theorem 4 (proof pp. 7–8)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

theorem no_competitive_below_harmonic_n_sub_one (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M]
    (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm (n - 1) M) (C₀ : KServer.Config (n - 1) M) (c : ℝ)
    (hc : c < (harmonic (n - 1) : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by sorry

end CompetitivePaging.LowerBound
