-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_marking_competitive
-- name    : CompetitivePaging.Marking.marking_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:12:49.009247+00:00
-- url     : https://prove2.me/theorems/8bb522ba-3abc-46ab-b5be-46e9e677babf
-- title:
--   The marking algorithm is $2H_k$-competitive for paging (Theorem 1)
-- statement:
--   Let $M$ be a set of $n$ vertices with the uniform metric (distinct vertices at distance $1$), enumerated as $e(0), \dots, e(n-1)$, and let $1 \le k \le n$. Run the marking algorithm with $k$ servers, initially on $e(0), \dots, e(k-1)$, and let $C_M(\sigma)$ be its expected cost (expected number of server moves) on a finite request sequence $\sigma$. Let $\mathrm{OPT}(\sigma)$ be the optimal off-line cost of serving $\sigma$ with $k$ servers starting from the same initial configuration $C_0$. With $H_k = 1 + \frac12 + \dots + \frac1k$, there is a constant $a$ such that for every request sequence $\sigma$,
--   $$C_M(\sigma) \le 2H_k \cdot \mathrm{OPT}(\sigma) + a.$$
--
--   That is, the marking algorithm is a $2H_k$-competitive algorithm for the uniform $k$-server problem on $n$ vertices, which is the paging problem with a cache of $k$ pages and $n$ pages of address space. Since $H_k \approx \ln k$, this is exponentially better than the factor $k$ that no deterministic on-line algorithm can beat.
--
--   **Formalization Note.** The constant $a$ is quantified before $\sigma$. The paper compares with every algorithm $B$; the optimal off-line cost from $C_0$ is the infimum of these costs up to the choice of $B$'s starting configuration, which changes the cost by at most $k$ and is absorbed into $a$.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 3, Theorem 1; definition of c-competitive on p. 1

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- Theorem 1 (p. 3): the marking algorithm is a `2 H_k`-competitive algorithm for the
uniform `k`-server problem on `n` vertices. -/
theorem marking_competitive {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ a : ℝ, ∀ σ : List M,
      markingExpCost k (initVertices e hkn) σ
        ≤ 2 * (harmonic k : ℝ) * KServer.offlineCost (initConfig e hkn) σ + a := by sorry

end CompetitivePaging.Marking
