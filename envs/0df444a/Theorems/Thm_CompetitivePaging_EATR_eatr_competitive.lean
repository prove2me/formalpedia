-- Prove2me | Theorems.Thm_CompetitivePaging_EATR_eatr_competitive
-- name    : CompetitivePaging.EATR.eatr_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:16:56.272967+00:00
-- url     : https://prove2.me/theorems/f18909f6-624b-4166-8b39-f5e826f0ece4
-- title:
--   Theorem 3 — Algorithm EATR is $3/2$-competitive for the uniform 2-server problem
-- statement:
--   Let $M$ be a set of $n\ge 2$ vertices, enumerated as $e(0),\dots,e(n-1)$, carrying the uniform metric: any two distinct vertices are at distance $1$. Run algorithm EATR with its two servers initially on the vertices $e(0)$ and $e(1)$ (the paper's vertices $1$ and $2$), and let $C_{\mathrm{EATR}}(\sigma)$ be its expected cost on a request sequence $\sigma$. Let $\mathrm{OPT}(\sigma)$ be the optimal off-line cost of serving $\sigma$ with two servers starting on $e(0)$ and $e(1)$. Then there is a constant $c$ such that for every request sequence $\sigma$,
--   $$C_{\mathrm{EATR}}(\sigma)\ \le\ \frac32\,\mathrm{OPT}(\sigma)+c.$$
--
--   Since every deterministic algorithm $B$, on-line or off-line, pays at least $\mathrm{OPT}(\sigma)$ on $\sigma$ (up to a constant for another starting position), this is the paper's statement that EATR is $3/2$-competitive. As $3/2=H_2=1+\tfrac12$, the second harmonic number, and the paper shows that no randomized paging algorithm is better than $H_k$-competitive, EATR is strongly competitive for two servers.
--
--   **Formalization Note** $\mathrm{OPT}$ is `KServer.offlineCost` from the published `KServer` model, the infimum of the movement cost over all schedules that serve $\sigma$ from the configuration $(e(0),e(1))$. The constant $c$ is quantified before $\sigma$. The uniform metric is a hypothesis on an abstract metric space, not the metric of `Fin n`.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, Theorem 3 (definition of c-competitive: p. 1)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem eatr_competitive {n : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hn : 2 ≤ n) (hunif : ∀ x y : M, x ≠ y → dist x y = 1) :
    ∃ c : ℝ, ∀ σ : List M,
      eatrExpCost (e ⟨0, by omega⟩) (e ⟨1, hn⟩) σ
        ≤ (3 / 2 : ℝ) * KServer.offlineCost ![e ⟨0, by omega⟩, e ⟨1, hn⟩] σ + c := by sorry

end CompetitivePaging.EATR
