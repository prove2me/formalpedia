-- Prove2me | Theorems.Thm_DirectedSearch_Approx_ideal_threshold_exists_unique
-- name    : DirectedSearch.Approx.ideal_threshold_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:00.776622+00:00
-- url     : https://prove2.me/theorems/8b8bae81-e3a8-40d0-91be-b430a5dcda08
-- title:
--   §4.2.2, p. 25 — the idealized threshold τ̂_w_i exists and is unique
-- statement:
--   Consider a market satisfying the standing assumptions with $\mathcal M=\{m\}$, an LP-feasible $\beta$ and distinct types $w_1,\dots,w_n$. For every $i$ there is exactly one $\hat\tau\ge0$ with
--   $$\hat\tau=\frac1{\alpha_{w_i}}f^*_{mw_i}\int_{\hat\tau}^\infty u\,dF_{mw_i},\qquad f^*_{mw_i}=\frac{\beta_{mw_i}}{\delta+\int_{\rho_{mw_i}}^\infty dF_{mw_i}}.$$
--
--   This is the paper's remark that the idealized thresholds are well defined: the left-hand side increases and the right-hand side decreases in $\hat\tau$.
--
--   **Formalization Note.** Existence and uniqueness are over $[0,\infty)$, where the right-hand side is decreasing; on all of $\mathbb R$ a second, negative root can exist. Only $\beta\ge0$ is used from LP feasibility.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 25, §4.2.2, parenthetical after the definition of τ̂_w_i

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Definitions.Def_DirectedSearch_Approx_Star

namespace DirectedSearch.Approx
theorem ideal_threshold_exists_unique {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m)
    (β : M → W → ℝ) (hβ : LPFeasible mk β) {n : ℕ} (ws : Fin n → W) (hws : Function.Injective ws)
    (i : Fin n) :
    ∃! t : ℝ, IsIdealThreshold mk β m ws i t := by sorry
end DirectedSearch.Approx
