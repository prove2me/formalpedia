-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_12
-- name    : DirectedSearch.Approx.lemma_4_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:11.504852+00:00
-- url     : https://prove2.me/theorems/a6667948-afe5-407f-a465-2efc31f9dd53
-- title:
--   Lemma 4.12, p. 26 — in an equilibrium with f = f*, max(τ_m, τ_w_i) ≥ τ̂_w_i
-- statement:
--   In the setting of Lemma 4.10, let $\hat\tau_{w_i}$ be the idealized thresholds and let $(\tau_m,(\tau_{w_i})_i)$ be an equilibrium where $f_{mw_i}=f^*_{mw_i}$, i.e. nonnegative thresholds solving (12). Then
--   $$\max(\tau_m,\tau_{w_i})\ge\hat\tau_{w_i}\qquad\text{for all } i.$$
--
--   With Lemma 4.10 this guarantees that no saturated type $w_i$ matches more than in the first best.
--
--   **Formalization Note.** The equilibrium is encoded as in Lemma 4.11.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 26, Lemma 4.12

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Definitions.Def_DirectedSearch_Approx_Star

namespace DirectedSearch.Approx
theorem lemma_4_12 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m)
    (β : M → W → ℝ) (hβ : LPFeasible mk β) {n : ℕ} (ws : Fin n → W) (hws : Function.Injective ws)
    (hsat : ∀ i : Fin n, i.val + 1 < n → β m (ws i) = mk.αW (ws i))
    (th : Fin n → ℝ) (hth : ∀ i, IsIdealThreshold mk β m ws i (th i))
    (τm : ℝ) (τw : Fin n → ℝ) (heq : IsStarEquilibrium mk β m ws τm τw) :
    ∀ i, th i ≤ max τm (τw i) := by sorry
end DirectedSearch.Approx
