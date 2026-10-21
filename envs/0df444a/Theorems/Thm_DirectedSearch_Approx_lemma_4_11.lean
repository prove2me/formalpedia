-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_11
-- name    : DirectedSearch.Approx.lemma_4_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:00.428987+00:00
-- url     : https://prove2.me/theorems/d8c731f4-7501-4ad8-b11d-794b1be298e5
-- title:
--   Lemma 4.11, p. 25 — in an equilibrium with f = f*, τ_w_i ≤ τ̂_w_i
-- statement:
--   In the setting of Lemma 4.10, let $\hat\tau_{w_i}$ be the idealized thresholds and let $(\tau_m,(\tau_{w_i})_i)$ be an equilibrium where $f_{mw_i}=f^*_{mw_i}$, i.e. nonnegative thresholds solving (12). Then
--   $$\tau_{w_i}\le\hat\tau_{w_i}\qquad\text{for all } i.$$
--
--   With Lemma 4.12 this pins down $\max(\tau_m,\tau_{w_i})=\max(\tau_m,\hat\tau_{w_i})$ in such equilibria.
--
--   **Formalization Note.** "Equilibrium where $f_{mw_i}=f^*_{mw_i}$" is encoded by the fixed-point equations (12) with nonnegative thresholds, as on the page, not by a full solution of (6a)–(6f).
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 25, Lemma 4.11

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Definitions.Def_DirectedSearch_Approx_Star

namespace DirectedSearch.Approx
theorem lemma_4_11 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m)
    (β : M → W → ℝ) (hβ : LPFeasible mk β) {n : ℕ} (ws : Fin n → W) (hws : Function.Injective ws)
    (hsat : ∀ i : Fin n, i.val + 1 < n → β m (ws i) = mk.αW (ws i))
    (th : Fin n → ℝ) (hth : ∀ i, IsIdealThreshold mk β m ws i (th i))
    (τm : ℝ) (τw : Fin n → ℝ) (heq : IsStarEquilibrium mk β m ws τm τw) :
    ∀ i, τw i ≤ th i := by sorry
end DirectedSearch.Approx
