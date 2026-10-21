-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_10
-- name    : DirectedSearch.Approx.lemma_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:04.956073+00:00
-- url     : https://prove2.me/theorems/08bd2efe-8b42-4e12-9743-847ddc3a7020
-- title:
--   Lemma 4.10, p. 25 — τ̂_w_i = ρ_mw_i for i < n and τ̂_w_n ≤ ρ_mw_n
-- statement:
--   Consider a market satisfying the standing assumptions with $\mathcal M=\{m\}$, an LP-feasible $\beta$ and distinct types $w_1,\dots,w_n$ with $\beta_{mw_i}=\alpha_{w_i}$ for every $i<n$ (as in Lemma 4.9). Let $\hat\tau_{w_i}$ be an idealized threshold of $w_i$. Then
--   $$\hat\tau_{w_i}=\rho_{mw_i}\ \ \text{if } i<n,\qquad \hat\tau_{w_n}\le\rho_{mw_n}.$$
--
--   The idealized thresholds therefore never fall below what the first best would choose for the saturated types.
--
--   **Formalization Note.** Indices are 0-based: "$i<n$" is `i.val + 1 < n` and "$i=n$" is `i.val + 1 = n`. The ordering of the $\rho_{mw_i}$ from Lemma 4.9 is not assumed; the proof does not use it.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 25, Lemma 4.10

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Definitions.Def_DirectedSearch_Approx_Star

namespace DirectedSearch.Approx
theorem lemma_4_10 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m)
    (β : M → W → ℝ) (hβ : LPFeasible mk β) {n : ℕ} (ws : Fin n → W) (hws : Function.Injective ws)
    (hsat : ∀ i : Fin n, i.val + 1 < n → β m (ws i) = mk.αW (ws i))
    (i : Fin n) (t : ℝ) (ht : IsIdealThreshold mk β m ws i t) :
    (i.val + 1 < n → t = rho mk m (ws i)) ∧ (i.val + 1 = n → t ≤ rho mk m (ws i)) := by sorry
end DirectedSearch.Approx
