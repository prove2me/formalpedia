-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_threshold_profile_clearing
-- name    : FlowAllocGames.StrongEq.threshold_profile_clearing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:22.628335+00:00
-- url     : https://prove2.me/theorems/ba59df4c-ec15-41a7-b6bc-c948422bca2a
-- title:
--   Proof of Theorem 9, p. 23 — with thresholds f*, the threshold-ranking profile is unit-ranking with clearing state f*
-- statement:
--   Let $f^*$ be an optimal (integral) circulation of the circulation network $G'$ of a flow allocation game. Let every node $v$ choose an arbitrary permutation $\pi_v$ of $E^+(v)$, and set the thresholds $\tau_e = f^*_e$ for every edge $e$ of $G$. Let $\mathbf a^*$ be the resulting threshold-ranking profile. Then
--
--   1. $\mathbf a^*$ is a unit-ranking profile, and
--   2. the clearing state of $\mathbf a^*$ is the restriction of $f^*$ to the edges of $G$:
--   $$\hat f_e(\mathbf a^*) = f^*_e \qquad \text{for every } e \in E.$$
--
--   This is the profile $\mathbf a^*$ that the proof of Theorem 9 shows to be a strong equilibrium; its threshold-ranking description is the compact representation behind the polynomial-space claim of Theorem 9.
--
--   **Formalization Note.** The permutations $\pi_v$ are given by one ranking $\mathrm{rank} : E \to \mathbb N$ that is injective on each $E^+(v)$; this injectivity is a hypothesis. The page asserts the second conclusion ("It is easy to see that in $\mathbf a^*$, the optimal circulation $f^*$ corresponds to the clearing state") and states the first in general ("They constitute a special class of unit-ranking strategies").
-- source:
--   arXiv:1908.01714v3, proof of Theorem 9, p. 23 (threshold-ranking strategies and the choice of a*)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model
import Definitions.Def_FlowAllocGames_StrongEq_Threshold

namespace FlowAllocGames.StrongEq

open Finset

/-- Proof of Theorem 9 (arXiv:1908.01714v3, p. 23): with an arbitrary ranking `π_v` of every
`E⁺(v)` and thresholds `τ_e = f*_e` taken from an optimal circulation `f*` of `G′`, the
threshold-ranking profile `a*` is a unit-ranking profile whose clearing state is `f*`. -/
theorem threshold_profile_clearing {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x) (rank : E → ℕ)
    (hrank : ∀ e e', G.tail e = G.tail e' → rank e = rank e' → e = e') :
    G.IsUnitRanking (G.thresholdProfile rank x.g) ∧
      G.clearingState (G.thresholdProfile rank x.g) = x.g := by sorry

end FlowAllocGames.StrongEq
