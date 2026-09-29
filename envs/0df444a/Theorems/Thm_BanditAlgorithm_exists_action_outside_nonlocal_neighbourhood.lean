-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_action_outside_nonlocal_neighbourhood
-- name    : BanditAlgorithm.exists_action_outside_nonlocal_neighbourhood
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:13:05.882128+00:00
-- url     : https://prove2.me/theorems/6f26d5d0-8691-4aca-be35-1f35537c969b
-- title:
--   A non-locally observable edge has an action outside its neighbourhood
-- statement:
--   Let $G$ be a finite partial-monitoring game. If $G$ is globally observable but not locally observable, then there are neighbouring actions $a,b$ such that their loss difference has a global feedback estimator, while at least one action $c$ lies outside the neighbourhood $N_{ab}$:
--
--   $$
--   a\sim b,\qquad \mathcal E^{\mathrm{glo}}_{ab}\ne\varnothing,\qquad \exists c\notin N_{ab}.
--   $$
--
--   This isolates the first logical consequence used in the hard-game lower-bound construction: the failure of local observability occurs on a concrete edge, and global observability still supplies an estimator on that edge.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed pp. 488–489, especially Eq. (37.5).

import Definitions.Def_PartialMonitoringGame

theorem BanditAlgorithm.exists_action_outside_nonlocal_neighbourhood
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (hglob : GloballyObservable G) (hloc : ¬ LocallyObservable G) :
    ∃ a b : Fin k, NeighbouringActions G a b ∧
      (∃ f : Fin k × 𝕊 → ℝ, IsGlobalLossEstimator G a b f) ∧
      ∃ c : Fin k, c ∉ pmNeighbourhood G a b := by sorry
