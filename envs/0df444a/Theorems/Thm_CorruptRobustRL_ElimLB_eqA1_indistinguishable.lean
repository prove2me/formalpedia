-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_eqA1_indistinguishable
-- name    : CorruptRobustRL.ElimLB.eqA1_indistinguishable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:02.962493+00:00
-- url     : https://prove2.me/theorems/893c7201-f8b9-4c64-8e50-ae75e83f9df8
-- title:
--   (A.1), p. 38 — until the combination (1,…,1) is played, ℳ and ℳ₀ are indistinguishable: P^ℳ[ℬ ∩ ⋂_k (ℰ^combi_k)^c] = P^{ℳ₀}[ℬ ∩ ⋂_k (ℰ^combi_k)^c]
-- statement:
--   Let $H\ge1$, $A\ge2$, let $\mathcal M,\mathcal M_0$ be the combination-lock instances, and run any uniformly action-eliminating algorithm for $K$ episodes. For every event $\mathcal B$ of the observed history after $K$ episodes,
--
--   $$
--   \mathbb P^{\mathcal M}\Bigl[\mathcal B\cap\bigcap_{k=1}^K(\mathcal E^{\mathrm{combi}}_k)^c\Bigr]=\mathbb P^{\mathcal M_0}\Bigl[\mathcal B\cap\bigcap_{k=1}^K(\mathcal E^{\mathrm{combi}}_k)^c\Bigr].
--   $$
--
--   Until the learner has played the sequence $(1,\dots,1)$ once, the two instances produce the same distribution of observations.
--
--   **Formalization Note** The history (all supervisors and observed episodes) is the whole sample space, so every set of histories is an event of $\mathcal F_K$. Probabilities are the outer measures of the run laws (`PMF.toOuterMeasure`).
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 38, App. A, observation 1, display (A.1)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- (A.1), arXiv:1911.08689v4, App. A, p. 38: for every set `B` of histories after `K` episodes,
`P^ℳ[B ∩ ⋂_k (ℰ^combi_k)^c] = P^{ℳ₀}[B ∩ ⋂_k (ℰ^combi_k)^c]`. -/
theorem eqA1_indistinguishable (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ)
    (B : Set (List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)))) :
    (runLaw (comboLock H A) L K).toOuterMeasure (B ∩ {run | ∀ k < K, ¬ combi k run}) =
      (runLaw (comboLock0 H A) L K).toOuterMeasure (B ∩ {run | ∀ k < K, ¬ combi k run}) := by sorry

end CorruptRobustRL.ElimLB
