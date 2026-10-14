-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_regret_chain
-- name    : CorruptRobustRL.ElimLB.regret_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:18.669863+00:00
-- url     : https://prove2.me/theorems/af5f4d1e-beaa-4849-b967-be5138d9756d
-- title:
--   Chain (i)–(iii), p. 39 — E^ℳ[Regret^ℳ_K] ≥ (1 − A^{−H}) K P^{ℳ₀}[⋂_k (ℰ^combi_k)^c ∩ ⋂_k ℰ^adm_k]
-- statement:
--   Let $H\ge1$, $A\ge2$, and run any uniformly action-eliminating algorithm for $K$ episodes. Its expected regret on the combination-lock instance $\mathcal M$ is bounded below through the all-zero instance $\mathcal M_0$:
--
--   $$
--   \mathbb E^{\mathcal M}\bigl[\mathrm{Regret}^{\mathcal M}_K\bigr]\ \ge\ (1-A^{-H})\,K\,\mathbb P^{\mathcal M_0}\Bigl[\bigcap_{k=1}^K(\mathcal E^{\mathrm{combi}}_k)^c\cap\bigcap_{k=1}^K\mathcal E^{\mathrm{adm}}_k\Bigr].
--   $$
--
--   The right-hand side transfers the regret of $\mathcal M$ to an event of $\mathcal M_0$, on which admissibility can be used.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 39, App. A, chain (i)–(iii)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- The chain (i)–(iii), arXiv:1911.08689v4, App. A, p. 39:
`E^ℳ[Regret^ℳ_K] ≥ (1 − A^{-H}) K P^{ℳ₀}[⋂_k (ℰ^combi_k)^c ∩ ⋂_k ℰ^adm_k]`. -/
theorem regret_chain (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ) :
    (1 - ((A : ℝ)⁻¹) ^ H) * (K : ℝ) *
        ((runLaw (comboLock0 H A) L K).toOuterMeasure
          ({run | ∀ k < K, ¬ combi k run} ∩ {run | ∀ k < K, admEv k run})).toReal ≤
      expRegret (comboLock H A) L K := by sorry

end CorruptRobustRL.ElimLB
