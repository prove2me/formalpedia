-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_noElim_regret_eq
-- name    : CorruptRobustRL.ElimLB.noElim_regret_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:05.571351+00:00
-- url     : https://prove2.me/theorems/34b38c4c-f264-4fe9-b407-b8d008965330
-- title:
--   App. A, observation 2, p. 38 — when ℰ^{no elim}_k holds, V⋆ − V^{ℳ,π_k} = 1 − A^{−H}
-- statement:
--   Let $H\ge1$, $A\ge2$, and let $\mathcal M$ be the combination-lock instance. If a Q-supervisor $\mathcal T$ eliminates no action (every active set is $\mathcal A$ and $\bar Q_h(x,a)\ge\max_{a'}\underline Q_h(x,a')$ for all $h,x,a$), then the policy $\pi$ that plays uniformly at random from the plausible sets of $\mathcal T$ satisfies
--
--   $$
--   V^\star-V^{\mathcal M,\pi}=1-A^{-H}.
--   $$
--
--   The optimal value of $\mathcal M$ is $1$, and the uniform policy collects the reward only by playing the correct combination, which has probability $A^{-H}$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 38, App. A, observation 2, last sentence

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- App. A, observation 2, last sentence, arXiv:1911.08689v4, p. 38: when the Q-supervisor
eliminates no action, the per-episode regret under `ℳ` of the uniformly-at-random policy is
`V⋆ − V^{ℳ,π} = 1 − A^{-H}`. -/
theorem noElim_regret_eq (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : NoElim T) :
    Vstar (comboLock H A) H - valueUnif (comboLock H A) T = 1 - ((A : ℝ)⁻¹) ^ H := by sorry

end CorruptRobustRL.ElimLB
