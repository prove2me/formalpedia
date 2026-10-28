-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_adm_imp_noElim
-- name    : CorruptRobustRL.ElimLB.adm_imp_noElim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:09.378245+00:00
-- url     : https://prove2.me/theorems/23068492-9b22-452a-9f69-ddbe74711003
-- title:
--   App. A, observation 3, p. 38 — a Q-supervisor confidence-admissible for ℳ₀ eliminates no action (ℰ^adm_k ⊆ ℰ^{no elim}_k)
-- statement:
--   Let $H\ge1$, $A\ge2$, and let $\mathcal M_0$ be the all-zero-reward combination-lock instance. If a Q-supervisor $\mathcal T=(\bar Q,\underline Q,\mathscr A,\pi^{\mathrm{ucb}})$ is confidence-admissible with respect to the optimal actions and Q-functions of $\mathcal M_0$, then it eliminates no action:
--
--   $$
--   \mathscr A_h(x)=\mathcal A\quad\text{and}\quad\bar Q_h(x,a)\ge\max_{a'\in\mathcal A}\underline Q_h(x,a')\qquad\forall h\in[H],\ x\in\mathcal X,\ a\in\mathcal A.
--   $$
--
--   Under $\mathcal M_0$ every action is optimal, so admissibility forces every action to stay active. Hence $\mathcal E^{\mathrm{adm}}_k\subseteq\mathcal E^{\mathrm{no\,elim}}_k$ for every episode.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 38, App. A, observation 3

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- App. A, observation 3, arXiv:1911.08689v4, p. 38: a Q-supervisor that is
confidence-admissible for `ℳ₀` eliminates no action. -/
theorem adm_imp_noElim (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : IsAdmissible (comboLock0 H A) T) :
    NoElim T := by sorry

end CorruptRobustRL.ElimLB
