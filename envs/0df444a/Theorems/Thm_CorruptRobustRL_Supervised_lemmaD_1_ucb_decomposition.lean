-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemmaD_1_ucb_decomposition
-- name    : CorruptRobustRL.Supervised.lemmaD_1_ucb_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:07.132208+00:00
-- url     : https://prove2.me/theorems/56b35744-d7e4-4cbe-86da-59544d6ce93d
-- title:
--   Lemma D.1, p. 54 — for a confidence-admissible Q-supervisor, $V^\star-V^{\pi^{\mathrm{ucb}}}\le E^{\pi^{\mathrm{ucb}}}[\sum_h\overline{\mathbf{Bell}}_h(x_h,a_h)]$
-- statement:
--   Let $\mathcal T=(\bar Q,\underline Q,\mathcal A,\pi^{\mathrm{ucb}})$ be a Q-supervisor (estimates in $[0,H]$, UCB policy an active-set argmax of $\bar Q$) for the nominal MDP with horizon $H\ge1$. If $\mathcal T$ is confidence-admissible, then
--   $$V^\star-V^{\pi^{\mathrm{ucb}}}\le E^{\pi^{\mathrm{ucb}}}\Big[\sum_{h=1}^H\overline{\mathbf{Bell}}_h(x_h,a_h)\Big].$$
--
--   This is the classical optimism-based regret decomposition for UCB policies, the case $\pi=\pi^{\mathrm{ucb}}$ of Proposition 4.1.
--
--   **Formalization Note** The UCB policy maximizes $\bar Q$ over the active set (see the Supervisor definition).
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 54, Lemma D.1, (D.1)

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Lemma D.1 (p. 54): for a confidence-admissible Q-supervisor,
`V⋆ − V^{π^ucb} ≤ E^{π^ucb}[Σ_h Bell̄_h(x_h, a_h)]`. -/
theorem lemmaD_1_ucb_decomposition
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T) :
    Vstar0 M H - value M H T.ucb ≤ expectDet M H T.ucb (upperBell M H T) := by sorry

end CorruptRobustRL.Supervised
