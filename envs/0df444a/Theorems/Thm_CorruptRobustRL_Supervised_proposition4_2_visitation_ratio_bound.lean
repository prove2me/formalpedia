-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_proposition4_2_visitation_ratio_bound
-- name    : CorruptRobustRL.Supervised.proposition4_2_visitation_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:04.426901+00:00
-- url     : https://prove2.me/theorems/43f42f79-3d00-4b23-8cb8-d859d803e07f
-- title:
--   Proposition 4.2, p. 15 (positive parts) — UCB visitation ratio $\le\rho$ gives $V^\star-V^\pi\le\rho(1+H)\,E^\pi[\sum_h(\text{Bellman errors})_+]$
-- statement:
--   Let $\mathcal T=(\bar Q,\underline Q,\mathcal A,\pi^{\mathrm{ucb}})$ be a confidence-admissible Q-supervisor for the nominal MDP with horizon $H\ge1$, and let $\pi$ be a randomized Markovian policy that is Q-supervised by $\mathcal T$ and has UCB visitation ratio at most $\rho$ with respect to $\mathcal T$. Then
--   $$V^\star-V^{\pi}\le\rho\,(1+H)\,E^{\pi}\Big[\sum_{h=1}^H\max\big(0,\ \overline{\mathbf{Bell}}_h(x_h,a_h),\ \overline{\mathbf{Bell}}_h(x_h,a_h)-\underline{\mathbf{Bell}}_h(x_h,a_h)\big)\Big].$$
--
--   The visitation ratio moves the expectations over fictitious trajectories in Proposition 4.1 back to the trajectories of $\pi$ itself, so the regret of $\pi$ is controlled by its own Bellman errors.
--
--   **Formalization Note** The page prints $E^\pi[\max(\sum_h\overline{\mathbf{Bell}}_h,\sum_h\overline{\mathbf{Bell}}_h-\underline{\mathbf{Bell}}_h)]$ and gives no proof. Bellman errors can be negative (as the page notes right after the statement), and the change of measure through the visitation ratio needs a nonnegative integrand. As printed, the inequality fails on small admissible instances (646 violations among 22,107 random instances with $H,|\mathcal X|,|\mathcal A|\le3$, all with a negative right-hand side). The Lean statement uses the per-stage positive part, the form that follows from Proposition 4.1 because $\rho\ge1$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 15, Proposition 4.2 (with positive parts; follows from Proposition 4.1)

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Proposition 4.2 (p. 15), with positive parts: for a confidence-admissible Q-supervisor `𝒯` and
a `𝒯`-supervised randomized Markovian policy `π` of UCB visitation ratio at most `ρ`,
`V⋆ − V^π ≤ ρ (1 + H) E^π[Σ_h max(0, Bell̄_h, Bell̄_h − Bell̲_h)]`. -/
theorem proposition4_2_visitation_ratio_bound
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T)
    (π : Mixture X A) (hπ : π.IsMixture) (hsup : IsQSupervised H π T)
    (ρ : ℝ) (hρ : HasVisitRatio M H π T.ucb ρ) :
    Vstar0 M H - mixValue M H π ≤
      ρ * (1 + H) * mixExpect M H π
        (fun h x a => max 0 (max (upperBell M H T h x a)
          (upperBell M H T h x a - lowerBell M H T h x a))) := by sorry

end CorruptRobustRL.Supervised
