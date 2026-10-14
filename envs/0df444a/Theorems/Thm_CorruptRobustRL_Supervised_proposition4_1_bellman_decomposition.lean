-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_proposition4_1_bellman_decomposition
-- name    : CorruptRobustRL.Supervised.proposition4_1_bellman_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:15.497112+00:00
-- url     : https://prove2.me/theorems/454d29ac-d679-4956-b84e-147f134fdf05
-- title:
--   Proposition 4.1, p. 15 — Bellman-error regret decomposition of a Q-supervised policy over the concatenated policies $\pi\oplus_h\pi^{\mathrm{ucb}}$
-- statement:
--   Let $\mathcal T=(\bar Q,\underline Q,\mathcal A,\pi^{\mathrm{ucb}})$ be a confidence-admissible Q-supervisor for the nominal MDP with horizon $H\ge1$, and let $\pi$ be a randomized Markovian policy (a mixture of deterministic Markov policies) that is Q-supervised by $\mathcal T$. Then
--   $$V^\star-V^{\pi}\le\sum_{h=1}^HE^{\pi}\big[\overline{\mathbf{Bell}}_h(x_h,a_h)\big]+\sum_{h=1}^HE^{\pi\oplus_h\pi^{\mathrm{ucb}}}\Big[\sum_{\tau=h}^H\overline{\mathbf{Bell}}_\tau(x_\tau,a_\tau)-\underline{\mathbf{Bell}}_\tau(x_\tau,a_\tau)\Big],$$
--   where $\pi\oplus_h\pi^{\mathrm{ucb}}$ follows $\pi$ before stage $h$ and $\pi^{\mathrm{ucb}}$ from stage $h$ on.
--
--   The second sum pays for the mismatch between $\pi$ and the UCB policy along fictitious trajectories that switch to $\pi^{\mathrm{ucb}}$.
--
--   **Formalization Note** The Lean sum over `h ∈ range H` and the indicator `h ≤ τ` index both sums from 0.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 15, Proposition 4.1; proof App. D.1, pp. 54–55

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Proposition 4.1 (p. 15): for a confidence-admissible Q-supervisor `𝒯` and a `𝒯`-supervised
randomized Markovian policy `π`,
`V⋆ − V^π ≤ Σ_h E^π[Bell̄_h] + Σ_h E^{π ⊕_h π^ucb}[Σ_{τ ≥ h} (Bell̄_τ − Bell̲_τ)]`. -/
theorem proposition4_1_bellman_decomposition
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (T : QSupervisor X A) (hT : T.IsQSupervisor H) (hadm : IsAdmissible M H T)
    (π : Mixture X A) (hπ : π.IsMixture) (hsup : IsQSupervised H π T) :
    Vstar0 M H - mixValue M H π ≤
      mixExpect M H π (upperBell M H T) +
        ∑ h ∈ range H, mixExpect M H (concatMix π h T.ucb)
          (fun τ x a => if h ≤ τ then upperBell M H T τ x a - lowerBell M H T τ x a else 0) := by sorry

end CorruptRobustRL.Supervised
