-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_bellman_solution_sets
-- name    : AvgRewardPMD.SPMD.bellman_solution_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:21.453249+00:00
-- url     : https://prove2.me/theorems/b87cf91a-7922-48b6-8e9b-8d770cd73935
-- title:
--   §2.1, p. 6 — under Assumption 1 the solutions of (2.3) and (2.4) are exactly {V̄^π + b1} and {Q̄^π + b1}
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c')$ be a finite AMDP satisfying the mixing Assumption 1 and let $\pi$ be a feasible policy, with average cost $\rho^\pi$, basic differential value function $\bar V^\pi$ and basic differential Q-function $\bar Q^\pi$. Then
--
--   1. the solution set of the Bellman equation
--   $$V=c'^\pi-\rho^\pi\mathbf 1_{|\mathcal S|}+P_\pi V\qquad(2.3)$$
--   is exactly $\{\bar V^\pi+b\mathbf 1_{|\mathcal S|}: b\in\mathbb R\}$;
--   2. the solution set of
--   $$Q=c'-\rho^\pi\mathbf 1_{|\mathcal S|\times|\mathcal A|}+P^\pi Q\qquad(2.4)$$
--   is exactly $\{\bar Q^\pi+b\mathbf 1_{|\mathcal S|\times|\mathcal A|}: b\in\mathbb R\}$.
--
--   Each clause says both that $\bar V^\pi$ (resp. $\bar Q^\pi$) solves its equation and that every solution differs from it by a constant. With $c'(s,a)=c(s,a)+h^\pi(s)$ these are the paper's equations $V=c^\pi+h^\pi-\rho^\pi\mathbf 1+P_\pi V$ and $Q=c+\tilde h^\pi-\rho^\pi\mathbf 1+P^\pi Q$, $\tilde h^\pi(s,a)=h^\pi(s)$.
--
--   **Formalization Note** $\bar V^\pi$ and $\bar Q^\pi$ are the series of expectations of $c'(s_t,a_t)-\rho^\pi$. In the equation at the state $s$ (resp. the pair $(s,a)$) the scalar $\rho^\pi$ is written as `avgCost` at $s$, which is the same number for every state under Assumption 1.
--
--   Differences from the source:
--   - generalization: the costs c^π + h^π and c + h̃^π → any cost c′(s,a); reason: c′(s,a) = c(s,a) + h^π(s) is an instance, with c′^π = c^π + h^π
--   - encoding: the scalar ρ^π → ρ^π(s) at the state of each equation; reason: ρ^π(s) does not depend on s under Assumption 1 (milestone 1)
--   - reading: V̄^π(s) = E_π[Σ_t (c(s_t,a_t) + h^π(s_t) − ρ^π) | s_0 = s] (and Q̄^π likewise) → the series of the expectations Σ_t (E_π[c(s_t,a_t) + h^π(s_t) | s_0 = s] − ρ^π); reason: the pathwise series need not converge (an i.i.d. chain with non-constant cost), while the series of expectations converges absolutely under Assumption 1
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 6, §2.1, (2.3)–(2.4) and the sentence after them

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning

theorem bellman_solution_sets {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (c : S → A → ℝ) :
    {V : S → ℝ | ∀ s, V s = InducedReward π c s - avgCost P π c s
        + ∑ s', InducedTransition π P s s' * V s'}
      = {V : S → ℝ | ∃ b : ℝ, V = fun s => diffV P π c s + b} ∧
    {Q : S × A → ℝ | ∀ x, Q x = c x.1 x.2 - avgCost P π c x.1
        + ∑ y, saTransition P π x y * Q y}
      = {Q : S × A → ℝ | ∃ b : ℝ, Q = fun x => diffQ P π c x + b} := by sorry

end AvgRewardPMD.SPMD
