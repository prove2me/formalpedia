-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_le_of_bellman_ineq
-- name    : BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:34:09.759014+00:00
-- url     : https://prove2.me/theorems/be7f19f0-1247-499d-a856-ac33a558c124
-- title:
--   Bellman optimality inequality upper-bounds the optimal gain
-- statement:
--   Let $M$ be a finite MDP with at least one state and one action, and suppose the pair $(\rho, v)$ satisfies the Bellman optimality *inequality*
--
--   $$r_a(s) + \langle P_a(s), v\rangle \;\le\; \rho + v(s) \qquad \text{for all states } s \text{ and actions } a,$$
--
--   with $v$ bounded. Then the optimal gain of $M$ satisfies
--
--   $$\rho^*(M) \;\le\; \rho .$$
--
--   This is the verification half of Theorem 38.2 of Lattimore and Szepesvári — the direction stating that any solution of the optimality equation certifies an upper bound on the achievable long-run average reward. It is the form in which optimistic reinforcement learning uses the theorem: in phase $k$ the algorithm UCRL2 computes a pair $(\rho_k, v_k)$ solving the Bellman optimality equation of the extended MDP, whose transition rows include those of the true MDP whenever the confidence sets hold; the inequality above then holds for the true $M$ and gives the optimism $\rho^* \le \rho_k$ of Eq. (38.17), which is Step 1 of the proof of Theorem 38.6.
--
--   Note that the hypothesis is only an inequality and that $\rho^*$ is the supremum over *all* history-dependent randomised policies and all starting states, so no communication assumption is needed.
--
--   The proof divides the finite-horizon estimate $\mathbb{E}[\sum_{t \le n} r_{A_t}(S_t)] \le n\rho + \mathrm{span}(v)$ by $n$: the span disappears in the limit, so the gain $\bar\rho^s_\pi = \limsup_n \frac{1}{n}\mathbb{E}^\pi[\sum_{t\le n} r_{A_t}(S_t) \mid S_1 = s]$ of every policy from every state is at most $\rho$, and $\rho^*$ is the supremum of those gains.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 38.2 (Section 38.2) and Eq. (38.17) in Step 1 of the proof of Theorem 38.6; Puterman, Markov Decision Processes (Wiley 1994), Theorem 8.4.1; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq {S A : ℕ}
    (hS : 0 < S) (hA : 0 < A) (M : FiniteMDP S A) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) :
    mdpOptimalGain M ≤ ρ := by
  sorry
