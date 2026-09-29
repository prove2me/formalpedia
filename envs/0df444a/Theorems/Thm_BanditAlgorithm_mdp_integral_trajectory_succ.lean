-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ
-- name    : BanditAlgorithm.mdp_integral_trajectory_succ
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:32:07.549269+00:00
-- url     : https://prove2.me/theorems/315cfb4e-b2d9-4bf7-900b-cd815bb0ad44
-- title:
--   One-round peel of a trajectory integral
-- statement:
--   Let $M$ be a finite MDP, $\pi$ a policy and $\mu_0$ an initial state distribution. For every $n$ and every $F$ on trajectories of $n+1$ rounds,
--
--   $$\int F \, d\mathbb{P}_{n+1} \;=\; \int \left( \int F\big(h \frown (s,a)\big) \, d\big(\mathrm{step}_n(h)\big)(s,a) \right) d\mathbb{P}_n(h),$$
--
--   where $\mathbb{P}_n$ is the law of the trajectory $(S_1,A_1),\dots,(S_n,A_n)$ produced by the interconnection of $\pi$ with $M$, and $\mathrm{step}_n(h)$ is the kernel that draws the next state $S_{n+1}$ from $P_{A_n}(S_n)$ (from $\mu_0$ when $n = 0$) and then the action $A_{n+1}$ from $\pi$ given the history.
--
--   This is the Markov property of the interaction protocol of Lattimore and Szepesvári, Figure 38.1, in the form in which every argument about MDP trajectories consumes it: it is the induction step for any quantity accumulated along a trajectory, and in particular for the accumulation of the Bellman inequality and for the martingale-difference term of the UCRL2 regret decomposition.
--
--   No integrability hypothesis is needed: the trajectory space $(\mathrm{Fin}\,S \times \mathrm{Fin}\,A)^{n+1}$ is finite, so every function on it is integrable against a finite measure. The proof is the change of variables along the map $\mathrm{Fin.snoc}$ that appends the last round, followed by the Fubini property of the composition-product of a measure with a kernel.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.1 and Figure 38.1 (the MDP interaction protocol and the induced measure over trajectories); the statement is the Markov property of that measure, used throughout the proof of Theorem 38.6.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_integral_trajectory_succ {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ)
    (F : MDPTrajectory S A (n + 1) → ℝ) :
    ∫ h, F h ∂(mdpMeasure M μ0 π (n + 1))
      = ∫ h, (∫ p, F (Fin.snoc h p) ∂(mdpStepKernel M μ0 π n h))
          ∂(mdpMeasure M μ0 π n) := by
  sorry
