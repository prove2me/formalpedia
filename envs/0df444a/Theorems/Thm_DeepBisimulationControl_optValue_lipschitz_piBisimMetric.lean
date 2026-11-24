-- Prove2me | Theorems.Thm_DeepBisimulationControl_optValue_lipschitz_piBisimMetric
-- name    : DeepBisimulationControl.optValue_lipschitz_piBisimMetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:03:57.764062+00:00
-- url     : https://prove2.me/theorems/3289fea2-d266-42ed-81ad-5fd3baaa4d3a
-- title:
--   Theorem 5: $V^*$ is Lipschitz with respect to $\tilde d$
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function, $\gamma\in[0,1)$ and $c<1$ with $c\ge\gamma$. Let $\pi^*$ be an optimal policy and $\tilde d$ the $\pi^*$-bisimulation metric, $\tilde d=\sup_nF(\cdot,\pi^*)^n(0)$. Then for all states $s_i,s_j$,
--
--   $$|V^*(s_i)-V^*(s_j)|\le\frac1{1-c}\,\tilde d(s_i,s_j).$$
--
--   So $V^*$ is Lipschitz with respect to $\tilde d$ with constant $1/(1-c)$.
--
--   **Formalization Note** The policy $\pi^*$ may be any optimal stationary stochastic policy; deterministic optimal policies are the special case.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 5, Theorem 5, eq. (7), p. 6 (proof cited from Ferns et al. 2004, Theorem 5.1)

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem optValue_lipschitz_piBisimMetric {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (gamma c : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hc1 : c < 1) (hgc : gamma ≤ c)
    (pi : S → A → ℝ) (hpi : IsOptimalPolicy P R gamma pi) (s t : S) :
    |optValue P R gamma s - optValue P R gamma t| ≤ 1 / (1 - c) * piBisimMetric P R c pi s t := by sorry

end DeepBisimulationControl
