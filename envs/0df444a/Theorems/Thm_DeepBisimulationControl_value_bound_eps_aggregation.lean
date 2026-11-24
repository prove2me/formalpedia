-- Prove2me | Theorems.Thm_DeepBisimulationControl_value_bound_eps_aggregation
-- name    : DeepBisimulationControl.value_bound_eps_aggregation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:05:36.054481+00:00
-- url     : https://prove2.me/theorems/84d2993e-7353-4ecb-a76a-47eea220cb50
-- title:
--   Theorem 2 (as proved): value bound based on bisimulation metrics
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function, $\gamma\in[0,1)$ and $c<1$ with $\gamma\le c$, and let $\tilde d$ be the bisimulation metric of Definition 2. Let $\varepsilon>0$ and let $\phi:\mathcal S\to C$ map onto a finite set of clusters, each contained in an $\varepsilon$-neighborhood of some state: for each cluster $k$ there is $s_0$ with $\tilde d(s_0,s)\le\varepsilon$ for all $s\in k$. Let $\bar V^*$ be the optimal value function of the aggregated MDP $\bar{\mathcal M}$ (rewards and transitions averaged over each cluster). Then for every state $s$,
--
--   $$|V^*(s)-\bar V^*(\phi(s))|\le\frac{2\varepsilon}{(1-\gamma)(1-c)}.$$
--
--   As $\varepsilon\to0$ the optimal value function of the aggregated MDP converges to that of the original MDP.
--
--   **Formalization Note** Two changes from the printed Theorem 2, both forced by its proof, which applies Ferns et al. (2004), Theorem 5.2: (i) the hypothesis $\gamma\le c$ of that theorem is added, since without it the bound is false; (ii) $\tilde d$ is the bisimulation metric of Definition 2 (maximum over actions) to which the cited theorem applies, not the $\pi^*$-bisimulation metric, for which the bound is false. The paper does not specify the aggregated MDP; the averaged MDP of Ferns et al. (2004) is used.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 5, Theorem 2, eq. (6), p. 5; proof in Appendix A, eq. (12), p. 12

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem value_bound_eps_aggregation {S A C : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] [Fintype C] [DecidableEq C]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (gamma c : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hc1 : c < 1) (hgc : gamma ≤ c)
    (eps : ℝ) (heps : 0 < eps) (phi : S → C) (hphi : Function.Surjective phi)
    (hnbhd : IsEpsAggregation (bisimMetric P R c) phi eps) (s : S) :
    |optValue P R gamma s - optValue (aggKernel P phi) (aggReward R phi) gamma (phi s)| ≤
      2 * eps / ((1 - gamma) * (1 - c)) := by sorry

end DeepBisimulationControl
