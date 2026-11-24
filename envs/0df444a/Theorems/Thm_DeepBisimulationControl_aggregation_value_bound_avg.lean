-- Prove2me | Theorems.Thm_DeepBisimulationControl_aggregation_value_bound_avg
-- name    : DeepBisimulationControl.aggregation_value_bound_avg
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:04:50.294494+00:00
-- url     : https://prove2.me/theorems/3a5ccc34-83da-4210-b947-8a3fd5f23523
-- title:
--   Theorem 2, proof step (Ferns et al. 2004, Theorem 5.2): aggregation bound through average in-cluster distance
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function, $\gamma\in[0,1)$ and $c<1$ with $\gamma\le c$. Let $\tilde d$ be the bisimulation metric of Definition 2. Let $\phi:\mathcal S\to C$ map onto a finite set of clusters, let $\bar V^*$ be the optimal value function of the aggregated MDP (rewards and transitions averaged over each cluster), and let $g(s,\tilde d)=\frac1{|\phi(s)|}\sum_{s'\in\phi(s)}\tilde d(s,s')$. Then for every state $s$,
--
--   $$(1-c)\,|V^*(s)-\bar V^*(\phi(s))|\le g(s,\tilde d)+\frac{\gamma}{1-\gamma}\max_{u\in\mathcal S}g(u,\tilde d).$$
--
--   This is the first line of the proof of Theorem 2, taken from Ferns, Panangaden and Precup (2004).
--
--   **Formalization Note** The paper writes this step as Theorem 5.1 of Ferns et al. (2004); the inequality is their Theorem 5.2, which assumes $\gamma\le c$ and defines the aggregated MDP by uniform averages over clusters. Both are written in here. The aggregated MDP's optimal value at the cluster of $s$ is the paper's $V^*(\phi(s))$.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Appendix A, proof of Theorem 2, first display, p. 12 (citing Ferns et al. 2004, Theorem 5.2)

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem aggregation_value_bound_avg {S A C : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] [Fintype C] [DecidableEq C]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (gamma c : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hc1 : c < 1) (hgc : gamma ≤ c)
    (phi : S → C) (hphi : Function.Surjective phi) (s : S) :
    (1 - c) * |optValue P R gamma s - optValue (aggKernel P phi) (aggReward R phi) gamma (phi s)| ≤
      avgClusterDist (bisimMetric P R c) phi s +
        gamma / (1 - gamma) * ⨆ u : S, avgClusterDist (bisimMetric P R c) phi u := by sorry

end DeepBisimulationControl
