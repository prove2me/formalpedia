-- Prove2me | Theorems.Thm_DeepBisimulationControl_value_bound_learning_error
-- name    : DeepBisimulationControl.value_bound_learning_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:06:58.203667+00:00
-- url     : https://prove2.me/theorems/14a3bc7e-c781-4452-acc6-63aa7c77845b
-- title:
--   Section 5, bound after Theorem 2 (as proved): value bound with learning error $\mathcal L$
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function, $\gamma\in[0,1)$ and $c<1$ with $\gamma\le c$, and let $\tilde d$ be the bisimulation metric of Definition 2. Let $\psi:\mathcal S\to\mathbb R^m$ be an encoder with learning error
--
--   $$\mathcal L=\sup_{s_i,s_j\in\mathcal S}\big|\,\|\psi(s_i)-\psi(s_j)\|_1-\tilde d(s_i,s_j)\big|.$$
--
--   Let $\varepsilon>0$ and let $\phi:\mathcal S\to C$ map onto a finite set of clusters, each contained in an $\varepsilon$-neighborhood of some state for the learned distance $\|\psi(\cdot)-\psi(\cdot)\|_1$. Let $\bar V^*$ be the optimal value function of the aggregated MDP. Then for every state $s$,
--
--   $$|V^*(s)-\bar V^*(\phi(s))|\le\frac{2\varepsilon+2\mathcal L}{(1-\gamma)(1-c)}.$$
--
--   **Formalization Note** The paper states this bound in one sentence after Theorem 2 and uses $\phi$ both for the encoder and for the map to clusters. Here the encoder is $\psi$ and the clusters are $\varepsilon$-neighborhoods for the learned distance, which is the reading under which $\mathcal L$ enters the bound. The hypothesis $\gamma\le c$ and the use of the Definition 2 metric are inherited from Theorem 2 (as proved).
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 5, paragraph after Theorem 2, p. 5

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem value_bound_learning_error {S A C : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] [Fintype C] [DecidableEq C]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (gamma c : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hc1 : c < 1) (hgc : gamma ≤ c)
    {m : ℕ} (psi : S → Fin m → ℝ) (eps : ℝ) (heps : 0 < eps) (phi : S → C)
    (hphi : Function.Surjective phi)
    (hnbhd : IsEpsAggregation (fun u v => l1Dist (psi u) (psi v)) phi eps) (s : S) :
    |optValue P R gamma s - optValue (aggKernel P phi) (aggReward R phi) gamma (phi s)| ≤
      (2 * eps + 2 * learningError (bisimMetric P R c) psi) / ((1 - gamma) * (1 - c)) := by sorry

end DeepBisimulationControl
