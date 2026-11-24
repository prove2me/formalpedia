-- Prove2me | Theorems.Thm_DeepBisimulationControl_bisimMetric_unique_fixed_point
-- name    : DeepBisimulationControl.bisimMetric_unique_fixed_point
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:02:55.218334+00:00
-- url     : https://prove2.me/theorems/1631a3f4-efc5-41ec-8ae2-63f89fecd115
-- title:
--   Definition 2: the bisimulation metric is the unique solution of eq. (3)
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function and $c\in[0,1)$. Let $\tilde d=\sup_nF^n(0)$, where
--
--   $$F(d)(s_i,s_j)=\max_{a\in\mathcal A}\,(1-c)\,|\mathcal R(s_i,a)-\mathcal R(s_j,a)|+c\,W_1\big(\mathcal P(\cdot\mid s_i,a),\mathcal P(\cdot\mid s_j,a);d\big).$$
--
--   Then:
--   1. $\tilde d$ is a pseudometric on $\mathcal S$;
--   2. $\tilde d$ satisfies eq. (3), $F(\tilde d)=\tilde d$;
--   3. every function $d:\mathcal S\times\mathcal S\to\mathbb R$ with $F(d)=d$ equals $\tilde d$.
--
--   Definition 2 of the paper defines the bisimulation metric as the solution of eq. (3), citing Ferns et al. (2011); this statement says that the solution exists, is unique and is a pseudometric.
--
--   **Formalization Note** The paper takes existence and uniqueness from the literature; here they are stated as a result about the explicit construction $\sup_nF^n(0)$.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 3, Definition 2, eq. (3), p. 4 (citing Ferns et al. 2011, Theorem 2.6, and Ferns et al. 2004, Theorem 4.5)

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem bisimMetric_unique_fixed_point {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    IsPseudometric (bisimMetric P R c) ∧
    bisimOperator P R c (bisimMetric P R c) = bisimMetric P R c ∧
    ∀ d : S → S → ℝ, bisimOperator P R c d = d → d = bisimMetric P R c := by sorry

end DeepBisimulationControl
