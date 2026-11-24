-- Prove2me | Theorems.Thm_DeepBisimulationControl_task_generalization_non_ancestors
-- name    : DeepBisimulationControl.task_generalization_non_ancestors
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:07:26.709331+00:00
-- url     : https://prove2.me/theorems/30fb2019-61d3-4754-aa08-aa3b7d021652
-- title:
--   Theorem 4 (as proved, part 1): the bisimulation metric ignores factors outside $AN(R)$
-- statement:
--   Let the state space be a product $\mathcal S=\prod_{i\in I}\mathcal S^i$ of finitely many finite factors, and let $\mathcal A$ be a finite nonempty action space. Suppose the one-step dynamics factorise along a causal graph:
--
--   $$\mathcal P(s'\mid s,a)=\prod_{i\in I}T_i(s'^i\mid s,a),$$
--
--   where each $T_i(\cdot\mid s,a)$ is a probability distribution on $\mathcal S^i$ that depends on $s$ only through the factors in $\mathrm{pa}(i)$, and the reward $\mathcal R(s,a)$ depends on $s$ only through the factors in $\mathrm{pa}(R)$. Let $AN(R)$ be the causal ancestors of the reward, the factors with a directed path to the reward. Let $c\in[0,1)$ and let $\tilde d$ be the bisimulation metric of Definition 2. If two states $s,s'$ agree on every factor in $AN(R)$, then
--
--   $$\tilde d(s,s')=0,$$
--
--   and every encoder $\phi:\mathcal S\to\mathbb R^m$ with $\|\phi(s_i)-\phi(s_j)\|_1=\tilde d(s_i,s_j)$ for all $s_i,s_j$ satisfies $\phi(s)=\phi(s')$.
--
--   So a bisimulation representation does not change when only factors outside $AN(R)$ change.
--
--   **Formalization Note** The printed Theorem 4 says informally that $\mathcal Z$ "encodes information about all the causal ancestors of the reward". Its proof has two parts. This statement is part 1, which is the precise claim the proof makes. Part 2 only says that a change of an ancestor "can" give a positive distance and is not included. The proof uses the maximum over actions of eq. (3), so $\tilde d$ is the metric of Definition 2.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 5, Definition 3 and Theorem 4, pp. 5-6; proof in Appendix A, part 1), p. 12

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem task_generalization_non_ancestors {I A : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [Fintype A] [Nonempty A]
    (T : ∀ i, (∀ j, X j) → A → X i → ℝ)
    (hT0 : ∀ i s a x, 0 ≤ T i s a x) (hT1 : ∀ i s a, ∑ x, T i s a x = 1)
    (pa : I → Set I) (hpa : ∀ i a x, DependsOnlyOn (fun s => T i s a x) (pa i))
    (R : (∀ j, X j) → A → ℝ) (paR : Set I) (hR : ∀ a, DependsOnlyOn (fun s => R s a) paR)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (s s' : ∀ j, X j) (hss' : ∀ j ∈ causalAncestors pa paR, s j = s' j) :
    bisimMetric (factoredKernel T) R c s s' = 0 ∧
    ∀ (m : ℕ) (phi : (∀ j, X j) → Fin m → ℝ),
      (∀ u v, l1Dist (phi u) (phi v) = bisimMetric (factoredKernel T) R c u v) → phi s = phi s' := by sorry

end DeepBisimulationControl
