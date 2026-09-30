-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_numToState_eq_sum
-- name    : DelayedBCN.Controllability.numToState_eq_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:07:43.835099+00:00
-- url     : https://prove2.me/theorems/055cbad6-c9f3-49e3-b19c-54eea89d3931
-- title:
--   Theorem 4.3 — counting control sequences that reach a destination state
-- statement:
--   Consider a delayed Boolean control network with delay length $\mu\ge1$ and transition-count matrix $Q$. Let $a$ be an initial trajectory, $b_s$ a destination state and $\Xi^{b_s}_\mu$ the set of trajectories whose current (last) state is $b_s$. For every integer $k>0$, the number $\mathbb N_2(k;a,b_s)$ of control sequences of length $k$ that steer the network from $a$ to $x(k)=b_s$ satisfies
--
--   $$
--   \mathbb N_2(k;a,b_s)=\sum_{b\in\Xi^{b_s}_\mu}\mathbb N_1(k;a,b)=\sum_{b\in\Xi^{b_s}_\mu} b^{\mathsf T}Q^k a .
--   $$
--
--   The formula transfers the counting results for trajectories to the counting of control sequences reaching a prescribed state.
--
--   **Formalization Note** Both equalities are stated. $\Xi^{p}_\mu$ is defined as the trajectories whose last entry is $p$, as in eq. (4.3); the index formula (4.4) has a misprinted range and is not transcribed. $k>0$ follows the paper ("Fix an arbitrary integer $k>0$", p. 489).
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 489, Theorem 4.3, Eq. (4.6)

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Theorem 4.3 (Lu et al. 2016, p. 489): for `k > 0`,
`ℕ₂(k; a, bs) = ∑_{b ∈ Ξ^{bs}_μ} ℕ₁(k; a, b) = ∑_{b ∈ Ξ^{bs}_μ} bᵀ Q^k a`. -/
theorem numToState_eq_sum {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (a : Traj μ n) (bs : State n) (k : ℕ) (hk : 0 < k) :
    numToState F k a bs = ∑ b ∈ xiLast bs, numSteering F k a b ∧
      numToState F k a bs = ∑ b ∈ xiLast bs, (Q F ^ k) b a := by sorry

end DelayedBCN.Controllability
