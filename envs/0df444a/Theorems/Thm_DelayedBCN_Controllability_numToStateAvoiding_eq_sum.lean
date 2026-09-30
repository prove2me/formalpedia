-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_numToStateAvoiding_eq_sum
-- name    : DelayedBCN.Controllability.numToStateAvoiding_eq_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:08:19.873399+00:00
-- url     : https://prove2.me/theorems/df4cd495-a311-439d-92ca-d5fcebde33b5
-- title:
--   Theorem 5.1 — counting control sequences that reach a state while avoiding forbidden states
-- statement:
--   Consider a delayed Boolean control network with delay length $\mu\ge1$ and transition-count matrix $Q$. Let $C_s$ be a set of forbidden states, $\Xi^{C_s}$ the set of trajectories containing at least one state of $C_s$, and $Q_{C_s}$ the matrix obtained from $Q$ by substituting zeros in the rows and columns of the trajectories in $\Xi^{C_s}$. Let $a$ be an initial trajectory, $b_s$ a destination state and $\Xi^{b_s}_\mu$ the trajectories whose current state is $b_s$. For every integer $k>0$, the number $\mathbb N_2(k;a,b_s,C_s)$ of control sequences of length $k$ that steer the network from $a$ to $x(k)=b_s$ while avoiding $C_s$ satisfies
--
--   $$
--   \mathbb N_2(k;a,b_s,C_s)=\sum_{b\in\Xi^{b_s}_\mu}\mathbb N_1(k;a,b,\Xi^{C_s})=\sum_{b\in\Xi^{b_s}_\mu} b^{\mathsf T}(Q_{C_s})^k a .
--   $$
--
--   The result reduces state avoidance to trajectory avoidance, so that the forbidden-state problem is solved by the matrix algorithm of Proposition 3.5.
--
--   **Formalization Note** "Avoiding $C_s$" is read as the theorem's middle term: no state $x(i)$, $i=1-\mu,\dots,k$ (the initial states included), belongs to $C_s$, equivalently no trajectory $y(0),\dots,y(k)$ lies in $\Xi^{C_s}$. Both equalities are stated; $k>0$ as in the paper.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, pp. 489-490, Theorem 5.1, Eq. (5.1)

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Theorem 5.1 (Lu et al. 2016, pp. 489–490): for `k > 0`,
`ℕ₂(k; a, bs, Cs) = ∑_{b ∈ Ξ^{bs}_μ} ℕ₁(k; a, b, Ξ^{Cs}) = ∑_{b ∈ Ξ^{bs}_μ} bᵀ (Q_{Ξ^{Cs}})^k a`. -/
theorem numToStateAvoiding_eq_sum {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Cs : Finset (State n)) (a : Traj μ n) (bs : State n) (k : ℕ) (hk : 0 < k) :
    numToStateAvoiding F k a bs Cs = ∑ b ∈ xiLast bs, numAvoiding F k a b (xiForbidden Cs) ∧
      numToStateAvoiding F k a bs Cs =
        ∑ b ∈ xiLast bs, (QZeroed F (xiForbidden Cs) ^ k) b a := by sorry

end DelayedBCN.Controllability
