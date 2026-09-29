-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_trajControllableUnder_iff_irreducible
-- name    : DelayedBCN.Controllability.trajControllableUnder_iff_irreducible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:09:10.092357+00:00
-- url     : https://prove2.me/theorems/f3ed799e-ccb6-4940-beee-fe41d90b495b
-- title:
--   Theorem 3.12 — trajectory controllability under a forbidden set C_t iff the deleted matrix ℚ_{C_t} is irreducible
-- statement:
--   Consider a delayed Boolean control network (2.2) with $n$ state nodes, $m$ inputs, delay length $\mu\ge1$ and arbitrary update functions, and let $C_t$ be any set of forbidden trajectories. Let $Q$ be the transition-count matrix ($Q_{b,a}$ = number of input values taking trajectory $a$ to trajectory $b$ in one step), and let $\mathbb Q_{C_t}$ be the matrix obtained from $Q$ by **deleting** the rows and columns of the trajectories in $C_t$. Then
--
--   $$
--   \text{the network is trajectory controllable under } C_t \iff \mathbb Q_{C_t}\ \text{is irreducible}.
--   $$
--
--   Trajectory controllability under $C_t$ is Definition 3.11: for all trajectories $a,b\notin C_t$ there are an integer $k\ge0$ and a control sequence $(u(0),\dots,u(k-1))$ steering the network from $y(0)=a$ to $y(k)=b$ with $y(i)\notin C_t$ for $i=0,\dots,k$. Irreducibility is Definition 3.7, applied to $\mathbb Q_{C_t}$ with entries viewed as real numbers.
--
--   The theorem is the paper's criterion for controllability with forbidden trajectories; with $C_t=\emptyset$ it recovers Theorem 3.10 up to the step-count convention.
--
--   **Formalization Note** The matrix is the deleted one ($q\times q$, $q=2^{\mu n}-|C_t|$), indexed by the allowed trajectories, not the zeroed $Q_{C_t}$ of Proposition 3.5. Definition 3.11 allows $k=0$, so with a single allowed trajectory both sides hold (a $1\times1$ matrix is irreducible by Definition 3.7). Controllability is defined through the dynamics, not through powers of $Q$.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 486, Theorem 3.12 (with Definition 3.11 and the definition of ℚ_{C_t} on the same page)

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Theorem 3.12 (Lu et al. 2016, p. 486): the delayed BCN is trajectory controllable under the
forbidden set `Ct` (Definition 3.11) if and only if the matrix `ℚ_{C_t}`, obtained from `Q` by
deleting the rows and columns of `Ct`, is irreducible (Definition 3.7). -/
theorem trajControllableUnder_iff_irreducible {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Ct : Finset (Traj μ n)) :
    TrajControllableUnder F Ct ↔
      IsIrreducibleMat ((QDeleted F Ct).map (fun x : ℕ => (x : ℝ))) := by sorry

end DelayedBCN.Controllability
