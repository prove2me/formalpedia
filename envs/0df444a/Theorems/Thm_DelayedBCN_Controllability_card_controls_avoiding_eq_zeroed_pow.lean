-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_card_controls_avoiding_eq_zeroed_pow
-- name    : DelayedBCN.Controllability.card_controls_avoiding_eq_zeroed_pow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:04:51.012987+00:00
-- url     : https://prove2.me/theorems/08a34f03-d090-431b-a1c6-ae89372e4d4d
-- title:
--   Proposition 3.5 — the number of k-step control sequences avoiding C_t is an entry of (Q_{C_t})^k
-- statement:
--   Consider a delayed Boolean control network with trajectories of length $\mu\ge1$, a set $C_t$ of forbidden trajectories and two trajectories $y_a,y_b$. Let $Q$ be the transition-count matrix and $Q_{C_t}$ the matrix obtained from $Q$ by substituting zeros in the rows and columns of the trajectories in $C_t$. For every integer $k>0$, the number $\mathbb N_1(k;y_a,y_b,C_t)$ of control sequences $(u(0),\dots,u(k-1))$ that steer the network from $y(0)=y_a$ to $y(k)=y_b$ with $y(i)\notin C_t$ for $i=0,1,\dots,k$ satisfies
--
--   $$
--   \mathbb N_1(k;y_a,y_b,C_t)=y_b^{\mathsf T}\,(Q_{C_t})^k\,y_a ,
--   $$
--
--   that is, it is the entry of $(Q_{C_t})^k$ in row $y_b$ and column $y_a$.
--
--   The proposition turns the enumeration of admissible control sequences into matrix multiplication; Theorems 3.12 and 5.1 are built on it.
--
--   **Formalization Note** The restriction $k>0$ is the paper's ("Fix an arbitrary integer $k>0$", p. 483); at $k=0$ the identity fails when $y_a=y_b\in C_t$. The entry $y_b^{\mathsf T}My_a$ is the matrix entry $M(y_b,y_a)$ with rows and columns indexed by trajectories.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 483, Proposition 3.5, Eq. (3.4)

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Proposition 3.5 (Lu et al. 2016, p. 483): for `k > 0`, the number of control sequences of
length `k` that steer `ya` to `yb` while avoiding `Ct` is the `(yb, ya)` entry of `(Q_{C_t})^k`. -/
theorem card_controls_avoiding_eq_zeroed_pow {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Ct : Finset (Traj μ n)) (ya yb : Traj μ n) (k : ℕ) (hk : 0 < k) :
    numAvoiding F k ya yb Ct = (QZeroed F Ct ^ k) yb ya := by sorry

end DelayedBCN.Controllability
