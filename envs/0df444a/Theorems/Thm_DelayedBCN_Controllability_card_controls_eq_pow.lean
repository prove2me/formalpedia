-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_card_controls_eq_pow
-- name    : DelayedBCN.Controllability.card_controls_eq_pow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:06:15.786693+00:00
-- url     : https://prove2.me/theorems/944ed32a-2404-4bf7-9124-292724970bfd
-- title:
--   Remark 3 — the number of k-step control sequences between two trajectories is an entry of Q^k
-- statement:
--   Consider a delayed Boolean control network with trajectories of length $\mu\ge1$ and transition-count matrix $Q$. For every integer $k\ge0$ and all trajectories $y_a,y_b$, the number $\mathbb N_1(k;y_a,y_b)$ of control sequences $(u(0),\dots,u(k-1))$ that steer the network from $y(0)=y_a$ to $y(k)=y_b$ without any restriction is
--
--   $$
--   \mathbb N_1(k;y_a,y_b)=y_b^{\mathsf T}\,Q^k\,y_a .
--   $$
--
--   This is the unconstrained case $C_t=\emptyset$ of Proposition 3.5, and underlies the state-counting formula of Theorem 4.3.
--
--   **Formalization Note** The identity is stated for all $k\ge0$; at $k=0$ both sides equal $1$ if $y_a=y_b$ and $0$ otherwise.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 484, Remark 3

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Remark 3 (Lu et al. 2016, p. 484): the number of control sequences of length `k` that steer
`ya` to `yb` is the `(yb, ya)` entry of `Q^k`. -/
theorem card_controls_eq_pow {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (ya yb : Traj μ n) (k : ℕ) :
    numSteering F k ya yb = (Q F ^ k) yb ya := by sorry

end DelayedBCN.Controllability
