-- Prove2me | Theorems.Thm_DelayedBCN_Controllability_stateControllable_of_trajControllable
-- name    : DelayedBCN.Controllability.stateControllable_of_trajControllable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:08:45.465903+00:00
-- url     : https://prove2.me/theorems/3c340b0d-2786-4938-9be9-8464603feb58
-- title:
--   Corollary 5.3 — trajectory controllability implies state controllability
-- statement:
--   Consider a delayed Boolean control network (2.2) with delay length $\mu\ge1$, without any forbidden states or trajectories. If it is trajectory controllable (Definition 3.1: every trajectory is reachable from every initial trajectory in some $k\ge1$ steps), then it is state controllable (Definition 4.1: from every initial trajectory $a$, every state $x_d$ equals $x(k)$ for some $k>0$ and some control sequence of length $k$):
--
--   $$
--   \text{trajectory controllable}\ \Longrightarrow\ \text{state controllable}.
--   $$
--
--   The converse fails in general (Remark 5 of the paper), so trajectory controllability is a sufficient but not necessary condition for state controllability.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, p. 490, Corollary 5.3

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix

namespace DelayedBCN.Controllability

/-- Corollary 5.3 (Lu et al. 2016, p. 490): a trajectory controllable delayed BCN (no forbidden
states or trajectories) is state controllable. -/
theorem stateControllable_of_trajControllable {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (h : TrajControllable F) : StateControllable F := by sorry

end DelayedBCN.Controllability
