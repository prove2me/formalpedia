-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_theorem7_policy_extremal_mdps
-- name    : BoundedParamMDP.Optimal.theorem7_policy_extremal_mdps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:51.421993+00:00
-- url     : https://prove2.me/theorems/1ac3d2c0-a5c9-4489-8489-6ab71beb35a0
-- title:
--   Theorem 7 — $\pi$-maximizing and $\pi$-minimizing MDPs exist in $X_{M_\updownarrow}\subseteq M_\updownarrow$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP and $\pi$ a policy. There is an order-maximizing MDP $M\in X_{M_\updownarrow}\subseteq M_\updownarrow$ that is $\pi$-maximizing,
--   $$
--   V_{M,\pi}\ge_{\mathrm{dom}}V_{M',\pi}\quad\text{for every }M'\in M_\updownarrow,
--   $$
--   and an order-maximizing MDP $M\in X_{M_\updownarrow}$ that is $\pi$-minimizing, $V_{M,\pi}\le_{\mathrm{dom}}V_{M',\pi}$ for every $M'\in M_\updownarrow$.
--
--   The point is that one MDP is extreme simultaneously at every state, so the bounds of the interval value function are the values of $\pi$ in two single MDPs.
--
--   **Formalization Note** The comparison is against all members of $M_\updownarrow$, not only against $X_{M_\updownarrow}$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 15, Theorem 7

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Theorem 7 (p. 15): for any policy `π` there exist `π`-maximizing and `π`-minimizing
MDPs in `X_{M↕} ⊆ M↕`. -/
theorem theorem7_policy_extremal_mdps {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (B : BMDP Q A) (π : Policy Q A) :
    (∃ M : Member B, M.1.F ∈ XM B ∧ IsPiMax B π M) ∧
    (∃ M : Member B, M.1.F ∈ XM B ∧ IsPiMin B π M) := by sorry

end BoundedParamMDP.Optimal
