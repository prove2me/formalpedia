-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_corollary1_interval_bounds_attained
-- name    : BoundedParamMDP.Optimal.corollary1_interval_bounds_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:28.291053+00:00
-- url     : https://prove2.me/theorems/8f1ed223-376c-457c-af2b-07d0d06136d5
-- title:
--   Corollary 1 — $V_\downarrow{}_\pi=\min_{M}V_{M,\pi}$ and $V_\uparrow{}_\pi=\max_M V_{M,\pi}$ for $\le_{\mathrm{dom}}$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP and $\pi$ a policy. The bounds of the interval value function are a minimum and a maximum of value functions for the dominance order:
--   $$
--   V_\downarrow{}_\pi=\min_{M\in M_\updownarrow}V_{M,\pi},\qquad V_\uparrow{}_\pi=\max_{M\in M_\updownarrow}V_{M,\pi},
--   $$
--   that is, there is $M\in M_\updownarrow$ with $V_{M,\pi}=V_\downarrow{}_\pi$ at every state and $V_{M,\pi}\le_{\mathrm{dom}}V_{M',\pi}$ for every $M'\in M_\updownarrow$, and there is $M\in M_\updownarrow$ with $V_{M,\pi}=V_\uparrow{}_\pi$ and $V_{M,\pi}\ge_{\mathrm{dom}}V_{M',\pi}$ for every $M'\in M_\updownarrow$.
--
--   The statewise minima and maxima of Definition 3 are therefore attained, and attained by one MDP for all states at once.
--
--   **Formalization Note** $V_\downarrow{}_\pi(q)$ and $V_\uparrow{}_\pi(q)$ are defined as the real infimum and supremum over the members; the corollary says these are attained, uniformly in $q$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 15, Corollary 1

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Corollary 1 (p. 15): `V↓π = min_{M ∈ M↕} V_{M,π}` and `V↑π = max_{M ∈ M↕} V_{M,π}`, the
minimum and maximum being taken for `≤_dom` and attained: some member's value function equals
the statewise infimum `V↓π` and is dominated by every member's, and some member's equals the
statewise supremum `V↑π` and dominates every member's. -/
theorem corollary1_interval_bounds_attained {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] (B : BMDP Q A) (π : Policy Q A) :
    (∃ M : Member B, value M.1 π = lowerV B π ∧ IsPiMin B π M) ∧
    (∃ M : Member B, value M.1 π = upperV B π ∧ IsPiMax B π M) := by sorry

end BoundedParamMDP.Optimal
