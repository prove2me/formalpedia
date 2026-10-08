-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_theorem8_optimal_policies_exist
-- name    : BoundedParamMDP.Optimal.theorem8_optimal_policies_exist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:22.015521+00:00
-- url     : https://prove2.me/theorems/a9113cc8-cdd1-4d6e-8182-4c0646e243ed
-- title:
--   Theorem 8 — optimistically and pessimistically optimal policies exist
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP over finite $Q$ and a finite nonempty action set $A$. There is a policy $\pi_{\mathrm{opt}}$ with
--   $$
--   V_\updownarrow{}_{\pi_{\mathrm{opt}}}(q)\ge_{\mathrm{opt}}V_\updownarrow{}_{\pi}(q)\quad\text{for every policy }\pi\text{ and every state }q,
--   $$
--   and there is a policy $\pi_{\mathrm{pes}}$ with $V_\updownarrow{}_{\pi_{\mathrm{pes}}}(q)\ge_{\mathrm{pes}}V_\updownarrow{}_{\pi}(q)$ for every $\pi$ and $q$.
--
--   The orders $\le_{\mathrm{opt}}$ and $\le_{\mathrm{pes}}$ are only partial on interval value functions, so a maximum over policies need not exist a priori; this theorem shows it does, and so justifies the optimal interval value functions $V_\updownarrow{}_{\mathrm{opt}}$ and $V_\updownarrow{}_{\mathrm{pes}}$ of Definition 8.
--
--   **Formalization Note** Policies are the deterministic stationary maps $Q\to A$, the paper's class $\Pi$. $A$ is assumed nonempty (otherwise there is no policy when $Q\ne\emptyset$).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 17, Theorem 8

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Theorem 8 (p. 17): there exists at least one optimistically optimal policy, and there
exists at least one pessimistically optimal policy. -/
theorem theorem8_optimal_policies_exist {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [Nonempty A] (B : BMDP Q A) :
    (∃ πo : Policy Q A, IsOptOptimal B πo) ∧ (∃ πp : Policy Q A, IsPesOptimal B πp) := by sorry

end BoundedParamMDP.Optimal
