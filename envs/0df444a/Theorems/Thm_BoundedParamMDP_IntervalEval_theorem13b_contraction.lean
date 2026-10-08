-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_theorem13b_contraction
-- name    : BoundedParamMDP.IntervalEval.theorem13b_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:35.602069+00:00
-- url     : https://prove2.me/theorems/2543028d-4a95-46cf-a0a2-b14cbc1ca453
-- title:
--   Theorem 13(b) — $IVI_{\downarrow opt,V}$ and $IVI_{\uparrow pes,V}$ are contraction mappings
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$ and finite nonempty action set $A$. For a value function $V$, $IVI_{\downarrow opt,V}(V')=IVI_{\downarrow opt}([V',V])$ and $IVI_{\uparrow pes,V}(V')=IVI_{\uparrow pes}([V,V'])$ are maps from value functions to value functions; their action choices are governed by the sets $\rho_V(p)$ and $\sigma_V(p)$.
--
--   **Theorem 13(b).** For any value function $V$ (with its associated action set selection functions $\rho_V$ and $\sigma_V$), $IVI_{\downarrow opt,V}$ and $IVI_{\uparrow pes,V}$ are contraction mappings: each $T$ of them has some $\lambda\in[0,1)$ with
--
--   $$\|Tv-Tu\|\le\lambda\|v-u\|\qquad\text{for all value functions }u,v.$$
--
--   This is what makes the lower bounds of optimistic (upper bounds of pessimistic) interval value iteration converge once the other bound has converged.
--
--   **Formalization Note.** No relation between $V$ and the argument $V'$ is assumed, so $[V',V]$ may be an improper interval, as on the page. The modulus may depend on $V$ (the paper's statement is per $V$).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 25, Theorem 13(b) (proof p. 47)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalValueIteration

namespace BoundedParamMDP.IntervalEval

/-- Theorem 13(b) (Givan–Leach–Dean 2000, p. 25; proof p. 47): for any value function `V`
(with its action selection sets `ρ_V`, `σ_V`), the maps `IVI↓_{opt,V}` and `IVI↑_{pes,V}`
from value functions to value functions are contraction mappings. -/
theorem theorem13b_contraction {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) (V : Q → ℝ) :
    IsContraction (IVIloOptV B V) ∧ IsContraction (IVIhiPesV B V) := by sorry

end BoundedParamMDP.IntervalEval
