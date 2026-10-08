-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_theorem11_fixed_points
-- name    : BoundedParamMDP.IntervalEval.theorem11_fixed_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:06.847602+00:00
-- url     : https://prove2.me/theorems/e5b8acfd-aa2f-444b-832a-2d995b4592b4
-- title:
--   Theorem 11 — $V_{\downarrow\pi}$, $V_{\uparrow\pi}$ and $V_{\updownarrow\pi}$ are fixed points of interval policy evaluation
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$ and finite nonempty action set $A$, and let $\pi$ be a policy. Let $V_{\downarrow\pi}(q)=\min_{M\in M_\updownarrow}V_{M,\pi}(q)$ and $V_{\uparrow\pi}(q)=\max_{M\in M_\updownarrow}V_{M,\pi}(q)$ be the bounds of the interval value $V_{\updownarrow\pi}$ of Definition 3.
--
--   **Theorem 11.** $V_{\downarrow\pi}$ is a fixed point of $IVI_{\downarrow\pi}$, $V_{\uparrow\pi}$ is a fixed point of $IVI_{\uparrow\pi}$, and therefore $V_{\updownarrow\pi}$ is a fixed point of $IVI_{\updownarrow\pi}$:
--
--   $$\min_{M\in M_\updownarrow}VI_{M,\pi}(V_{\downarrow\pi})=V_{\downarrow\pi},\qquad \max_{M\in M_\updownarrow}VI_{M,\pi}(V_{\uparrow\pi})=V_{\uparrow\pi},\qquad IVI_{\updownarrow\pi}(V_{\updownarrow\pi})=V_{\updownarrow\pi}.$$
--
--   This identifies the interval value of Definition 3, defined through the value functions of the (infinitely many) member MDPs, with the fixed point of the interval operator.
--
--   **Formalization Note.** $V_{\downarrow\pi}$ and $V_{\uparrow\pi}$ are the infimum and supremum over the member MDPs of the discounted-series value functions; they are not defined as fixed points. The interval value function $V_{\updownarrow\pi}$ is the pair $(V_{\downarrow\pi},V_{\uparrow\pi})$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 22, Theorem 11 (restated with proof pp. 44–45)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation

namespace BoundedParamMDP.IntervalEval

/-- Theorem 11 (Givan–Leach–Dean 2000, p. 22; restated p. 44): for any policy `π`, the lower
bound `V↓π` of the interval value (Definition 3) is a fixed point of `IVI↓π`, the upper bound
`V↑π` is a fixed point of `IVI↑π`, and therefore `V↕π = [V↓π, V↑π]` is a fixed point of
`IVI↕π`. -/
theorem theorem11_fixed_points {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A) (π : BoundedParamMDP.Optimal.Policy Q A) :
    IVIlo B π (BoundedParamMDP.Optimal.lowerV B π) = BoundedParamMDP.Optimal.lowerV B π ∧
    IVIhi B π (BoundedParamMDP.Optimal.upperV B π) = BoundedParamMDP.Optimal.upperV B π ∧
    IVI B π (BoundedParamMDP.Optimal.lowerV B π, BoundedParamMDP.Optimal.upperV B π) =
      (BoundedParamMDP.Optimal.lowerV B π, BoundedParamMDP.Optimal.upperV B π) := by sorry

end BoundedParamMDP.IntervalEval
