-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_interval_policy_evaluation_converges
-- name    : BoundedParamMDP.IntervalEval.interval_policy_evaluation_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:27.653863+00:00
-- url     : https://prove2.me/theorems/66e5a1dd-b150-49a5-b845-6da67bbc1188
-- title:
--   Section 5.1 — iterating $IVI_{\updownarrow\pi}$ from any interval value function converges to $V_{\updownarrow\pi}$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$, finite nonempty action set $A$ and discount rate $0\le\gamma<1$, and let $\pi:Q\to A$ be a policy. Let $V_{\updownarrow\pi}=[V_{\downarrow\pi},V_{\uparrow\pi}]$ be the interval value of $\pi$ (Definition 3): $V_{\downarrow\pi}(q)=\min_{M\in M_\updownarrow}V_{M,\pi}(q)$ and $V_{\uparrow\pi}(q)=\max_{M\in M_\updownarrow}V_{M,\pi}(q)$, the extreme values of $\pi$ over all exact MDPs consistent with the interval bounds.
--
--   Let $V_{\updownarrow 0}=[V_{\downarrow 0},V_{\uparrow 0}]$ be any interval value function, i.e. $V_{\downarrow 0}(q)\le V_{\uparrow 0}(q)$ at every state $q$. Then the iterates of interval policy evaluation converge to the interval value of $\pi$:
--
--   $$\lim_{n\to\infty}IVI_{\updownarrow\pi}^{\,n}(V_{\updownarrow 0})=V_{\updownarrow\pi},$$
--
--   that is, $IVI_{\downarrow\pi}^{\,n}(V_{\downarrow 0})\to V_{\downarrow\pi}$ and $IVI_{\uparrow\pi}^{\,n}(V_{\uparrow 0})\to V_{\uparrow\pi}$ in the sup norm.
--
--   This is the correctness of interval policy evaluation: the tightest interval enclosing the value of $\pi$ in every MDP of the family, an extremum over infinitely many MDPs, is computed by iterating a single dynamic-programming operator from any starting point.
--
--   **Formalization Note.** An interval value function is the pair $(V_{\downarrow},V_{\uparrow})$; convergence is in the product topology on pairs of functions on the finite set $Q$, which is the topology of the sup norm. The limit is the infimum/supremum over member MDPs of Definition 3, not a fixed point of the operator. The hypothesis $V_{\downarrow 0}\le V_{\uparrow 0}$ is the paper's notion of an interval value function; it is not needed for the conclusion.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 22, Section 5.1, the sentence after Theorem 11 (consequence of Theorems 10 and 11 and Theorem 1)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation

namespace BoundedParamMDP.IntervalEval

/-- Section 5.1, p. 22 (consequence of Theorems 10 and 11 and the Banach fixed-point theorem):
for any policy `π`, iterating interval policy evaluation `IVI↕π` on any initial interval value
function `V↕₀ = [V↓₀, V↑₀]` (with `V↓₀ ≤ V↑₀` statewise) converges to the interval value
function `V↕π = [V↓π, V↑π]` of Definition 3. -/
theorem interval_policy_evaluation_converges {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A) (π : BoundedParamMDP.Optimal.Policy Q A)
    (V₀ : (Q → ℝ) × (Q → ℝ)) (hV₀ : V₀.1 ≤ V₀.2) :
    Filter.Tendsto (fun n : ℕ => (IVI B π)^[n] V₀) Filter.atTop
      (nhds (BoundedParamMDP.Optimal.lowerV B π, BoundedParamMDP.Optimal.upperV B π)) := by sorry

end BoundedParamMDP.IntervalEval
