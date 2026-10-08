-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_theorem10_contraction
-- name    : BoundedParamMDP.IntervalEval.theorem10_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:56.149984+00:00
-- url     : https://prove2.me/theorems/a4dfdbf9-a414-42ad-84d5-c015d29f0206
-- title:
--   Theorem 10 — $IVI_{\downarrow\pi}$ and $IVI_{\uparrow\pi}$ are contraction mappings
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$ and finite nonempty action set $A$, and let $\pi:Q\to A$ be a policy. Consider the lower- and upper-bound operators of interval policy evaluation, as maps on the space $\overline V$ of value functions with the sup norm $\|v\|=\max_{q}|v(q)|$:
--
--   $$IVI_{\downarrow\pi}(v)(p)=\min_{M\in M_\updownarrow}VI_{M,\pi}(v)(p),\qquad IVI_{\uparrow\pi}(v)(p)=\max_{M\in M_\updownarrow}VI_{M,\pi}(v)(p).$$
--
--   **Theorem 10.** Both $IVI_{\downarrow\pi}$ and $IVI_{\uparrow\pi}$ are contraction mappings: for each of them, $T$, there is $\lambda\in[0,1)$ with
--
--   $$\|T v-T u\|\le\lambda\,\|v-u\|\qquad\text{for all }u,v\in\overline V.$$
--
--   Together with Theorem 11 and the Banach fixed-point theorem, this gives the convergence of interval policy evaluation.
--
--   **Formalization Note.** The statement asserts the existence of a modulus, as the paper's notion of contraction mapping does; it does not fix the modulus to $\gamma$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 21, Theorem 10 (restated with proof pp. 43–44)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation

namespace BoundedParamMDP.IntervalEval

/-- Theorem 10 (Givan–Leach–Dean 2000, p. 21; restated p. 43): for any policy `π`, the
interval policy evaluation operators `IVI↓π` and `IVI↑π`, viewed as maps from value functions
to value functions, are contraction mappings for the sup norm. -/
theorem theorem10_contraction {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) (π : BoundedParamMDP.Optimal.Policy Q A) :
    IsContraction (IVIlo B π) ∧ IsContraction (IVIhi B π) := by sorry

end BoundedParamMDP.IntervalEval
