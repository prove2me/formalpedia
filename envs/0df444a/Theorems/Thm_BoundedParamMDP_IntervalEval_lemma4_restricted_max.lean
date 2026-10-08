-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_lemma4_restricted_max
-- name    : BoundedParamMDP.IntervalEval.lemma4_restricted_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:45.925993+00:00
-- url     : https://prove2.me/theorems/300f4f1a-0bf2-4e21-a593-480e8993f895
-- title:
--   Lemma 4 — $IVI_{\downarrow opt,V}$ and $IVI_{\uparrow pes,V}$ as maxima over $\rho_V(p)$ and $\sigma_V(p)$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$ and finite nonempty action set $A$, and let $\rho_V,\sigma_V$, $IVI_{\downarrow opt,V}$ and $IVI_{\uparrow pes,V}$ be as in the definitions of interval value iteration.
--
--   **Lemma 4.** For any value functions $V,V'$ and state $p$,
--
--   $$IVI_{\downarrow opt,V}(V')(p)=\max_{\alpha\in\rho_V(p)}\ \min_{M\in M_\updownarrow}VI_{M,\alpha}(V')(p),\qquad IVI_{\uparrow pes,V}(V')(p)=\max_{\alpha\in\sigma_V(p)}\ \max_{M\in M_\updownarrow}VI_{M,\alpha}(V')(p).$$
--
--   It isolates how the action choice of $IVI_{\updownarrow opt}$ (respectively $IVI_{\updownarrow pes}$) is driven by the fixed bound $V$, and is the form used to show that these operators contract.
--
--   **Formalization Note.** The paper prints the inner operator of the second line as $\min_{M\in M_\updownarrow}$. Since $IVI_{\uparrow pes,V}$ is an upper bound, eq. (29) and the proof of Theorem 13(b) (p. 47) make it $\max_{M\in M_\updownarrow}$, which is what is stated here. Each "$\max_{\alpha\in S}$" is stated as: the value is the greatest element of the set $\{f(\alpha):\alpha\in S\}$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 25, Lemma 4, eq. (32) (second line misprinted min corrected to max)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalValueIteration

namespace BoundedParamMDP.IntervalEval

/-- Lemma 4 (Givan–Leach–Dean 2000, p. 25, eq. (32)), with the misprinted `min` of the second
line read as `max`: for any value functions `V, V'` and state `p`,
`IVI↓_{opt,V}(V')(p) = max_{α ∈ ρ_V(p)} min_{M ∈ M↕} VI_{M,α}(V')(p)` and
`IVI↑_{pes,V}(V')(p) = max_{α ∈ σ_V(p)} max_{M ∈ M↕} VI_{M,α}(V')(p)`; each maximum over a set
of actions is stated as "the greatest element of the set of values". -/
theorem lemma4_restricted_max {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) (V V' : Q → ℝ) (p : Q) :
    IsGreatest ((fun α => ⨅ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V' p) '' rho B V p)
      (IVIloOptV B V V' p) ∧
    IsGreatest ((fun α => ⨆ M : BoundedParamMDP.Optimal.Member B, BoundedParamMDP.Optimal.VIact M.1 α V' p) '' sigma B V p)
      (IVIhiPesV B V V' p) := by sorry

end BoundedParamMDP.IntervalEval
