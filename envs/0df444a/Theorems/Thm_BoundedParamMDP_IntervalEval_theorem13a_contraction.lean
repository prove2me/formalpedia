-- Prove2me | Theorems.Thm_BoundedParamMDP_IntervalEval_theorem13a_contraction
-- name    : BoundedParamMDP.IntervalEval.theorem13a_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:02.110997+00:00
-- url     : https://prove2.me/theorems/707601ed-bf25-4280-8d9e-91e035c9c178
-- title:
--   Theorem 13(a) — $IVI_{\uparrow opt}$ and $IVI_{\downarrow pes}$ are contraction mappings
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP with finite state set $Q$ and finite nonempty action set $A$. $IVI_{\uparrow opt}$ is the upper bound returned by optimistic interval value iteration $IVI_{\updownarrow opt}$; it depends only on the upper bound $V_\uparrow$ of its input, and is regarded as a map $\overline V\to\overline V$. Likewise $IVI_{\downarrow pes}$, the lower bound returned by $IVI_{\updownarrow pes}$, depends only on $V_\downarrow$.
--
--   **Theorem 13(a).** $IVI_{\uparrow opt}$ and $IVI_{\downarrow pes}$ are contraction mappings. Precisely, there are $\lambda,\lambda'\in[0,1)$ such that for all interval inputs $[L,U]$ and $[L',U']$,
--
--   $$\big\|IVI_{\uparrow opt}([L',U'])-IVI_{\uparrow opt}([L,U])\big\|\le\lambda\,\|U'-U\|,\qquad \big\|IVI_{\downarrow pes}([L',U'])-IVI_{\downarrow pes}([L,U])\big\|\le\lambda'\,\|L'-L\|.$$
--
--   With Theorem 9 this yields convergence of the upper bounds of optimistic (lower bounds of pessimistic) interval value iteration.
--
--   **Formalization Note.** The inequalities are taken over arbitrary pairs of input functions with arbitrary values of the other bound. Taking equal other bounds gives the contraction property of the map on $\overline V$; taking equal relevant bounds gives the independence from the other bound (p. 23) that makes the map on $\overline V$ well defined. Inputs are not required to be proper intervals ($L\le U$).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), DOI 10.1016/S0004-3702(00)00047-3, manuscript of May 22, 2000, p. 25, Theorem 13(a) (proof pp. 45–47); IVI↑opt as a map on value functions, p. 23

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalValueIteration

namespace BoundedParamMDP.IntervalEval

/-- Theorem 13(a) (Givan–Leach–Dean 2000, p. 25; proof pp. 45–47): `IVI↑opt` and `IVI↓pes` are
contraction mappings. `IVI↑opt` is the upper bound returned by `IVI↕opt`, regarded as a map
`V̄ → V̄` of the upper input `V↑` (it does not depend on the lower input, p. 23); `IVI↓pes`
likewise is the lower bound returned by `IVI↕pes` as a map of the lower input `V↓`. The
statement bounds the outputs for two arbitrary interval inputs by `λ` times the distance of
the relevant input bounds only: this is the contraction property together with the
independence from the other bound that makes the maps well defined on `V̄`. -/
theorem theorem13a_contraction {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) :
    (∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ L L' U U' : Q → ℝ,
      ‖(fun p => (IVIopt B (L', U') p).2) - (fun p => (IVIopt B (L, U) p).2)‖ ≤
        c * ‖U' - U‖) ∧
    (∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ L L' U U' : Q → ℝ,
      ‖(fun p => (IVIpes B (L', U') p).1) - (fun p => (IVIpes B (L, U) p).1)‖ ≤
        c * ‖L' - L‖) := by sorry

end BoundedParamMDP.IntervalEval
