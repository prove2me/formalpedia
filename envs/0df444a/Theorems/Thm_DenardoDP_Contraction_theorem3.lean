-- Prove2me | Theorems.Thm_DenardoDP_Contraction_theorem3
-- name    : DenardoDP.Contraction.theorem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:56:21.582699+00:00
-- url     : https://prove2.me/theorems/1322e09d-0bf9-429e-8538-7eefd1979f84
-- title:
--   Theorem 3 — the functional-equation solution is the optimal return
-- statement:
--   Suppose Denardo's contraction and monotonicity assumptions both hold. For every policy $\delta$, let $v_\delta$ be its return function, the unique fixed point of $H_\delta$. The maximization operator $A$ then has exactly one fixed point $v^*\in V$, and this solution is the optimal return function $f$, defined pointwise over all policies:
--
--   $$Av^*=v^*,\qquad v^*(x)=f(x)=\sup_{\delta\in\Delta}v_\delta(x)\quad(x\in\Omega).$$
--
--   The theorem identifies the solution of the functional equation with the best policy return at every state. Its monotonicity assumption matters: the paper gives a contraction that violates monotonicity for which the two functions can differ.
--
--   **Formalization Note** The policy operators and $A$ are supplied as maps $V\to V$ constrained by equations (1) and (3), recording the paper's bounded-range assumptions. The family $v_\delta$ is supplied through equation (2), which has a unique solution for each policy under contraction. The formal statement includes existence and uniqueness of the fixed point and uses a real least-upper-bound predicate for the supremum of policy returns. `IsMaxOperator` enforces nonempty decision sets wherever a state exists.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 168, Theorem 3, with definitions on pp. 166–167; https://doi.org/10.1137/1009030

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.Contraction

/-- Theorem 3, p. 168: the unique functional-equation solution is the optimal return. -/
theorem theorem3 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (A : BFun Ω → BFun Ω) (c : ℝ)
    (v : ((x : Ω) → D x) → BFun Ω)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hc : ContractionAssumption h c) (hmono : MonotonicityAssumption H)
    (hv : ∀ δ, H δ (v δ) = v δ) :
    (∃! w : BFun Ω, A w = w) ∧
      ∀ w : BFun Ω, A w = w → IsOptimalReturn v w := by sorry

end DenardoDP.Contraction
