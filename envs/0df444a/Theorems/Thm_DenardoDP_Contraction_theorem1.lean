-- Prove2me | Theorems.Thm_DenardoDP_Contraction_theorem1
-- name    : DenardoDP.Contraction.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:55:32.218099+00:00
-- url     : https://prove2.me/theorems/20483154-d867-4eb7-b1f6-025d2965a285
-- title:
--   Theorem 1 — policy return residual bound
-- statement:
--   Under Denardo's contraction assumption with $0\le c<1$, let $v_\delta$ be the return function of policy $\delta$, meaning $H_\delta v_\delta=v_\delta$. For every policy $\delta$ and every bounded value function $w\in V$,
--
--   $$\rho(v_\delta,w)\le\frac{\rho(H_\delta w,w)}{1-c}.$$
--
--   The inequality bounds the distance from an arbitrary continuation value to a policy's return using its residual under that policy.
--
--   **Formalization Note** The policy operator is tied to the return function $h$ by equation (1) and maps $V$ into $V$. The family $v_\delta$ is supplied through equation (2); under the contraction assumption, each member exists uniquely. The factor $1-c$ is positive.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 167, Theorem 1; https://doi.org/10.1137/1009030

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.Contraction

/-- Theorem 1, p. 167: the residual bound for the policy return. -/
theorem theorem1 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (c : ℝ) (v : ((x : Ω) → D x) → BFun Ω)
    (hH : IsPolicyOperator h H) (hc : ContractionAssumption h c)
    (hv : ∀ δ, H δ (v δ) = v δ) :
    ∀ (δ : (x : Ω) → D x) (w : BFun Ω),
      dist (v δ) w ≤ dist (H δ w) w / (1 - c) := by sorry

end DenardoDP.Contraction
