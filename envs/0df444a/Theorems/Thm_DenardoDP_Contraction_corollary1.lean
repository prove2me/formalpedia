-- Prove2me | Theorems.Thm_DenardoDP_Contraction_corollary1
-- name    : DenardoDP.Contraction.corollary1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:56:04.446509+00:00
-- url     : https://prove2.me/theorems/0e19b4e5-ce21-4482-8384-03bb51ee5be8
-- title:
--   Corollary 1 — approximate policies and exact-policy criterion
-- statement:
--   Let $v^*$ solve Denardo's functional equation $Av^*=v^*$, and let $v_\delta$ be the fixed-point return of policy $\delta$. Under the contraction assumption, for every $\varepsilon>0$ there is a policy $\delta$ with
--
--   $$\rho(H_\delta v^*,v^*)\le\varepsilon(1-c).$$
--
--   Every policy satisfying this bound has $\rho(v_\delta,v^*)\le\varepsilon$. If a policy has zero residual, then its return equals $v^*$ exactly. This gives policies whose returns approximate the solution of the functional equation.
--
--   **Formalization Note** The fixed point $v^*$ is supplied as a solution of equation (4), whose existence and uniqueness are a separate milestone. The operators map $V$ to $V$; their pointwise definitions and the real suprema are explicit. The family $v_\delta$ is supplied by equation (2).
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), pp. 167–168, Corollary 1; https://doi.org/10.1137/1009030

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.Contraction

/-- Corollary 1, p. 167: approximate policies and an exact-policy criterion. -/
theorem corollary1 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (A : BFun Ω → BFun Ω) (c : ℝ)
    (v : ((x : Ω) → D x) → BFun Ω) (vstar : BFun Ω)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hc : ContractionAssumption h c)
    (hv : ∀ δ, H δ (v δ) = v δ) (hstar : A vstar = vstar) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar ≤ ε * (1 - c)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar ≤ ε * (1 - c) → dist (v δ) vstar ≤ ε) ∧
    (∀ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar = 0 → v δ = vstar) := by sorry

end DenardoDP.Contraction
