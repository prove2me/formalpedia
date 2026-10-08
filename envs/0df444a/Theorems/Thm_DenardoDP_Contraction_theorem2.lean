-- Prove2me | Theorems.Thm_DenardoDP_Contraction_theorem2
-- name    : DenardoDP.Contraction.theorem2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:56:02.616691+00:00
-- url     : https://prove2.me/theorems/105e300a-db26-4568-86b3-5878dd90de3e
-- title:
--   Theorem 2 — the maximization operator is a contraction
-- statement:
--   Let $A$ be Denardo's maximization operator, so $(Aw)(x)=\sup_{d\in D_x}h(x,d,w)$ is a bounded real function for every $w\in V$. If the return $h$ obeys the contraction assumption with $0\le c<1$, then for all $u,w\in V$,
--
--   $$\rho(Au,Aw)\le c\rho(u,w).$$
--
--   Thus the operator defined by maximizing at each state inherits the contraction modulus of the returns.
--
--   **Formalization Note** `IsMaxOperator` requires a genuine real least upper bound at every state and an output in $V$. The policy operator and monotonicity assumption play no role in this theorem.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 167, Theorem 2 and equation (3); https://doi.org/10.1137/1009030

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.Contraction

/-- Theorem 2, p. 167: the maximization operator inherits the contraction modulus. -/
theorem theorem2 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (A : BFun Ω → BFun Ω)
    (c : ℝ) (hA : IsMaxOperator h A) (hc : ContractionAssumption h c) :
    ModulusLE A c := by sorry

end DenardoDP.Contraction
