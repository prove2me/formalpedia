-- Prove2me | Theorems.Thm_DenardoDP_Contraction_equation4
-- name    : DenardoDP.Contraction.equation4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:56:02.948618+00:00
-- url     : https://prove2.me/theorems/cc4b119f-1d1e-4aa9-aafc-f53a3da83875
-- title:
--   Equation (4) — a unique solution of the functional equation
-- statement:
--   Under Denardo's contraction assumption, the maximization operator $A$ has exactly one fixed point $v^*\in V$. Equivalently, the functional equation
--
--   $$v^*(x)=\sup_{d\in D_x}h(x,d,v^*)\qquad(x\in\Omega)$$
--
--   has exactly one bounded solution. This defines the equation's solution independently of the supremum of policy returns.
--
--   **Formalization Note** `IsMaxOperator` states both the pointwise least-upper-bound equation and the paper's assumption that $A$ maps bounded functions to bounded functions.
-- source:
--   Denardo, Contraction Mappings in the Theory Underlying Dynamic Programming, SIAM Review 9(2) (1967), p. 167, equation (4) and preceding sentence; https://doi.org/10.1137/1009030

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

namespace DenardoDP.Contraction

/-- Equation (4), p. 167: existence and uniqueness of its solution in `V`. -/
theorem equation4 {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (A : BFun Ω → BFun Ω)
    (c : ℝ) (hA : IsMaxOperator h A) (hc : ContractionAssumption h c) :
    ∃! w : BFun Ω, A w = w := by sorry

end DenardoDP.Contraction
