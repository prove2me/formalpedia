-- Prove2me | Theorems.Thm_DynSetValue_DPP_equation_3_6
-- name    : DynSetValue.DPP.equation_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:15.231341+00:00
-- url     : https://prove2.me/theorems/0ec110ba-91b2-4429-b563-0757212b55d0
-- title:
--   Equation (3.6) — uniform positive and inverse density moments
-- statement:
--   Under Assumption 3.1, for every real $p\ge1$ there is a finite constant $C_p$ independent of the admissible control profile $\alpha$ such that
--
--   $$
--   \sup_{\alpha\in\mathcal A}
--   \mathbb E^{\mathbb P_0}\!\left[(M_T^\alpha)^p+(M_T^\alpha)^{-p}\right]\le C_p.
--   $$
--
--   The density here is the one at the zero history and initial time. The estimate controls both large densities and small densities in later comparisons of the changed measures.
--
--   **Formalization Note** The expectation is a nonnegative extended integral, so failure of integrability cannot silently yield a default value of zero.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 25, equation (3.6), proof of Theorem 3.7(i)

import Mathlib
import Definitions.Def_DynSetValue_DPP_Game

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Equation (3.6), p. 25. -/
theorem equation_3_6 {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (G : Game T hT d N) (P0 : Measure (Ω T d))
    (hP0 : IsWiener hT P0) (h31 : Assumption31 G P0)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α : Profile hT G, IsProfile hT G P0 α →
        (∫⁻ ω' : Ω T d, ENNReal.ofReal
          ((M hT G P0 0 (zeroPath T d) α ω') ^ p +
           (M hT G P0 0 (zeroPath T d) α ω') ^ (-p)) ∂P0) ≤ ENNReal.ofReal C := by sorry

end DynSetValue.DPP
