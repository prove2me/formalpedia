-- Prove2me | Theorems.Thm_Arxiv1506_07229_slab_boundary_solution
-- name    : Arxiv1506_07229.slab_boundary_solution
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:05:18.565263+00:00
-- url     : https://prove2.me/theorems/8851f530-3e07-4583-866b-633c48021c84
-- title:
--   Eqs. (B3)-(B4): solution of the slab boundary conditions
-- statement:
--   Let a slab of thickness $a>0$ with local permittivity $\varepsilon\neq0$ lie in vacuum, let $q>0$, and assume $1+e^{aq}+\varepsilon(e^{aq}-1)\neq0$. Then the coefficients
--
--   $$A_2=B_2=\frac{\varepsilon-1}{\varepsilon}\,\frac{e^{aq/2}}{1+e^{aq}+\varepsilon(e^{aq}-1)},\qquad A_1=B_3=\varepsilon(1-e^{aq})A_2$$
--
--   of Eq. (B4) satisfy the boundary conditions (B3). If moreover $\varepsilon(e^{aq}+1)+e^{aq}-1\neq0$, they are the only solution of (B3).
--
--   **Formalization Note** The determinant of the linear system (B3) is proportional to $[1+e^{aq}+\varepsilon(e^{aq}-1)]\,[\varepsilon(e^{aq}+1)+e^{aq}-1]$. The paper calls (B4) "the solution" without stating that the second factor must be nonzero. When it vanishes ($\varepsilon=-\tanh(aq/2)$), (B4) is still a solution but not the only one. The uniqueness clause therefore carries this extra hypothesis. The first factor is the denominator of (B4).
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c018; Appendix B, Eqs. (B2)-(B4), PDF p. 6-7

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem slab_boundary_solution (eps : ℂ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q) (he : eps ≠ 0)
    (hD : 1 + (Real.exp (a * q) : ℂ) + eps * ((Real.exp (a * q) : ℂ) - 1) ≠ 0) :
    slabBC eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q) ∧
      (eps * ((Real.exp (a * q) : ℂ) + 1) + ((Real.exp (a * q) : ℂ) - 1) ≠ 0 →
        ∀ A1 A2 B2 B3 : ℂ, slabBC eps a q A1 A2 B2 B3 →
          A1 = slabA1 eps a q ∧ A2 = slabA2 eps a q ∧ B2 = slabA2 eps a q ∧ B3 = slabA1 eps a q) := by sorry

end Arxiv1506_07229
