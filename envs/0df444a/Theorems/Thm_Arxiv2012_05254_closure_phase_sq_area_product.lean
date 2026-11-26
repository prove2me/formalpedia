-- Prove2me | Theorems.Thm_Arxiv2012_05254_closure_phase_sq_area_product
-- name    : Arxiv2012_05254.closure_phase_sq_area_product
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:16:43.827908+00:00
-- url     : https://prove2.me/theorems/57bc59f1-bb2f-5342-a054-4bc98f99b1bb
-- title:
--   Eq. (19): $\psi_3^2 = 16\pi^2 A_{\mathcal A3} A_{\mathcal I3}$
-- statement:
--   Let $x_0,x_1,x_2$ be the positions (in wavelengths) of a closed triad of non-collinear elements, and let $A_{\mathcal A3}$ be the area of the triangle they form. Let $\psi_{a\lceil a+1\rfloor_3}$ be the phase offsets of three NPCs, with closure phase $\psi_3$. Let $A_{\mathcal I3}$ be the area of the triangle enclosed by the three NPCs in the image plane. Then
--
--   $$\psi_3^2=16\pi^2\,A_{\mathcal A3}\,A_{\mathcal I3}.$$
--
--   So the squared closure phase is measured by the product of the two areas.
--
--   **Formalization Note** The statement holds for any choice of the integers $n_{ab}$ in $\psi_{ab}=\phi_{ab}+2\pi n_{ab}$. The principal triangle is the case $n_{ab}=0$. Areas are unsigned.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c029; Section 3.2, eq. (19), PDF p. 7; derivation Appendix 1, eqs. (21)-(22), PDF p. 16

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem closure_phase_sq_area_product (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) :
    closurePhase ψ ^ 2 = 16 * Real.pi ^ 2 * apertureArea x * imageArea x ψ := by sorry

end Arxiv2012_05254
