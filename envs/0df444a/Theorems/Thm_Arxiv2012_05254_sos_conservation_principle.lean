-- Prove2me | Theorems.Thm_Arxiv2012_05254_sos_conservation_principle
-- name    : Arxiv2012_05254.sos_conservation_principle
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T04:02:51.3858+00:00
-- url     : https://prove2.me/theorems/906dbc00-4393-5271-8830-dc2c99b460f8
-- title:
--   SOS conservation principle (Sec. 3.1): element-based corruption only translates the principal triangle
-- statement:
--   **Shape-orientation-size (SOS) conservation principle.** Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with spacings $u_{a\lceil a+1\rfloor_3}$. Let $\psi_{a\lceil a+1\rfloor_3}$ be the phase offsets of the three NPCs, whose triangle is the principal triangle when the $\psi$ are the principal phases. Corrupt the measurement by arbitrary element phases $\xi_0,\xi_1,\xi_2$, so that $\tilde\psi_{a\lceil a+1\rfloor_3}=\psi_{a\lceil a+1\rfloor_3}+\xi_{\lceil a+1\rfloor_3}-\xi_a$ (eq. 5). Then:
--
--   1. there is a vector $t$ such that each corrupted NPC is the translate by $t$ of the corresponding uncorrupted NPC, and the triangle enclosed by the corrupted NPCs is the translate by $t$ of the original triangle;
--   2. the closure phase is unchanged: $\tilde\psi_3=\psi_3$;
--   3. the area of the enclosed triangle is unchanged: $A_{\mathcal I3}(\tilde\psi)=A_{\mathcal I3}(\psi)$.
--
--   Hence the shape, the orientation and the size of the triangle are conserved under element-based phase corruption of any magnitude. The only remaining freedom is an overall translation.
--
--   **Formalization Note** The corrupted phases are the real numbers of eq. (5), so each NPC keeps its index $n_{ab}$. If the corrupted phases were instead reduced to principal values in $(-\pi,\pi]$, the principal triangle could change: the principal closure phase can jump by a multiple of $2\pi$. See the mission report.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c003; Section 3.1, paragraph after eq. (18) and discussion of Fig. 3(b), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem sos_conservation_principle (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ ξ : Fin 3 → ℝ) :
    (∃ t : Plane, npcTranslate x ψ (elementCorrupt ξ ψ) t ∧
      npcVertices x (elementCorrupt ξ ψ) = (fun s => s + t) '' npcVertices x ψ) ∧
    closurePhase (elementCorrupt ξ ψ) = closurePhase ψ ∧
    imageArea x (elementCorrupt ξ ψ) = imageArea x ψ := by sorry

end Arxiv2012_05254
