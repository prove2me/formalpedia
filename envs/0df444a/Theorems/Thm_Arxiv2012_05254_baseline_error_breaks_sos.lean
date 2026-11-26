-- Prove2me | Theorems.Thm_Arxiv2012_05254_baseline_error_breaks_sos
-- name    : Arxiv2012_05254.baseline_error_breaks_sos
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:10:50.013236+00:00
-- url     : https://prove2.me/theorems/3c7c31b1-4bf2-48fa-8795-ac1637cd03cc
-- title:
--   Sec. 4.1 (Fig. 5 right, as proved): a single-baseline phase error moves one NPC and breaks SOS conservation
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with NPC phase offsets $\psi_{b\lceil b+1\rfloor_3}$ and closure phase $\psi_3$. Add a phase error $\beta\ne0$ to one side $a$ only. Then:
--
--   1. the NPCs of the other two sides are unchanged;
--   2. the closure phase changes to $\psi_3+\beta$;
--   3. the new NPC pattern is not a translate of the old one, so SOS conservation fails;
--   4. if $\psi_3\ne0$, the new triangle is the image of the old one under the homothety centred at the vertex $\hat s_0$ opposite side $a$, with ratio $(\psi_3+\beta)/\psi_3$, so the directions of its sides are unchanged;
--   5. the area of the triangle changes if and only if $\beta\ne-2\psi_3$.
--
--   **Formalization Note** The paper says such an error "will change the size of the triangle". This holds except when $\beta=-2\psi_3$. In that case the new triangle is the point reflection of the old one through the vertex $\hat s_0$: it has the same size and side directions, and the closure phase changes sign. Item 5 states what the argument proves.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c031; Section 4.1, counter-example of Fig. 5 (right panel), PDF pp. 9-10

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem baseline_error_breaks_sos (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (a : Fin 3) (β : ℝ) (hβ : β ≠ 0) :
    (∀ b, b ≠ a → npc (spacing x b) (Function.update ψ a (ψ a + β) b) = npc (spacing x b) (ψ b)) ∧
    closurePhase (Function.update ψ a (ψ a + β)) = closurePhase ψ + β ∧
    (¬ ∃ t : Plane, npcTranslate x ψ (Function.update ψ a (ψ a + β)) t) ∧
    (closurePhase ψ ≠ 0 →
      ∀ V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2)),
        npcVertices x (Function.update ψ a (ψ a + β)) =
          ⇑(AffineMap.homothety V ((closurePhase ψ + β) / closurePhase ψ)) '' npcVertices x ψ) ∧
    (imageArea x (Function.update ψ a (ψ a + β)) ≠ imageArea x ψ ↔ β ≠ -2 * closurePhase ψ) := by sorry

end Arxiv2012_05254
