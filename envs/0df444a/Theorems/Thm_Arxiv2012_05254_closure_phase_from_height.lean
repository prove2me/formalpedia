-- Prove2me | Theorems.Thm_Arxiv2012_05254_closure_phase_from_height
-- name    : Arxiv2012_05254.closure_phase_from_height
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:49:40.21435+00:00
-- url     : https://prove2.me/theorems/da5a2240-1cfc-54f1-b0f4-de0c7c868dec
-- title:
--   Eq. (18): the closure phase is $2\pi|u|$ times a height of the principal triangle
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with spacings $u_{a\lceil a+1\rfloor_3}$. Let $\psi_{a\lceil a+1\rfloor_3}$ be the phase offsets of three NPCs, with closure phase $\psi_3=\sum_a\psi_{a\lceil a+1\rfloor_3}$. Fix a side $a$. The NPCs of the two other sides meet in a point $\hat s_0$, a vertex of the triangle enclosed by the NPCs. For every such vertex:
--
--   1. with $\hat s_0$ as phase centre, the two NPCs through it have phase offset $0$ (eq. 17);
--   2. the closure phase equals the phase offset of the remaining NPC measured from $\hat s_0$:
--
--   $$\psi_3=\psi'_{a\lceil a+1\rfloor_3}=\psi_{a\lceil a+1\rfloor_3}+2\pi\,u_{a\lceil a+1\rfloor_3}\cdot\hat s_0;$$
--
--   3. in terms of the height $\delta s'_{a\lceil a+1\rfloor_3}$ of the triangle drawn from $\hat s_0$ to the opposite side (eq. 18):
--
--   $$|\psi_3|=2\pi\,|u_{a\lceil a+1\rfloor_3}|\,\delta s'_{a\lceil a+1\rfloor_3}.$$
--
--   So one measurement of any one height of the triangle gives the closure phase, up to its sign.
--
--   **Formalization Note** The height is the distance from the vertex to the line of the opposite NPC. The paper's signed relation $\psi_3=2\pi|u|\,\delta s'$ is stated as item 2 together with the unsigned item 3. Non-collinearity of the elements is the paper's footnote d, which excludes collinear triads.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c002; Section 3.1, eqs. (17)-(18), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem closure_phase_from_height (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (a : Fin 3) :
    (∃ V : Plane, V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2))) ∧
    ∀ V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2)),
      recentredPhase (spacing x (a + 1)) (ψ (a + 1)) V = 0 ∧
      recentredPhase (spacing x (a + 2)) (ψ (a + 2)) V = 0 ∧
      closurePhase ψ = recentredPhase (spacing x a) (ψ a) V ∧
      |closurePhase ψ| =
        2 * Real.pi * ‖spacing x a‖ * Metric.infDist V (npc (spacing x a) (ψ a)) := by sorry

end Arxiv2012_05254
