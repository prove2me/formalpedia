-- Prove2me | Theorems.Thm_Arxiv2012_05254_single_element_error_slides_pattern
-- name    : Arxiv2012_05254.single_element_error_slides_pattern
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:59:49.420125+00:00
-- url     : https://prove2.me/theorems/82e8af53-8f04-56ad-8923-ef2a1cc999e1
-- title:
--   Sec. 4.2 (Fig. 7): a single-element error slides the triangle along the uncorrupted fringe; shifts compose
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with NPC phase offsets $\psi_{a\lceil a+1\rfloor_3}$.
--
--   1. If only the phase of element $e$ is corrupted, by any amount $\delta$, the NPC pattern is translated by a vector $t$ parallel to the NPC of the uncorrupted side $(e+1,e+2)$: $u_{e+1,e+2}\cdot t=0$. The triangle slides along the uncorrupted fringe.
--   2. Shifts compose. Suppose corrupting by element phases $\xi$ translates the pattern by $t$, and then corrupting the result by $\xi'$ translates it by $t'$. Then corrupting the original by $\xi+\xi'$ translates it by $t+t'$. So the shift caused by several corrupted elements is obtained by applying the single-element shifts one after another.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c032; Section 4.2 and Fig. 7 (middle and right panels), PDF pp. 11-12

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem single_element_error_slides_pattern (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (e : Fin 3) (δ : ℝ) :
    (∃ t : Plane, ⟪spacing x (e + 1), t⟫ = 0 ∧
      npcTranslate x ψ (elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ) t) ∧
    ∀ (ξ ξ' : Fin 3 → ℝ) (t t' : Plane),
      npcTranslate x ψ (elementCorrupt ξ ψ) t →
      npcTranslate x (elementCorrupt ξ ψ) (elementCorrupt ξ' (elementCorrupt ξ ψ)) t' →
      npcTranslate x ψ (elementCorrupt (ξ + ξ') ψ) (t + t') := by sorry

end Arxiv2012_05254
