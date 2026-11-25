-- Prove2me | Theorems.Thm_Arxiv2012_05254_npc_translation_iff_element_based
-- name    : Arxiv2012_05254.npc_translation_iff_element_based
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:05:58.860368+00:00
-- url     : https://prove2.me/theorems/875e7ef1-c452-47ab-95ad-cc040bf2db09
-- title:
--   Sec. 4.1: the NPC pattern of a triad is translated exactly when the phase error is element-based
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with NPC phase offsets $\psi_{a\lceil a+1\rfloor_3}$. Add arbitrary phase errors $c_a$ to the three sides. The following are equivalent:
--
--   1. the corrupted NPC pattern is a translate of the original one;
--   2. the errors are element-based: $c_a=\xi_{\lceil a+1\rfloor_3}-\xi_a$ for some element phases $\xi$;
--   3. the closure phase is unchanged.
--
--   This is the geometric criterion separating element-based from baseline-based corruptions. Element-based errors translate the fringes and conserve the SOS of the triangle. Any other error changes the closure phase, and the pattern is then no longer a translate.
--
--   **Formalization Note** The paper's proposed diagnostic use (needing a source model or a redundant array), and its remark that a miscalculated spacing vector can change any of the SOS parameters, are not part of the statement.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c036; Section 4.1, fourth conclusion of the 3C 286 analysis, PDF p. 10; Section 5, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem npc_translation_iff_element_based (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ c : Fin 3 → ℝ) :
    ((∃ t : Plane, npcTranslate x ψ (ψ + c) t) ↔ ∃ ξ : Fin 3 → ℝ, ∀ a, c a = ξ (a + 1) - ξ a) ∧
    ((∃ t : Plane, npcTranslate x ψ (ψ + c) t) ↔ closurePhase (ψ + c) = closurePhase ψ) := by sorry

end Arxiv2012_05254
