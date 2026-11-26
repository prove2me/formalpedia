-- Prove2me | Theorems.Thm_Arxiv2012_05254_single_element_error_shifts_fringes
-- name    : Arxiv2012_05254.single_element_error_shifts_fringes
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:55:45.867855+00:00
-- url     : https://prove2.me/theorems/6f295bb9-c7a6-405d-82b4-69f8e9262f06
-- title:
--   Sec. 3.3: a single-element phase error shifts two fringes by $\delta\xi_a/(2\pi|u_{ab}|)$ and translates the pattern
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with NPC phase offsets $\psi_{a\lceil a+1\rfloor_3}$. Corrupt the phase of one element $e$ by $\delta\xi_e=\delta$ and leave the others unchanged. By eq. (5):
--
--   1. the side not containing $e$ keeps its phase, $\tilde\psi_{e+1,e+2}=\psi_{e+1,e+2}$;
--   2. the two sides containing $e$ change by equal and opposite amounts: $\tilde\psi_{e,e+1}=\psi_{e,e+1}-\delta$ and $\tilde\psi_{e-1,e}=\psi_{e-1,e}+\delta$;
--   3. each of these two NPCs is displaced perpendicular to itself by a distance
--
--   $$\Delta s_{ab}=\frac{|\delta\xi_e|}{2\pi\,|u_{ab}|};$$
--
--   4. the whole three-NPC pattern is translated by one vector $t$, which conserves its shape, orientation and size.
--
--   **Formalization Note** The paper's argument tilts the aperture plane and holds, per its footnote, for path-length changes small compared with the baselines. The statement here concerns the NPCs defined by eqs. (5) and (7), which hold exactly for every $\delta$. Indices are mod 3.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c006; Section 3.3 and Fig. 4, eq. (8), PDF pp. 7-8

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem single_element_error_shifts_fringes (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (e : Fin 3) (δ : ℝ) :
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ (e + 1) = ψ (e + 1) ∧
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ e = ψ e - δ ∧
    elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ (e + 2) = ψ (e + 2) + δ ∧
    (∀ a ∈ ({e, e + 2} : Finset (Fin 3)), ∃ w : Plane, (∃ c : ℝ, w = c • spacing x a) ∧
      ‖w‖ = |δ| / (2 * Real.pi * ‖spacing x a‖) ∧
      npc (spacing x a) (elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ a) =
        (fun s => s + w) '' npc (spacing x a) (ψ a)) ∧
    ∃ t : Plane, npcTranslate x ψ (elementCorrupt (Pi.single e δ : Fin 3 → ℝ) ψ) t := by sorry

end Arxiv2012_05254
