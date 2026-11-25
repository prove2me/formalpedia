-- Prove2me | Theorems.Thm_Arxiv2012_05254_polygon_pattern_not_sos_conserved
-- name    : Arxiv2012_05254.polygon_pattern_not_sos_conserved
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T04:49:56.397158+00:00
-- url     : https://prove2.me/theorems/8f3858a0-a049-436c-8105-0e7f34d878e2
-- title:
--   App. 2 (Fig. 11): for $N\ge4$ the whole NPC pattern is not SOS-conserved, its elemental triads are, and $A_{\mathcal I4}\ne\sum_q A_{\mathcal I3(q)}$
-- statement:
--   Let $N\ge4$ elements at positions $x_0,\dots,x_{N-1}$ form a closed $N$-polygon in which no three consecutive elements are collinear. Let $\psi_{ab}$ be NPC phase offsets with $\psi_{ba}=-\psi_{ab}$.
--
--   1. Corrupting the phase of any single element by $\delta\ne0$ does not translate the NPC pattern of the polygon: the pattern is distorted, not shifted.
--   2. For any element phase corruption, the NPC pattern of every non-degenerate elemental triad $(0,q,q+1)$ is translated, so each triad obeys SOS conservation.
--   3. The area enclosed by the NPCs of a 4-polygon is not in general the sum of the areas enclosed by the NPCs of its two elemental triads. There is a 4-polygon, with no three consecutive elements collinear and non-degenerate triads, for which $A_{\mathcal I4}\ne A_{\mathcal I3(1)}+A_{\mathcal I3(2)}$.
--
--   **Formalization Note** $A_{\mathcal I4}$ is the area of the convex hull of the four points where consecutive NPCs meet. The paper describes it only as the area enclosed by the four NPCs (Fig. 11).
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c024; Appendix 2 and Fig. 11, PDF pp. 17-18

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem polygon_pattern_not_sos_conserved {M : ℕ} (hM : 2 ≤ M) (x : Fin (M + 2) → Plane)
    (hx3 : ∀ a : Fin (M + 2), AffineIndependent ℝ ![x a, x (a + 1), x (a + 2)])
    (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b) :
    (∀ (e : Fin (M + 2)) (δ : ℝ), δ ≠ 0 →
      ¬ ∃ t : Plane, npcTranslate x (loopPhase ψ id)
        (elementCorrupt (Pi.single e δ : Fin (M + 2) → ℝ) (loopPhase ψ id)) t) ∧
    (∀ (ξ : Fin (M + 2) → ℝ) (q : Fin M), AffineIndependent ℝ (x ∘ fanTriad q) →
      ∃ t : Plane, npcTranslate (x ∘ fanTriad q) (loopPhase ψ (fanTriad q))
        (elementCorrupt (ξ ∘ fanTriad q) (loopPhase ψ (fanTriad q))) t) ∧
    ∃ (y : Fin (2 + 2) → Plane) (φ : Fin (2 + 2) → Fin (2 + 2) → ℝ),
      (∀ a b, φ b a = -φ a b) ∧
      (∀ a : Fin (2 + 2), AffineIndependent ℝ ![y a, y (a + 1), y (a + 2)]) ∧
      (∀ q : Fin 2, AffineIndependent ℝ (y ∘ fanTriad q)) ∧
      imageArea y (loopPhase φ id) ≠
        ∑ q : Fin 2, imageArea (y ∘ fanTriad q) (loopPhase φ (fanTriad q)) := by sorry

end Arxiv2012_05254
