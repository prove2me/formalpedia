-- Prove2me | Theorems.Thm_Arxiv2012_05254_polygon_area_from_triad_closure_phases
-- name    : Arxiv2012_05254.polygon_area_from_triad_closure_phases
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T04:56:47.967949+00:00
-- url     : https://prove2.me/theorems/5aaa0a4d-2de3-469e-83ca-1e3eeee6666e
-- title:
--   Eq. (28) (as proved): the aperture area of an $N$-polygon from elemental-triad closure phases
-- statement:
--   Let $N\ge3$ elements at positions $x_0,\dots,x_{N-1}$ form a closed $N$-polygon. Let $\psi_{ab}$ be NPC phase offsets with $\psi_{ba}=-\psi_{ab}$. Then:
--
--   1. If the polygon is strictly convex in its cyclic order, its area is $A_{\mathcal AN}=\sum_{q=1}^{N-2}A_{\mathcal A3(q)}$.
--   2. If every elemental triad $(0,q,q+1)$ is non-collinear with non-zero closure phase $\psi_{3(q)}$, then
--
--   $$\sum_{q=1}^{N-2}A_{\mathcal A3(q)}=\frac{1}{16\pi^2}\sum_{q=1}^{N-2}\frac{\psi_{3(q)}^2}{A_{\mathcal I3(q)}}.$$
--
--   Together these are eq. (28).
--
--   **Formalization Note** The paper states $A_{\mathcal AN}=\sum_qA_{\mathcal A3(q)}$ for any closed polygon. With unsigned areas this fails for concave polygons. For example, the quadrilateral $(4,0),(1,1),(0,4),(0,0)$ has enclosed (shoelace) area $4$ and convex-hull area $8$, but its two fan triangles from the first vertex have areas $4$ and $8$, summing to $12$. The first equality is therefore stated for convex polygons. The paper also leaves implicit that every $\psi_{3(q)}\ne0$, without which $A_{\mathcal I3(q)}=0$ and the right-hand side is undefined.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c026; Appendix 2, eq. (28), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem polygon_area_from_triad_closure_phases {M : ℕ} (hM : 1 ≤ M) (x : Fin (M + 2) → Plane)
    (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b) :
    (IsConvexPolygon x → apertureArea x = ∑ q : Fin M, apertureArea (x ∘ fanTriad q)) ∧
    ((∀ q : Fin M, AffineIndependent ℝ (x ∘ fanTriad q)) →
      (∀ q : Fin M, closurePhase (loopPhase ψ (fanTriad q)) ≠ 0) →
      ∑ q : Fin M, apertureArea (x ∘ fanTriad q) =
        1 / (16 * Real.pi ^ 2) * ∑ q : Fin M,
          closurePhase (loopPhase ψ (fanTriad q)) ^ 2 /
            imageArea (x ∘ fanTriad q) (loopPhase ψ (fanTriad q))) := by sorry

end Arxiv2012_05254
