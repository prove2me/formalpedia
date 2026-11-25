-- Prove2me | Theorems.Thm_Arxiv2012_05254_complementary_triangles_two_pi
-- name    : Arxiv2012_05254.complementary_triangles_two_pi
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T04:23:40.132386+00:00
-- url     : https://prove2.me/theorems/af3b8137-966e-4340-95fe-36577e187fae
-- title:
--   Sec. 3.1, footnote e: the closure phases of two complementary triangles at a vertex sum to $2\pi$
-- statement:
--   Let $x_0,x_1,x_2$ be the positions of a closed triad of non-collinear elements, with NPC phase offsets $\psi_{b\lceil b+1\rfloor_3}$ and closure phase $\psi_3$. Let $\hat s_0$ be the intersection of the NPCs of the two sides other than $a$. The NPCs of side $a$ form the family $L_n:\ 2\pi u_{a\lceil a+1\rfloor_3}\cdot\hat s+\psi_{a\lceil a+1\rfloor_3}+2\pi n=0$, $n\in\mathbb Z$, and $\hat s_0$ lies in the closed strip between two consecutive members $L_n,L_{n+1}$. For every such $n$, the two complementary triangles at $\hat s_0$ cut off by $L_n$ and $L_{n+1}$ have heights from $\hat s_0$ that give the closure phases
--
--   $$2\pi|u_{a\lceil a+1\rfloor_3}|\,d(\hat s_0,L_n)=|\psi_3+2\pi n|,\qquad 2\pi|u_{a\lceil a+1\rfloor_3}|\,d(\hat s_0,L_{n+1})=|\psi_3+2\pi(n+1)|,$$
--
--   and these sum to $2\pi$:
--
--   $$|\psi_3+2\pi n|+|\psi_3+2\pi(n+1)|=2\pi.$$
--
--   This is the geometric form of the $2\pi$ ambiguity of the closure phase.
--
--   **Formalization Note** The paper gives no definition of "complementary triangles". They are read here as the two triangles at the vertex bounded by the two neighbouring NPCs of the third fringe, one on each side of the vertex.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c035; Section 3.1, footnote e to the discussion of Fig. 3(a), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem complementary_triangles_two_pi (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) (a : Fin 3) (V : Plane)
    (hV : V ∈ npc (spacing x (a + 1)) (ψ (a + 1)) ∩ npc (spacing x (a + 2)) (ψ (a + 2))) :
    (∃ n : ℤ, V ∈ convexHull ℝ (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ)) ∪
        npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1)))) ∧
    ∀ n : ℤ, V ∈ convexHull ℝ (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ)) ∪
        npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1))) →
      2 * Real.pi * ‖spacing x a‖ *
          Metric.infDist V (npc (spacing x a) (ψ a + 2 * Real.pi * (n : ℝ))) =
        |closurePhase ψ + 2 * Real.pi * (n : ℝ)| ∧
      2 * Real.pi * ‖spacing x a‖ *
          Metric.infDist V (npc (spacing x a) (ψ a + 2 * Real.pi * ((n : ℝ) + 1))) =
        |closurePhase ψ + 2 * Real.pi * ((n : ℝ) + 1)| ∧
      |closurePhase ψ + 2 * Real.pi * (n : ℝ)| + |closurePhase ψ + 2 * Real.pi * ((n : ℝ) + 1)| =
        2 * Real.pi := by sorry

end Arxiv2012_05254
