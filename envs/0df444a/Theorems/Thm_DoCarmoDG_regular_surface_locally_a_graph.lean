-- Prove2me | Theorems.Thm_DoCarmoDG_regular_surface_locally_a_graph
-- name    : DoCarmoDG.regular_surface_locally_a_graph
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:34:08.205305+00:00
-- url     : https://prove2.me/theorems/3ad3b8f2-1d65-4585-828e-70b68fbce7e5
-- title:
--   A regular surface is locally a graph
-- statement:
--   do Carmo §2-2, Proposition 3 (p. 63): let $S \subseteq \mathbb{R}^3$ be a regular surface and $p \in S$. Then there exists a neighbourhood $V$ of $p$ in $S$ such that $V$ is the graph of a differentiable function of one of the three forms $z = f(x,y)$, $y = g(x,z)$, $x = h(y,z)$. Which of the three occurs depends on which $2 \times 2$ Jacobian minor of a parametrization is nonzero at the point.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-2 (pp. 54-71)

import Definitions.Def_DoCarmo_regular_surface

namespace DoCarmoDG

theorem regular_surface_locally_a_graph
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ∈ S) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ p ∈ W ∧
      ((∃ (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ W ∩ S = W ∩ graphOf U f) ∨
       (∃ (U : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) g U ∧ W ∩ S = W ∩ graphOfXZ U g) ∨
       (∃ (U : Set (ℝ × ℝ)) (h : ℝ × ℝ → ℝ),
          IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) h U ∧ W ∩ S = W ∩ graphOfYZ U h)) := by sorry

end DoCarmoDG
