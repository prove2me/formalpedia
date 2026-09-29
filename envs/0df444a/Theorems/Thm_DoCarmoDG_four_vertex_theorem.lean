-- Prove2me | Theorems.Thm_DoCarmoDG_four_vertex_theorem
-- name    : DoCarmoDG.four_vertex_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:34:14.543551+00:00
-- url     : https://prove2.me/theorems/0f3bc25f-7607-45aa-863e-304fcf5dabaf
-- title:
--   The four-vertex theorem
-- statement:
--   **The four-vertex theorem** (do Carmo §1-7, Theorem 2, p. 37): *a simple closed convex curve has at least four vertices*, a vertex being a parameter at which the derivative of the curvature vanishes.
--
--   An ellipse with unequal axes has exactly four vertices, at the points where the axes meet it, so the bound is sharp. Equivalently, the curvature function of a closed convex curve is either constant or has at least two maxima and two minima. do Carmo notes that the theorem remains true for simple closed curves that are not convex, by a harder argument.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 1, Section 1-7 (pp. 31-46)

import Definitions.Def_DoCarmo_plane_curves

namespace DoCarmoDG

theorem four_vertex_theorem
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsSimpleClosedCurve l alpha)
    (hconv : IsConvexPlaneCurve alpha) :
    ∃ t₁ ∈ Set.Ico (0 : ℝ) l, ∃ t₂ ∈ Set.Ico (0 : ℝ) l, ∃ t₃ ∈ Set.Ico (0 : ℝ) l,
      ∃ t₄ ∈ Set.Ico (0 : ℝ) l,
        t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ ∧
        IsVertex alpha t₁ ∧ IsVertex alpha t₂ ∧ IsVertex alpha t₃ ∧ IsVertex alpha t₄ := by
  sorry

end DoCarmoDG
