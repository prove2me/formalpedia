-- Prove2me | Theorems.Thm_DoCarmoDG_change_of_parameters
-- name    : DoCarmoDG.change_of_parameters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:35:51.877182+00:00
-- url     : https://prove2.me/theorems/0f98a50f-e50e-46a2-a8d2-2ba8cba5b3c2
-- title:
--   Change of parameters (do Carmo §2-3, Proposition 1)
-- statement:
--   **Change of parameters** (do Carmo §2-3, Proposition 1, p. 74): let $p$ be a point of a regular surface $S$, and let $x : U \to S$, $y : V \to S$ be two parametrizations of $S$ with $p \in x(U) \cap y(V) = W$. Then the change of coordinates $h = x^{-1} \circ y : y^{-1}(W) \to x^{-1}(W)$ is a diffeomorphism: $h$ is differentiable and has a differentiable inverse.
--
--   This is what makes every notion defined in local coordinates — differentiable function on a surface, tangent plane, first and second fundamental forms, curvature — independent of the parametrization used to define it.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-3, Proposition 1 (p. 74)

import Definitions.Def_DoCarmo_regular_surface

namespace DoCarmoDG

theorem change_of_parameters
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U V : Set (ℝ × ℝ)) (x y : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsSurfaceParametrization U x S) (hy : IsSurfaceParametrization V y S) :
    IsOpen (V ∩ y ⁻¹' (x '' U)) ∧ IsOpen (U ∩ x ⁻¹' (y '' V)) ∧
      ∃ h hinv : ℝ × ℝ → ℝ × ℝ,
        (∀ q ∈ V ∩ y ⁻¹' (x '' U),
            h q ∈ U ∩ x ⁻¹' (y '' V) ∧ x (h q) = y q ∧ hinv (h q) = q) ∧
        (∀ q ∈ U ∩ x ⁻¹' (y '' V),
            hinv q ∈ V ∩ y ⁻¹' (x '' U) ∧ y (hinv q) = x q ∧ h (hinv q) = q) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h (V ∩ y ⁻¹' (x '' U)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) hinv (U ∩ x ⁻¹' (y '' V)) := by sorry

end DoCarmoDG
