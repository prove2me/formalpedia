-- Prove2me | Theorems.Thm_DoCarmoDG_preimage_of_regular_value_is_regular_surface
-- name    : DoCarmoDG.preimage_of_regular_value_is_regular_surface
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:28:34.719498+00:00
-- url     : https://prove2.me/theorems/5c757842-52f8-4257-be8f-c250186fdb79
-- title:
--   The inverse image of a regular value is a regular surface
-- statement:
--   do Carmo §2-2, Proposition 2 (p. 61): if $f : U \subseteq \mathbb{R}^3 \to \mathbb{R}$ is a differentiable function and $a \in f(U)$ is a regular value of $f$, then $f^{-1}(a)$ is a regular surface in $\mathbb{R}^3$. This is the criterion that identifies spheres, ellipsoids, tori and other level sets as regular surfaces without exhibiting parametrizations.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-2 (pp. 54-71)

import Definitions.Def_DoCarmo_regular_surface

namespace DoCarmoDG

theorem preimage_of_regular_value_is_regular_surface
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (a : ℝ) (ha : a ∈ f '' U) (hreg : IsRegularValue U f a) :
    IsRegularSurface {p | p ∈ U ∧ f p = a} := by sorry

end DoCarmoDG
