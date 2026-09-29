-- Prove2me | Theorems.Thm_DoCarmoDG_injective_parametrization_has_continuous_inverse
-- name    : DoCarmoDG.injective_parametrization_has_continuous_inverse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T01:35:26.82613+00:00
-- url     : https://prove2.me/theorems/42f3c65a-17ad-4602-9c63-9a8fe49134b1
-- title:
--   Conditions 1 and 3 plus injectivity give a continuous inverse
-- statement:
--   do Carmo §2-2, Proposition 4 (p. 65): let $p \in S$ be a point of a regular surface $S$ and let $x : U \subseteq \mathbb{R}^2 \to \mathbb{R}^3$ be a map with $p \in x(U) \subseteq S$ satisfying conditions 1 and 3 of Definition 1. If $x$ is one-to-one, then $x^{-1}$ is continuous. In other words, for a map into a surface already known to be regular, the homeomorphism condition follows from the other two conditions together with injectivity — which is what makes examples easy to verify.
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-2 (pp. 54-71)

import Definitions.Def_DoCarmo_regular_surface

namespace DoCarmoDG

theorem injective_parametrization_has_continuous_inverse
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsRegularSurface S)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) x U)
    (hreg : ∀ q ∈ U, Function.Injective (fderiv ℝ x q))
    (hsub : x '' U ⊆ S) (hinj : Set.InjOn x U) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ,
      ContinuousOn g (x '' U) ∧ ∀ q ∈ U, g (x q) = q := by sorry

end DoCarmoDG
