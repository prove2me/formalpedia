-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
-- name    : AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/cd4559dc-e2d0-5d9d-aa17-aacedf59b522
-- title:
--   Smooth over normal is normal, on affine sections
-- statement:
--   Let $X$ and $Y$ be schemes and $f\colon X\to Y$ a morphism which is smooth, with both $X$ and $Y$ integral schemes. Assume that $Y$ is normal in the sense expressed by sections: for every open subset $V\subseteq Y$ which is an affine open, the ring $\Gamma(Y,V)$ of sections over $V$ is integrally closed (in its field of fractions, as the Mathlib predicate `IsIntegrallyClosed` asserts for a domain). Then the same holds for $X$: for every open $U\subseteq X$ which is an affine open, the ring $\Gamma(X,U)$ is integrally closed. The conclusion is stated for one fixed $U$ with its affineness hypothesis, so that, quantified over $U$, it says that $X$ is normal in exactly the same sections-based sense as the hypothesis on $Y$. Note that integrality of $X$ is assumed rather than deduced from smoothness over the integral scheme $Y$, and that normality of $Y$ enters only through the rings of sections of its affine opens.
--
--   This is the standard permanence statement that a smooth scheme over a normal base is normal (EGA IV 6.5.4, 17.5.7), here in the form "affine sections are integrally closed". It is used to verify normality of products such as $\mathfrak X\times_R D$ and $\mathfrak X\times_R(D\times_R D)$ over a normal Deligne–Rapoport model, via the smooth projections, in the construction of relative group laws and of Hecke correspondences on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ V : Y.Opens, IsAffineOpen V → IsIntegrallyClosed Γ(Y, V))
    (U : X.Opens) (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by sorry
