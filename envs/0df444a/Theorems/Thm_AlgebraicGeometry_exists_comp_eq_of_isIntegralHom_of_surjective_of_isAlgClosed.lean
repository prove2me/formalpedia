-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed
-- name    : AlgebraicGeometry.exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/4c2a429b-bc5e-56f6-93c8-306adf1d3246
-- title:
--   Lifting k-points along an integral surjection
-- statement:
--   Let $M$ and $X$ be schemes in a fixed universe and let $\pi : M \to X$ be a morphism of schemes which is integral, i.e. satisfies Mathlib's `IsIntegralHom`, and whose underlying continuous map `π.base` on topological spaces is surjective. Let $k$ be a field in the same universe which is algebraically closed, and let $y : \operatorname{Spec} k \to X$ be any morphism of schemes from the spectrum of $k$ (that is, a $k$-point of $X$, with $k$ regarded as a commutative ring via `CommRingCat.of`). The assertion is that there exists a morphism $x : \operatorname{Spec} k \to M$ with $x$ followed by $\pi$ equal to $y$; equivalently, $\pi \circ x = y$, so that every $k$-point of $X$ is the image of a $k$-point of $M$. No uniqueness is claimed, and no hypotheses beyond integrality and surjectivity of $\pi$ are imposed on the morphism.
--
--   This is the standard fact that an integral surjective morphism of schemes is surjective on points valued in an algebraically closed field (the case of finite surjections, in particular of quotients by finite groups, being the one used in practice). It is applied in the construction of coarse moduli spaces as quotients in the Čerednik–Drinfeld setting, where geometric points of a quotient must be realised as images of geometric points of the object being quotiented.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed
    {M X : Scheme.{u}} (π : M ⟶ X) [IsIntegralHom π] (hsurj : Function.Surjective π.base)
    (k : Type u) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ X) :
    ∃ x : Spec (CommRingCat.of k) ⟶ M, x ≫ π = y := by sorry
