-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective
-- name    : AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/162e73cc-7863-5163-aa9c-2a23642830f8
-- title:
--   Geometric points lift along integral surjections
-- statement:
--   Let $X$ and $Y$ be schemes (in the bottom universe) and let $f : X \to Y$ be a morphism of schemes which is integral, in the sense of Mathlib's `IsIntegralHom`, and surjective, in the sense of Mathlib's `Surjective` for scheme morphisms (the induced map of underlying topological spaces is onto). Let $k$ be an algebraically closed field, viewed as a commutative ring object, and let $y : \operatorname{Spec} k \to Y$ be any morphism of schemes, i.e. a $k$-valued point of $Y$. The assertion is that there exists a morphism $x : \operatorname{Spec} k \to X$, i.e. a $k$-valued point of $X$, such that $x$ followed by $f$ equals $y$; equivalently $f \circ x = y$. Thus every $k$-point of $Y$ lifts to a $k$-point of $X$ along $f$. No separatedness, finiteness of type or quasi-compactness hypotheses beyond those contained in integrality are imposed, and the lift is not claimed to be unique.
--
--   This is the standard fact that an integral (in particular finite) surjective morphism of schemes is surjective on $k$-valued points for $k$ algebraically closed, a geometric-point form of surjectivity. It is used in the Čerednik–Drinfel'd part of the development, where surjectivity on geometric points is transported along finite surjective comparison morphisms between moduli problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f]
    (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by sorry
