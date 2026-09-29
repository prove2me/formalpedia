-- Prove2me | Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
-- name    : AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/4a492eaa-aabc-5918-96cf-25edf7e82d8c
-- title:
--   Nilpotent thickening of the base: homeomorphism on underlying spaces
-- statement:
--   Let $B$ and $B_0$ be commutative rings and let $\varphi\colon B \to B_0$ be a ring homomorphism which is surjective and whose kernel is nilpotent as an ideal, i.e. $(\ker\varphi)^n = 0$ for some $n$. Let $X$ and $X_0$ be schemes, and let $f\colon X \to \operatorname{Spec} B$, $f_0\colon X_0 \to \operatorname{Spec} B_0$ and $g\colon X_0 \to X$ be morphisms of schemes such that the square formed by $g$, $f_0$, $f$ and $\operatorname{Spec}\varphi\colon \operatorname{Spec} B_0 \to \operatorname{Spec} B$ is a pullback square, that is, $g$ followed by $f$ equals $f_0$ followed by $\operatorname{Spec}\varphi$ and the square is cartesian (so $X_0$ is identified with $X \times_{\operatorname{Spec} B} \operatorname{Spec} B_0$). The conclusion is the conjunction of three assertions: $g$ is a closed immersion; $g$ is surjective as a morphism of schemes (its underlying map of topological spaces is surjective); and the underlying continuous map $g_{\mathrm{base}}\colon |X_0| \to |X|$ is a homeomorphism.
--
--   This is the topological invariance of a scheme under a nilpotent thickening of its base: passing from $\operatorname{Spec} B$ to the closed subscheme $\operatorname{Spec} B_0$ cut out by a nilpotent ideal changes neither the underlying space of a $B$-scheme nor, consequently, its lattices of open, closed and clopen subsets. It is used in the project wherever data on a scheme must be transported along a nilpotent thickening, for instance in the deformation-theoretic arguments on relative tangent points, in the construction of local lifts over an ordered affine cover, and in the recognition of geometric connectedness over Artinian bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
    {B B₀ : Type u} [CommRing B] [CommRing B₀] (φ : B →+* B₀)
    (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ))
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀))
    (g : X₀ ⟶ X) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom φ))) :
    IsClosedImmersion g ∧ Surjective g ∧ IsHomeomorph g.base := by sorry
