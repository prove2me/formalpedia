-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
-- name    : AlgebraicGeometry.isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/2817d001-e580-5e78-b713-6646490ea2e6
-- title:
--   Affine charts of a finite flat surjective morphism are faithfully flat
-- statement:
--   Let $X$ and $Y$ be schemes and let $g \colon X \to Y$ be a morphism which is finite and flat (as morphisms of schemes, in Mathlib's sense) and whose underlying map of points is surjective. Let $U$ be an open subset of $Y$ which is an affine open, i.e. the canonical morphism from the spectrum of $\Gamma(Y, U)$ identifies $U$ with an affine scheme. The conclusion is a threefold assertion: first, the preimage open $g^{-1}U$ of $X$ is again an affine open; second, the ring homomorphism $g^{\sharp} \colon \Gamma(Y, U) \to \Gamma(X, g^{-1}U)$ obtained by applying $g$ on sections over $U$ is injective; and third, with respect to the $\Gamma(Y,U)$-algebra structure on $\Gamma(X, g^{-1}U)$ given by this very homomorphism, the ring $\Gamma(X, g^{-1}U)$ is faithfully flat as a $\Gamma(Y,U)$-module. Thus over every affine chart of the base the morphism is given by a faithfully flat, in particular injective, ring extension.
--
--   This is the standard affine-chart description of a finite flat surjective morphism: such a morphism is affine, and on charts it is given by a faithfully flat ring extension (cf. EGA IV 2.2.11). It is used in the treatment of abelian schemes and Jacobians of good reduction, for instance to descend data along finite flat covers, to produce finite faithfully flat charts compatible with étale pullbacks, and in arguments about the group law and cohomology of such schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [Flat g] (hsurj : Function.Surjective g)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (g ⁻¹ᵁ U) ∧ Function.Injective (g.app U).hom ∧
      (letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra;
        Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) := by sorry
