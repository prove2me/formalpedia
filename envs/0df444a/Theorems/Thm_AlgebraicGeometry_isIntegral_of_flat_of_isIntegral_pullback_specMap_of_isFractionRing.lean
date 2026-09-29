-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
-- name    : AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fc002a90-6251-5873-ba10-3cd745ecba5e
-- title:
--   Flatness and integral generic fibre imply X integral
-- statement:
--   Let $A$ be a commutative ring that is an integral domain and let $L$ be a field equipped with an $A$-algebra structure exhibiting $L$ as a fraction field of $A$ (so the structure map $A \to L$ is injective with every element of $L$ a quotient of images of elements of $A$), both in a fixed universe. Let $X$ be a scheme in that universe and let $f : X \to \operatorname{Spec} A$ be a morphism of schemes which is flat. Write $g : \operatorname{Spec} L \to \operatorname{Spec} A$ for the morphism induced by the structure map $A \to L$, and assume that the underlying scheme of the categorical fibre product $X \times_{\operatorname{Spec} A} \operatorname{Spec} L$ — the generic fibre of $f$ — is integral, that is, its underlying topological space is irreducible (in particular non-empty) and it is reduced. The conclusion is that $X$ itself is integral: $X$ is irreducible and reduced.
--
--   This is the standard descent of integrality along a flat morphism to a domain from the generic fibre, as in EGA IV₂. It is used in the project to recognise integrality of schemes over a base domain — for instance for smooth proper families, for schemes over a discrete valuation ring analysed through their smooth locus, and in the construction of an integral coarse moduli scheme in the Čerednik–Drinfeld setting — where it replaces limit arguments over possibly non-noetherian valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
    {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [IsIntegral ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A L))))] :
    IsIntegral X := by sorry
