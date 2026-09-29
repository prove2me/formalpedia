-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
-- name    : AlgebraicGeometry.isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fb732eb1-aca9-5e7e-b9e6-57a747b598ee
-- title:
--   Generic fibre of an integral scheme flat over a domain
-- statement:
--   Let $R$ be a commutative ring which is a domain, and let $K$ be a field equipped with an $R$-algebra structure exhibiting it as a fraction ring of $R$ (that is, the localisation of $R$ at its non-zero divisors). Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as an object of the category of commutative rings; assume that $X$ is an integral scheme (irreducible and reduced, in Mathlib's `IsIntegral` sense) and that $f$ is flat. The conclusion is that the fibre product of $f$ with the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map $R \to K$, formed as a pullback in the category of schemes, is again an integral scheme. Both the base ring and the fraction field are taken in the same universe as the scheme $X$.
--
--   This is the standard fact that the generic fibre $X_K = X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ of an integral scheme flat over a domain $R$ with fraction field $K$ is integral. It is used in the Čerednik–Drinfel'd part of the development, where geometric reducedness and geometric connectedness of curve models over a base are deduced from properties of their generic fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X] [Flat f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by sorry
