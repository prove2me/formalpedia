-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
-- name    : AlgebraicGeometry.isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/df27494c-bdd1-5518-813e-d56565c4fc88
-- title:
--   Integrality of X×_A L from a geometrically integral generic fibre
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, and $A_0$ a commutative ring which is a domain, equipped with an injective ring homomorphism $\iota\colon A_0\to A$. Let $X_0$ be a scheme with a structure morphism $\mathrm{toBase}_0\colon X_0\to\operatorname{Spec}A_0$, and let $X$ be a scheme with a morphism $\mathrm{toBase}\colon X\to\operatorname{Spec}A$. Assume given an isomorphism $\mathrm{iso}$ of $X$ with the fibre product $X_0\times_{\operatorname{Spec}A_0}\operatorname{Spec}A$ formed along $\operatorname{Spec}(\iota)$, compatible with the structure morphisms in the sense that $\mathrm{iso}$ followed by the second projection equals $\mathrm{toBase}$. Assume further that the second projection $X_0\times_{\operatorname{Spec}A_0}\operatorname{Spec}K_0\to\operatorname{Spec}K_0$, formed along $\operatorname{Spec}$ of the localisation map $A_0\to K_0=\operatorname{FractionRing}A_0$ — that is, the generic fibre of $X_0$ over $A_0$ — satisfies `GeometricallyIntegral`, whose consequence used here is that any scheme sitting in a pullback square over this projection along a morphism out of $\operatorname{Spec}K_0$ is integral. The conclusion is that the fibre product $X\times_{\operatorname{Spec}A}\operatorname{Spec}L$, formed along $\operatorname{Spec}$ of the inclusion $A\to L$, is an integral scheme.
--
--   This is the standard statement that the generic fibre of a base change along an injective map of domains inherits integrality from the geometric integrality of the original generic fibre; here the base change is from a domain $A_0$ to a valuation subring $A$ of a field $L$, and the fibre taken is the one over $L$. It is used in the integrality clause of the construction of models over valuation rings, being cited by [`AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
    {L : Type} [Field L] (A : ValuationSubring L)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀]
    (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hGI : GeometricallyIntegral
      (Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀)))))) :
    IsIntegral ↑(Limits.pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap ↥A L)))) := by sorry
