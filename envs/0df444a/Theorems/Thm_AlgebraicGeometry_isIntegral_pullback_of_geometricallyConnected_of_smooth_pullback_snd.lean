-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
-- name    : AlgebraicGeometry.isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/38f68475-9855-5301-a359-ab2f3ea39d06
-- title:
--   Integrality of base changes of smooth geometrically connected fibres
-- statement:
--   Let $R$ be a commutative ring, $K$ and $L$ fields, all in a fixed universe, and let $i : R \to K$ and $j : K \to L$ be ring homomorphisms. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism of schemes. Assume that the second projection of the fibre product $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ taken along $f$ and the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $i$, i.e. the structure morphism $X_K \to \operatorname{Spec} K$, is smooth and satisfies the property `GeometricallyConnected`. Then the fibre product of $f$ with the morphism $\operatorname{Spec} L \to \operatorname{Spec} R$ induced by the composite $j \circ i$, namely the scheme $X_L = X \times_{\operatorname{Spec} R} \operatorname{Spec} L$, is an integral scheme, i.e. satisfies `IsIntegral`. Note that the conclusion is an assertion about the scheme $X_L$ itself (irreducible, non-empty and reduced), not about the morphism $X_L \to \operatorname{Spec} L$.
--
--   This is the standard permanence statement that smoothness together with geometric connectedness of a fibre over a field forces integrality of all further base changes of that fibre to extension fields. It is used in the construction of Čerednik–Drinfel'd quotients, through [`CerednikDrinfeld.isIntegral_pullback_of_cerednikDrinfeld_quotient_of_smooth`](thm.html#CerednikDrinfeld.isIntegral_pullback_of_cerednikDrinfeld_quotient_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
    {R K L : Type u} [CommRing R] [Field K] [Field L] (i : R →+* K) (j : K →+* L)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom i)))]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom i)))] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by sorry
