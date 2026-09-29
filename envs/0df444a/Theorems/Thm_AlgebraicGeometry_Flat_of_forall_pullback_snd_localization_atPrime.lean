-- Prove2me | Theorems.Thm_AlgebraicGeometry_Flat_of_forall_pullback_snd_localization_atPrime
-- name    : AlgebraicGeometry.Flat.of_forall_pullback_snd_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/b5d2eb99-6dba-596d-a99d-fc53121c1be3
-- title:
--   Flatness over Spec R is detected after base change to all R_𝔭
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $g : X \to \operatorname{Spec} R$ a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of the commutative ring $R$ viewed as an object of `CommRingCat`. Assume that for every prime ideal $\mathfrak p$ of $R$ the second projection of the pullback of $g$ along the morphism $\operatorname{Spec}(R_{\mathfrak p}) \to \operatorname{Spec} R$ induced by the localisation map $R \to R_{\mathfrak p} =$ `Localization.AtPrime p`, that is the base-changed morphism $X \times_{\operatorname{Spec} R} \operatorname{Spec}(R_{\mathfrak p}) \to \operatorname{Spec}(R_{\mathfrak p})$, belongs to the class `Flat` of flat morphisms of schemes. Then $g$ itself is flat. The hypothesis is indexed by all primes of $R$, not merely the maximal ones, and the conclusion is flatness of $g$ as a morphism of schemes, with no finiteness, quasi-compactness or affineness assumption on $X$.
--
--   This is the statement that flatness of a morphism over an affine base may be checked after base change to each local ring of the base. It is used, in combination with the corresponding statement for formal unramifiedness and for finite presentation, to obtain [`AlgebraicGeometry.Etale.of_forall_pullback_snd_localization_atPrime`](thm.html#AlgebraicGeometry.Etale.of_forall_pullback_snd_localization_atPrime), the analogous criterion for étaleness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Flat_of_forall_pullback_snd_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Flat.of_forall_pullback_snd_localization_atPrime
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (H : ∀ (p : Ideal R) [p.IsPrime],
      Flat (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    Flat g := by sorry
