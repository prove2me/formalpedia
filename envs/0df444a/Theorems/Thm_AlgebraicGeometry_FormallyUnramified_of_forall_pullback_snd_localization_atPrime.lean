-- Prove2me | Theorems.Thm_AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime
-- name    : AlgebraicGeometry.FormallyUnramified.of_forall_pullback_snd_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ff7c9426-8b37-5022-b735-5817adcd5773
-- title:
--   Formal unramifiedness over Spec R from localisations at primes
-- statement:
--   Let $R$ be a commutative ring and let $X$ be a scheme, and let $g : X \to \operatorname{Spec} R$ be a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as an object of `CommRingCat`. Assume that for every prime ideal $\mathfrak p$ of $R$ the second projection of the pullback of $g$ along the morphism $\operatorname{Spec}(R_{\mathfrak p}) \to \operatorname{Spec} R$ induced by the localisation map $R \to R_{\mathfrak p}$ (localisation at $\mathfrak p$, i.e. `Localization.AtPrime`) lies in the class `AlgebraicGeometry.FormallyUnramified`; that is, the base change $X \times_{\operatorname{Spec} R} \operatorname{Spec}(R_{\mathfrak p}) \to \operatorname{Spec}(R_{\mathfrak p})$ is formally unramified for all $\mathfrak p$. The conclusion is that $g$ itself is formally unramified. Thus formal unramifiedness of a morphism with affine base may be checked after base change to all localisations of the base at its prime ideals; the converse implication is the (separate) stability of formal unramifiedness under base change.
--
--   This is the descent, or globalisation, half of the statement that formal unramifiedness over an affine base is detected on the localisations of the base at its primes; it permits results proved over a local base to be transferred to an arbitrary affine (hence, by Zariski-locality on the target, arbitrary) base. It is used for the corresponding criterion for étale morphisms and, in this development, in the verification that torsion kernels of group schemes and related closed subschemes are finite and étale when the relevant integer is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.FormallyUnramified.of_forall_pullback_snd_localization_atPrime
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (H : ∀ (p : Ideal R) [p.IsPrime],
      FormallyUnramified (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    FormallyUnramified g := by sorry
