-- Prove2me | Theorems.Thm_AlgebraicGeometry_isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing
-- name    : AlgebraicGeometry.isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/4975f674-a1fd-5236-9e77-390c5363b6db
-- title:
--   Properness from a proper closed fibre and a section
-- statement:
--   Let $R$ be a Noetherian local commutative ring and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes (all in a fixed universe) which is separated, locally of finite type and quasi-compact, and which satisfies the property `GeometricallyConnected`, i.e. has geometrically connected fibres. Assume that $f$ admits a section: a morphism $e \colon \operatorname{Spec} R \to X$ such that $e$ followed by $f$ is the identity of $\operatorname{Spec} R$. Assume further that there is a field $K$ and a morphism $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} R$ which is a closed immersion (so $\iota$ identifies $\operatorname{Spec} K$ with the closed point of $\operatorname{Spec} R$, $K$ being its residue field), such that the second projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is proper, i.e. the closed fibre of $f$ is proper over $K$. The conclusion is that $f$ itself is proper.
--
--   This is Grothendieck's criterion for properness along a fibre (EGA IV, 15.7.10) specialised to a local base, where an open neighbourhood of the closed point is the whole of $\operatorname{Spec} R$: properness of the closed fibre propagates to properness of $f$ once fibres are geometrically connected and a section exists. It is used in the construction of Néron models and abelian schemes from relative group laws, and in establishing properness of the compactified models of the modular curves $X_1$ occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyConnected f]
    (e : Spec (CommRingCat.of R) ⟶ X) (he : e ≫ f = 𝟙 (Spec (CommRingCat.of R)))
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion ι] [IsProper (pullback.snd f ι)] :
    IsProper f := by sorry
