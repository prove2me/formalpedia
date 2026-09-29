-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_of_pullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Polarisation.RosatiCompatible.of_pullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/75b85ec6-5d6a-55eb-9c89-58705ef9ef1e
-- title:
--   Rosati compatibility descends along faithfully flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra that is faithfully flat as an $S$-module. Let $f\colon A\to\operatorname{Spec} S$ be a morphism of schemes equipped with a relative group law $L$ (a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of points over varying $t\colon T\to\operatorname{Spec} S$), and assume `AbelianSchemePropertyBundle S f`: $f$ is smooth and proper, each fibre of $f$ is connected, and $f$ admits a relative group law. Let $f'\colon A'\to\operatorname{Spec} S'$ carry a relative group law $L'$, and let $g\colon A'\to A$ make the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S\to S'$ cartesian; assume $g$ is multiplicative on points, namely for all $t'\colon T\to\operatorname{Spec} S'$ and points $P,Q$ of $A'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,P\,Q$ with $g$ is $L.\mathrm{mul}$ applied to the images of $P$ and $Q$ over $t'$ followed by $\operatorname{Spec}(S\to S')$. Let $I$ be a type, $\iota\colon I\to\operatorname{End}(A)$ with $\iota(b)$ over $\operatorname{Spec} S$ (i.e. $\iota(b)$ followed by $f$ is $f$), $\iota'\colon I\to\operatorname{End}(A')$ with $\iota'(b)$ over $\operatorname{Spec} S'$, intertwined by $g$ in the sense that $\iota'(b)$ followed by $g$ equals $g$ followed by $\iota(b)$, and let $\star\colon I\to I$ be any self-map. Let $\mathcal L$ be an invertible module on $A$. Assume `RosatiCompatible` holds for $f'$, $L'$, $g^{*}\mathcal L$, $\iota'$ and $\star$. Then `RosatiCompatible` holds for $f$, $L$, $\mathcal L$, $\iota$ and $\star$: for every $b\in I$, the pullbacks of the Mumford bundle $m^{*}\mathcal L\otimes(p_1^{*}\mathcal L^{\vee}\otimes p_2^{*}\mathcal L^{\vee})$ on $A\times_S A$ along $(p_1,\iota(b)\circ p_2)$ and along $(\iota(\star b)\circ p_1,p_2)$ are isomorphic locally on the base, i.e. every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over whose preimage in $A\times_S A$ the two modules become isomorphic.
--
--   This is fpqc descent for Rosati compatibility of a line bundle with a family of endomorphisms and a prescribed involution-like self-map of the index set: the property, read as a local-on-the-base isomorphism of the two pullbacks of the Mumford bundle, may be checked after a faithfully flat extension of the base ring. It is used in the construction of canonical polarisation data on fake elliptic curves, where the compatibility is verified after localisation at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_RosatiCompatible_of_pullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u v

theorem AlgebraicGeometry.Polarisation.RosatiCompatible.of_pullback_of_faithfullyFlat
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (f' : A' ⟶ Spec (CommRingCat.of S')) (L' : RelativeGroupLaw S' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {I : Type v} (ι : I → (A ⟶ A)) (hι : ∀ b, ι b ≫ f = f) (ι' : I → (A' ⟶ A')) (hι' : ∀ b, ι' b ≫ f' = f')
    (hgι : ∀ b, ι' b ≫ g = g ≫ ι b) (star : I → I)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hros : RosatiCompatible f' L' ((Scheme.Modules.pullback g).obj 𝓛) ι' hι' star) :
    RosatiCompatible f L 𝓛 ι hι star := by sorry
