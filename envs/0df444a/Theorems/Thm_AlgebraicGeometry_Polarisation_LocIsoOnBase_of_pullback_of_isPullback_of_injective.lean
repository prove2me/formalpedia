-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_isPullback_of_injective
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_isPullback_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4a320aac-37b5-5e98-be1e-67e587a21dee
-- title:
--   Descent of local isomorphism of line bundles along an injective base change
-- statement:
--   Let $\varphi : T \to R$ be a ring homomorphism of commutative rings which is injective as a map of sets. Let $f : A \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points of $f$, with the group axioms and compatibility under base change along maps of test schemes) and with an `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal M, \mathcal N$ be modules on $A$, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction is isomorphic to the unit sheaf of modules on $U$. Let $f' : A' \to \operatorname{Spec} R$ and $g : A' \to A$ be such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ is cartesian. Assume that $g^{*}\mathcal M$ and $g^{*}\mathcal N$ are locally isomorphic over the base $\operatorname{Spec} R$: for every point $s \in \operatorname{Spec} R$ there is an open $U \ni s$ and an isomorphism between the restrictions of $g^{*}\mathcal M$ and $g^{*}\mathcal N$ to $f'^{-1}(U)$. Then $\mathcal M$ and $\mathcal N$ are locally isomorphic over $\operatorname{Spec} T$ in the same sense: every point of $\operatorname{Spec} T$ has an open neighbourhood $U$ with the restrictions of $\mathcal M$ and $\mathcal N$ to $f^{-1}(U)$ isomorphic.
--
--   This is the descent step for the see-saw criterion: the locus in the base over which two invertible modules on an abelian scheme become locally isomorphic is closed, so it contains the whole base as soon as it contains a subscheme whose defining ring map is injective. It is used in the construction of canonical polarisations on fake elliptic curves and in the discrete-valuation-ring statements about principal square roots and kernels of polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_isPullback_of_injective.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_isPullback_of_injective
    {T R : Type} [CommRing T] [CommRing R] (φ : T →+* R) (hφ : Function.Injective φ)
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of T)} (L : RelativeGroupLaw T f) (hA : AbelianSchemePropertyBundle T f)
    (𝓜 𝓝 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓝 : Scheme.Modules.IsInvertible 𝓝)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (h : LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓜) ((Scheme.Modules.pullback g).obj 𝓝)) :
    LocIsoOnBase f 𝓜 𝓝 := by sorry
