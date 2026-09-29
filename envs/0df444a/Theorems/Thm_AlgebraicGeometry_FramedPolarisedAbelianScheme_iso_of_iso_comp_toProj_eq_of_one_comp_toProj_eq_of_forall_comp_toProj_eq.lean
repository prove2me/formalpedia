-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/969f1507-e46d-5a1a-8fa8-e5ba8d2bd1f8
-- title:
--   Framed rigidity: frame-compatible isomorphisms of framed polarised abelian schemes
-- statement:
--   Let $g$, $N$, $n$ be natural numbers, $S$ a commutative ring, and let $X$, $X'$ be framed polarised abelian schemes of type $(g,N,n)$ over $S$: each consists of a polarised abelian scheme of relative dimension $g$, degree $N+1$ and level $n$ over $\operatorname{Spec} S$ — a scheme $A$ with structure morphism $f$, relative group law $L$, commutativity, the property bundle `bundle`, fibre dimension $g$, level sections $P_i$ ($i \in \mathrm{Fin}\,(2g)$) forming a basis of the $n$-torsion, and an invertible, very ample module `pol` with geometric fibre $H^0$-rank $N+1$ — together with a projective presentation `frame` of `pol` over $f$ with $N+1$ sections, whose morphism `frame.toProj` to $\mathbb{P}^N_S = \operatorname{Proj}$ of the homogeneous subalgebra of $S[X_0,\dots,X_N]$ is a closed immersion, the sections forming a section basis on the whole of $A$. Assume given an isomorphism of schemes $e_0 : X.A \cong X'.A$ such that $e_0$ followed by $X'.f$ is $X.f$ and $e_0$ followed by $X'$'s frame morphism is $X$'s frame morphism, that the identity-section origins of the two group laws over $\mathrm{id}_{\operatorname{Spec} S}$ have equal composites with the respective frame morphisms, and that for each $i$ the level sections $P_i$ and $P'_i$ likewise have equal composites with the respective frame morphisms. The conclusion is `FramedPolarisedAbelianScheme.Iso X X'`: there exist an isomorphism $e : X.A \cong X'.A$ over $\operatorname{Spec} S$ whose composite with $X'$'s frame morphism is $X$'s, which is a homomorphism for the relative group laws (for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x$, $y$ of $X.A$ over $t$, the product $X.L.\mathrm{mul}\,t\,x\,y$ followed by $e$ equals the $X'$-product of the transported points), which carries each $P_i$ to $P'_i$, and for which every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the pullback of $X'.\mathrm{pol}$ along $e$ becomes isomorphic to $X.\mathrm{pol}$ after restriction to $X.f^{-1}(U)$.
--
--   This is the rigidity step in the identification of framed polarised abelian schemes: an isomorphism of the underlying framed schemes that matches the embedded origin and the embedded level sections is automatically an isomorphism of the full polarised, framed data. It is used in the construction of the fine moduli space of such objects and in the comparison statements [`AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_one`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_one) and [`AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isPullback_of_isPullback`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isPullback_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
    {g N n : ℕ} {S : Type} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S)
    (e₀ : X.A ≅ X'.A) (he₀f : e₀.hom ≫ X'.f = X.f) (he₀ι : e₀.hom ≫ X'.frame.toProj = X.frame.toProj)
    (hone : (X.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ X.frame.toProj =
      (X'.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ X'.frame.toProj)
    (hP : ∀ i, (X.P i).1 ≫ X.frame.toProj = (X'.P i).1 ≫ X'.frame.toProj) :
    FramedPolarisedAbelianScheme.Iso X X' := by sorry
