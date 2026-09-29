-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_left
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/867e6474-ab49-5c26-b27d-d2c0b2f8a002
-- title:
--   Left translation invariance of pair tangent coordinates
-- statement:
--   Let $T'$ be a local commutative ring with residue field $k=\mathrm{ResidueField}\,T'$, let $I\subseteq T'$ be an ideal, let $V$ be an abelian group carrying commuting left and right $k$-module structures with central scalars together with a compatible $T'$-module structure, let $\iota\colon V\to T'$ be $T'$-linear, and let $C$ be a commutative $T'$-algebra. Let $q_Y\colon Y\to\operatorname{Spec} T'$ be a scheme over $T'$ equipped with a relative group law $L$, i.e. a group structure, natural in the base, on the sets of sections $\{\varphi\colon S\to Y: \varphi\circ q_Y$ equals the given $S\to\operatorname{Spec} T'\}$. Let $u,v,w\colon\operatorname{Spec} C\to Y$ be three morphisms whose composites with $q_Y$ are $\operatorname{Spec}$ of the structure map $T'\to C$. Let $x_k\colon A_k\to\operatorname{Spec} k$ carry a relative group law $L_k$, and let $a_k\colon A_k\to Y$ exhibit $A_k$ as the fibre product of $Y$ with $\operatorname{Spec} k$ over $\operatorname{Spec} T'$ along $\operatorname{Spec}$ of the residue map; assume $a_k$ is a homomorphism on points, in the sense that for every $t\colon S\to\operatorname{Spec} k$ and sections $P,Q$ of $x_k$ over $t$, the composite of $L_k.\mathrm{mul}\,t\,P\,Q$ with $a_k$ is the $L$-product of $P\circ a_k$ and $Q\circ a_k$ over $t$ followed by $\operatorname{Spec}$ of the residue map. Let $U_e\subseteq A_k$ be open and let $c$ assign to each section in $\Gamma(A_k,U_e)$ a $k$-linear map $\mathrm{Hom}_k(V,k)\to k\otimes_{T'}C$. Assume $c$ is a system of tangent coordinates for the pair $(u,v)$, that is: there are $w_0\colon\operatorname{Spec}\big((k\otimes_{T'}C)\otimes_k \mathrm{TrivSqZeroExt}(k,V)\big)\to A_k$ lying over the prescribed base morphism and $w_1\colon\operatorname{Spec}$ of the same thickening $\to U_e$ such that $w_0\circ a_k$ realises the pair $(u,v)$ (there exist a Schlessinger map $\vartheta$ from the pair ring of $I$ and $C$ to the thickening and a morphism $\varphi$ from $\operatorname{Spec}$ of the pair ring to $Y$ pulling back to $u$ and $v$ along the two projections, with $w_0\circ a_k=\varphi\circ\operatorname{Spec}\vartheta$), $w_1$ followed by the open immersion $U_e\to A_k$ is the $L_k$-translate of $w_0$ to the unit, and $c$ is the tangent-coordinate function attached to the chart ring homomorphism of $w_1$. Then the same $c$ is a system of tangent coordinates for the left-translated pair $(w\cdot u,\,w\cdot v)$, the products being taken in the group of sections of $q_Y$ over $\operatorname{Spec}$ of $T'\to C$ supplied by $L$, with respect to the same data $x_k,L_k,a_k,U_e$.
--
--   This expresses the invariance of the pair-level tangent coordinates under left translation by a common point $w$ of $Y$ over $\operatorname{Spec} C$, the scheme-theoretic counterpart of the trivialisation of the tangent bundle of a group scheme by translations. It feeds into [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_of_isCommutative`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_of_isCommutative), where the commutative case lets translation be moved from one side to the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_left.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_left
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T')
    (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (L : RelativeGroupLaw T' qY)
    (u v w : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hw : w ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (hakhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      (Lk.mul t P Q).1 ≫ ak =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (residue T')))
          ⟨P.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, Q.2]⟩).1)
    (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    IsTangentCoordsOfPairAt I V ι C
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨w, hw⟩ ⟨u, hu⟩).1
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨w, hw⟩ ⟨v, hv⟩).1 xk Lk ak Ue c := by sorry
