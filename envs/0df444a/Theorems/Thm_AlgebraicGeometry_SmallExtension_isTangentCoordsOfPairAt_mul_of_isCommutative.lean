-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_of_isCommutative
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/0c5254ed-1dd1-50a6-b2a6-92bb116a1082
-- title:
--   Additivity of pair tangent coordinates along a commutative group law
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k=\mathrm{ResidueField}\,T'$, let $I\subseteq\mathfrak m$ be an ideal with $I\cdot\mathfrak m=0$, let $V$ be a finite $k$-module (with the two-sided, centrally acting structure and a compatible $T'$-action), and let $\iota\colon V\to T'$ be an injective $T'$-linear map whose image is exactly $I$. Let $C$ be a flat $T'$-algebra, $q_Y\colon Y\to\operatorname{Spec}T'$ a scheme over $T'$ and $L$ a relative group law on $q_Y$ (a functorial group structure on the sets of sections $\{\varphi\mid \varphi\circ q_Y=t\}$, natural in the base $t$) which is commutative. Let $u,v,u',v'\colon\operatorname{Spec}C\to Y$ be four $T'$-morphisms, with $u,v$ agreeing and $u',v'$ agreeing after precomposition with $\operatorname{Spec}(C/IC)\to\operatorname{Spec}C$. Let $x_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ and let $a_k\colon A_k\to Y$ make $(a_k,x_k)$ a pullback of $q_Y$ along $\operatorname{Spec}k\to\operatorname{Spec}T'$, the hypothesis `hakhom` saying that $a_k$ carries $L_k$-products of sections over any $t\colon S\to\operatorname{Spec}k$ to $L$-products of their images. Let $U_e\subseteq A_k$ be an affine open through which the $L_k$-unit section factors via $e_1$, and let $c,c'\colon\Gamma(A_k,U_e)\to\mathrm{Hom}_k(V^\vee,k\otimes_{T'}C)$ satisfy `IsTangentCoordsOfPairAt` for the pairs $(u,v)$ and $(u',v')$ respectively: there are a morphism $w_0\colon\operatorname{Spec}\bigl((k\otimes_{T'}C)\otimes_k \mathrm{TrivSqZeroExt}\,k\,V\bigr)\to A_k$ over the canonical base map and a lift $w_1$ into $U_e$ of the $L_k$-translate of $w_0$, such that $w_0$ followed by $a_k$ is a tangent vector of the pair (it factors as $\operatorname{Spec}\vartheta$ followed by some $\varphi\colon\operatorname{Spec}(\mathrm{pairRing}\,I\,C)\to Y$ with $\vartheta$ a Schlessinger map and with the two structural sections pulling $\varphi$ back to $u$ and $v$), and the coordinate function is obtained from the chart ring homomorphism of $w_1$ by `tangentCoords`. Then $c+c'$ satisfies `IsTangentCoordsOfPairAt` for the pair of $L$-products $(u\cdot u',\,v\cdot v')$ of sections over $\operatorname{Spec}C$, with the same $x_k$, $L_k$, $a_k$ and $U_e$.
--
--   This is the product rule for the canonical tangent coordinates attached to a pair of $C$-points congruent modulo $IC$: the pairing is additive in each argument, so that passing to pointwise products in a commutative group law adds coordinates. It feeds the computation of the obstruction cocycle attached to local lifts, where a cocycle built from such pair coordinates must be shown to be additive under multiplication of the lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_mul_of_isCommutative.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing
open AlgebraicGeometry.SmallExtension
open NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_mul_of_isCommutative
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (L : RelativeGroupLaw T' qY) (hLc : L.IsCommutative)
    (u v u' v' : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hu' : u' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv' : v' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (huv' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u'
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v')
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (hakhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      (Lk.mul t P Q).1 ≫ ak =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (residue T')))
          ⟨P.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ ak, by rw [Category.assoc, hak.w, ← Category.assoc, Q.2]⟩).1)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (c c' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c)
    (h' : IsTangentCoordsOfPairAt I V ι C u' v' xk Lk ak Ue c') :
    IsTangentCoordsOfPairAt I V ι C
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨u, hu⟩ ⟨u', hu'⟩).1
      (L.mul (Spec.map (CommRingCat.ofHom (algebraMap T' C))) ⟨v, hv⟩ ⟨v', hv'⟩).1 xk Lk ak Ue (c + c') := by sorry
