-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt
-- name    : AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c89ffd4a-ff42-5657-9749-b6824a3cbe49
-- title:
--   Tangent coordinates determine the second member of a deformation pair
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k=$ `ResidueField T'`, let $I\subseteq\mathfrak m$ be an ideal with $I\mathfrak m=0$, and let $V$ be a finite-dimensional $k$-module (with a central right action and a compatible $T'$-module structure) equipped with an injective $T'$-linear map $\iota\colon V\to T'$ whose range is $I$. Let $C$ be a flat $T'$-algebra, $q_Y\colon Y\to\operatorname{Spec}T'$ a scheme over $T'$, and $u\colon\operatorname{Spec}C\to Y$ a $T'$-morphism. Let $x_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}k$, with associativity, unit, inverse and base-change naturality axioms), let $a_k\colon A_k\to Y$ exhibit $A_k$ as the pullback of $Y$ along $\operatorname{Spec}k\to\operatorname{Spec}T'$, let $U_e\subseteq A_k$ be an affine open, and let $e_1\colon\operatorname{Spec}k\to U_e$ be a lift of the unit section $L_k$ at the identity base. Let $v,v'\colon\operatorname{Spec}C\to Y$ be $T'$-morphisms which both agree with $u$ after restriction along $\operatorname{Spec}(C/IC)\to\operatorname{Spec}C$. Finally, let $c\colon\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$ and assume `IsTangentCoordsOfPairAt` holds for $c$ with respect to both pairs $(u,v)$ and $(u,v')$: that is, for each of $v$ and $v'$ there are $w_0\colon\operatorname{Spec}\bigl((k\otimes_{T'}C)\otimes_k (k\oplus V)\bigr)\to A_k$ lying over the canonical base morphism and $w_1$ into $U_e$ such that $w_0$ followed by $a_k$ is a tangent vector of the pair (i.e. both $u$ and the relevant member arise from a single morphism on the pair ring $\operatorname{pairRing} I\,C$ via a Schlessinger map $\vartheta$), $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ to the unit, and $c$ is the tangent-coordinate function of the chart homomorphism attached to $w_1$. Then $v=v'$.
--
--   This is the injectivity (rigidity) half of the standard identification of the set of infinitesimal deformations of $u$ over a small extension with a space of tangent coordinates: a deformation $v$ of $u$ modulo $IC$ is determined by the canonical coordinates of the pair $(u,v)$ on an affine chart at the unit of the special fibre group law. It is used in the construction of lifts of morphisms to Néron-model-type schemes, where coordinates are manipulated and the resulting morphism must be recovered uniquely.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra

universe u

theorem AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAt_of_isTangentCoordsOfPairAt
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (v v' : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv' : v' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (huv' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v')
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c)
    (h' : IsTangentCoordsOfPairAt I V ι C u v' xk Lk ak Ue c) :
    v = v' := by sorry
