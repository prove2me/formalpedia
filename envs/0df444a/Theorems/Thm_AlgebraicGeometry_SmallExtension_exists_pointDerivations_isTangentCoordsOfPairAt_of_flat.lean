-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
-- name    : AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/f4b340e9-e475-53be-bfd9-c2ac112d81fd
-- title:
--   Point-derivation form of tangent coordinates of a pair of lifts
-- statement:
--   Let $T'$ be a commutative Artinian local ring with residue field $k=\mathrm{ResidueField}\,T'$, let $I\subseteq\mathfrak m_{T'}$ be an ideal with $I\cdot\mathfrak m_{T'}=0$, and let $V$ be a finite $k$-module (with compatible left, right and $T'$-module structures) equipped with an injective $T'$-linear map $\iota\colon V\to T'$ whose range is $I$ viewed as a $T'$-submodule. Let $C$ be a commutative flat $T'$-algebra, $q_Y\colon Y\to\operatorname{Spec}T'$ a scheme over $T'$, and $u,v\colon\operatorname{Spec}C\to Y$ two morphisms over $\operatorname{Spec}T'$ that become equal after pre-composition with $\operatorname{Spec}$ of the quotient $C\to C/IC$. Let $x_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ (a functorial group structure on sections over $\operatorname{Spec}k$, with unit, inverse, associativity and naturality), let $a_k\colon A_k\to Y$ make the square with $x_k$, $q_Y$ and $\operatorname{Spec}$ of the residue map cartesian, let $U_e\subseteq A_k$ be an affine open, and let $e_1\colon\operatorname{Spec}k\to U_e$ factor the unit $L_k.\mathrm{one}(\mathrm{id})$ through $U_e$. Then, for the $k$-algebra structure on $\Gamma(A_k,U_e)$ induced by $x_k$, there is a $k$-linear map $\delta\colon\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$ satisfying the Leibniz rule $\delta(ab)=\mathrm{ev}(a)\,\delta(b)+\mathrm{ev}(b)\,\delta(a)$ for the evaluation ring map $\mathrm{ev}\colon\Gamma(A_k,U_e)\to k$ coming from $e_1$, such that $a\mapsto\delta(a)$ is a tangent coordinate function of the pair $(u,v)$ at the unit in the chart $U_e$: there exist $w_0\colon\operatorname{Spec}\bigl((k\otimes_{T'}C)\otimes_k(k\oplus V)\bigr)\to A_k$ over the canonical base morphism and $w_1$ into $U_e$ with $w_0$ followed by $a_k$ a tangent morphism of $(u,v)$ (i.e. it factors, through a Schlessinger map $\vartheta$ out of the pair ring of $I$ and $C$, a morphism from $\operatorname{Spec}$ of the pair ring restricting to $u$ and $v$ along the two projections), with $w_1$ followed by the inclusion of $U_e$ the translate of $w_0$ by $L_k$, and with $\delta$ equal to the tangent coordinates attached to the chart ring homomorphism of $w_1$.
--
--   This is the existence half of the dictionary between pairs of lifts of a point agreeing modulo a small ideal $I$ and point derivations at the identity with values in $k\otimes_{T'}C\otimes V^\vee$-coordinates, in the form in which the derivation property is explicit; it refines the bare existence of tangent coordinates by recording that the coordinate function is a $k$-point derivation at the unit section. It is used in the deformation-theoretic computation of obstruction cocycles and of the criterion for extending homomorphisms of abelian schemes over small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing
open AlgebraicGeometry.SmallExtension
open Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra

universe u

theorem AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (v : Spec (CommRingCat.of C) ⟶ Y) (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1) :
    letI := algebraOfHom xk Ue
    ∃ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
      IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue
        (fun a => (δ : Γ(Ak, Ue) →ₗ[ResidueField T'] (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) a) := by sorry
