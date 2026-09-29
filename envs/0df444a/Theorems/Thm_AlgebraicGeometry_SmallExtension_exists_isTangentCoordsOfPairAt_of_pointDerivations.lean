-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations
-- name    : AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt_of_pointDerivations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/31a313a6-737e-50c6-ae3e-467d49e1d47b
-- title:
--   Point derivations at the unit are tangent coordinates of deformations
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k$, let $I\subseteq T'$ be an ideal contained in the maximal ideal with $I\cdot\mathfrak m=0$, and let $V$ be a finite-dimensional $k$-vector space (carrying compatible left and right $k$-actions with central scalars, and a $T'$-module structure compatible with the tower $T'\to k$) presented inside $I$ by an injective $T'$-linear $\iota\colon V\to T'$ whose range, as a $T'$-submodule, is $I$. Let $C$ be a flat $T'$-algebra, let $q_Y\colon Y\to\operatorname{Spec} T'$ be a scheme over $T'$ and $u\colon\operatorname{Spec} C\to Y$ a $T'$-morphism, i.e. $u$ followed by $q_Y$ is $\operatorname{Spec}$ of the structure map $T'\to C$. Let $x_k\colon A_k\to\operatorname{Spec} k$ carry a relative group law $L_k$ (functorial multiplication, unit and inverse on sections over varying bases, associative, unital, with inverses, and natural in the base), and let $a_k\colon A_k\to Y$ exhibit $A_k$ as the fibre product of $Y$ with $\operatorname{Spec} k$ over $\operatorname{Spec} T'$. Let $U_e\subseteq A_k$ be an affine open and $e_1\colon\operatorname{Spec} k\to U_e$ a factorisation of the unit section $L_k.\mathrm{one}$ of the identity base through $U_e$. Finally let $\delta$ be a point derivation of the $k$-algebra $\Gamma(A_k,U_e)$ (the algebra structure induced by $x_k$) at the evaluation homomorphism $\Gamma(A_k,U_e)\to k$ given by restriction along $e_1$, with values in $\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$; that is, a $k$-linear $\delta$ with $\delta(ab)=\mathrm{ev}(a)\,\delta(b)+\mathrm{ev}(b)\,\delta(a)$. Then there exists a $T'$-morphism $v\colon\operatorname{Spec} C\to Y$ which agrees with $u$ after composition with $\operatorname{Spec}$ of the quotient map $C\to C/IC$, and such that `IsTangentCoordsOfPairAt` holds for $I,V,\iota,C,u,v,x_k,L_k,a_k,U_e$ with the coordinate function $\delta$: there are $w_0\colon\operatorname{Spec}\big((k\otimes_{T'}C)\otimes_k(k\oplus V)\big)\to A_k$ lying over the canonical base morphism and $w_1\colon\operatorname{Spec}\big((k\otimes_{T'}C)\otimes_k(k\oplus V)\big)\to U_e$ such that $w_0$ followed by $a_k$ is a tangent vector of the pair $(u,v)$ — i.e. it factors as $\operatorname{Spec}$ of a Schlessinger ring map out of the pair ring of $I$ and $C$ composed with a morphism $\operatorname{Spec}(\mathrm{pairRing}\,I\,C)\to Y$ restricting to $u$ and $v$ along the two projections — while $w_1$ followed by the open immersion $U_e\hookrightarrow A_k$ is the $L_k$-translate of $w_0$ to the unit, and $\delta$ is the tangent-coordinate function of the chart homomorphism attached to $w_1$.
--
--   This is the surjectivity half of the identification, in the style of Schlessinger's theory of functors of Artin rings, between point derivations at the unit of the special fibre and infinitesimal deformations of a given $C$-point modulo a small ideal: every such derivation is realised as the tangent coordinate of an actual second $T'$-point $v$ congruent to $u$ modulo $IC$. It feeds the lifting and regluing steps in the construction of group-scheme (Néron/abelian-scheme) structures, being cited in the results that produce homomorphism lifts from point derivations and coboundary data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt_of_pointDerivations
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
    (δ : letI := algebraOfHom xk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))) :
    letI := algebraOfHom xk Ue
    ∃ v : Spec (CommRingCat.of C) ⟶ Y,
      v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v ∧
      IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue
        (fun a => (δ : Γ(Ak, Ue) →ₗ[ResidueField T'] (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) a) := by sorry
