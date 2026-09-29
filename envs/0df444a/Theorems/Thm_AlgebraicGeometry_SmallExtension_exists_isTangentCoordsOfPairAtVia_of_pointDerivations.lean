-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations
-- name    : AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia_of_pointDerivations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/d73ac266-7ed5-58a2-b466-556ed9581142
-- title:
--   Exponentiating a point derivation into a deformation of u
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k =$ `ResidueField T'`, let $I \subseteq \mathfrak m_{T'}$ be an ideal with $I\,\mathfrak m_{T'} = 0$, and let $V$ be a finite-dimensional $k$-vector space (with its two central $k$-actions and a compatible $T'$-module structure) together with an injective $T'$-linear map $\iota : V \to T'$ whose image is exactly $I$. Let $C$ be a flat $T'$-algebra, $q_Y : Y \to \operatorname{Spec} T'$ a scheme over $T'$ and $u : \operatorname{Spec} C \to Y$ a morphism over $T'$. Let $x_k : A_k \to \operatorname{Spec} k$ carry a relative group law $L_k$, i.e. functorial group structures on the sets of $x_k$-sections over varying bases, let $W \subseteq A_k$ be an open with $a_W : W \to Y$ making the square formed by $a_W$, $W \hookrightarrow A_k \to \operatorname{Spec} k$, $q_Y$ and $\operatorname{Spec}(T' \to k)$ cartesian, and let $U_e \subseteq A_k$ be an affine open carrying a point $e_1 : \operatorname{Spec} k \to U_e$ lying over the unit section $L_k.\mathrm{one}$ of the group law on $\operatorname{Spec} k$. Finally let $\delta$ be a point derivation of $\Gamma(A_k, U_e)$ at the evaluation homomorphism attached to $e_1$ with values in $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} C)$, that is, a $k$-linear map $D$ with $D(ab) = a(e_1)\,D(b) + b(e_1)\,D(a)$. Then there is a morphism $v : \operatorname{Spec} C \to Y$ over $T'$ which agrees with $u$ after composition with $\operatorname{Spec}(C \to C/IC)$, and which satisfies `IsTangentCoordsOfPairAtVia` with coordinate function $\delta$: there are morphisms $w_0 : \operatorname{Spec} E \to W$ and $w_1 : \operatorname{Spec} E \to U_e$, where $E = (k \otimes_{T'} C) \otimes_k (k \oplus V)$ is the trivial square-zero thickening, such that $w_0$ lies over the canonical base point of the relative tangent points, $w_0$ followed by $a_W$ exhibits $(u,v)$ as a tangent vector in the sense of `IsTangentOfPair` (a ring map $\vartheta$ from the pair ring of $I$ and $C$ to $E$ which is a Schlessinger map, together with a morphism on $\operatorname{Spec}$ of the pair ring restricting to $u$ and $v$ along the two projections and to $w_0 \gg a_W$ along $\vartheta$), $w_1$ lands over the $L_k$-translate of $w_0$ to the unit, and the tangent coordinates of the chart homomorphism of $w_1$ equal $\delta$.
--
--   This is the surjectivity half of the identification of the tangent space of the deformation problem for $u$ with point derivations at the unit: every point derivation at the identity of $A_k$ is realised as the canonical tangent coordinate of some deformation $v$ of $u$ modulo $IC$, computed in the chart $U_e$ via the translation furnished by the group law. It feeds the construction of deformations compatible with an overlap isomorphism, used in [`AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations`](thm.html#AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations.lean

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
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia_of_pointDerivations
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
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
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
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue
        (fun a => (δ : Γ(Ak, Ue) →ₗ[ResidueField T'] (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) a) := by sorry
