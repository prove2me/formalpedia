-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
-- name    : AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c12ac4f6-1b5b-5a4e-982d-c348e92d036b
-- title:
--   Tangent coordinates determine the deformation v
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k=\mathrm{ResidueField}\,T'$, let $I\subseteq T'$ be an ideal with $I\le\mathfrak m$ and $I\cdot\mathfrak m=0$, and let $V$ be a $k$-module, finite over $k$, carrying commuting left and right $k$-actions (central) and a $T'$-module structure compatible with $k$ via the scalar tower, together with an injective $T'$-linear map $\iota\colon V\to T'$ whose range is $I$ viewed as a $T'$-submodule. Let $C$ be a flat $T'$-algebra, $q_Y\colon Y\to\operatorname{Spec}T'$ a scheme over $T'$, and $u,v,v'\colon\operatorname{Spec}C\to Y$ three sections over $\operatorname{Spec}T'$ (each composing with $q_Y$ to $\operatorname{Spec}$ of the structure map $T'\to C$) such that $u$ agrees with $v$ and with $v'$ after restriction along $\operatorname{Spec}(C/IC)\to\operatorname{Spec}C$. Let $x_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}k$, with associativity, unit laws, left inverse and naturality), let $W\subseteq A_k$ be an open with $a_W\colon W\to Y$ such that the square formed by $a_W$, $W\hookrightarrow A_k\to\operatorname{Spec}k$, $q_Y$ and $\operatorname{Spec}$ of the residue map is a pullback, let $U_e\subseteq A_k$ be an affine open and $e_1\colon\operatorname{Spec}k\to U_e$ a lift of the unit section $L_k.\mathrm{one}$. Finally let $c\colon\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$ be a function, and suppose both pairs $(u,v)$ and $(u,v')$ admit tangent coordinates $c$ via $(W,a_W,U_e)$, i.e. for each of them there are $w_0\colon\operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C)\to W$ lying over the base map of the relative tangent construction and $w_1\colon\operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C)\to U_e$ with: $w_0$ followed by $a_W$ is a tangent vector of the pair (there are a Schlessinger map $\vartheta$ from the pair ring of $I$ and $C$ to the thickening and a morphism $\varphi$ on $\operatorname{Spec}$ of the pair ring restricting to $u$ and to $v$, respectively $v'$, along the two projections, with $w_0\circ a_W$ obtained from $\varphi$ by $\vartheta$); $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ followed by the inclusion of $W$; and $c$ is the tangent-coordinate function attached to the chart homomorphism of $w_1$. Then $v=v'$.
--
--   This is the uniqueness half of the Schlessinger-style tangent space description of infinitesimal deformations: the canonical coordinates of a pair $(u,v)$, read in an affine chart at the unit of the group law after translating to the identity, determine $v$ among the lifts of $u$ along the small extension $I$. It is used in the construction of the overlap isomorphisms and the two-cocycle comparison in [`AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary`](thm.html#AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
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
    (v v' : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv' : v' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (huv' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v')
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c)
    (h' : IsTangentCoordsOfPairAtVia I V ι C u v' xk Lk W aW Ue c) :
    v = v' := by sorry
