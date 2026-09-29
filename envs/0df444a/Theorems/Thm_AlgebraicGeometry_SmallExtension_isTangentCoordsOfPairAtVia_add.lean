-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/4794e306-fbc4-569e-89e5-2f5fb30a46e6
-- title:
--   Additivity of via-tangent coordinates along a chain of lifts
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k =$ `ResidueField T'`, and let $I \subseteq \mathfrak m_{T'}$ be an ideal with $I\cdot\mathfrak m_{T'} = 0$. Let $V$ be a finite $k$-module, equipped also with a right $k$-action agreeing with the left one and with a $T'$-module structure compatible with the $k$-structure, and let $\iota : V \to T'$ be an injective $T'$-linear map whose image is $I$ viewed as a $T'$-submodule. Let $C$ be a flat $T'$-algebra, $q_Y : Y \to \operatorname{Spec} T'$ a scheme over $T'$, and $u, v, x : \operatorname{Spec} C \to Y$ three morphisms over $\operatorname{Spec} T'$ (each composing with $q_Y$ to $\operatorname{Spec}$ of the structure map $T' \to C$) such that $u$ and $v$, and $v$ and $x$, become equal after restriction along $\operatorname{Spec}$ of the quotient map $C \to C/IC$. Let $x_k : A_k \to \operatorname{Spec} k$ carry a relative group law $L_k$, i.e. functorial multiplication, unit and inversion on $T$-points over $k$, associative and unital with inverses, natural in the base. Let $W \subseteq A_k$ be open together with $a_W : W \to Y$ making the square formed by $a_W$, $W \hookrightarrow A_k \to \operatorname{Spec} k$, $q_Y$ and $\operatorname{Spec}$ of the residue map a pullback, and let $U_e \subseteq A_k$ be an affine open through which the unit section of $L_k$ at the identity factors, via $e_1$. Finally let $c_1, c_2, c_3$ be maps $\Gamma(A_k, U_e) \to \operatorname{Hom}_k(V^\vee, k \otimes_{T'} C)$ such that $c_1$, $c_2$, $c_3$ are tangent coordinates, via $a_W$ and $U_e$, of the pairs $(u,v)$, $(v,x)$, $(u,x)$ respectively: for each pair there are a morphism $w_0$ from $\operatorname{Spec}$ of `thickening T' V C` to $W$ lying over the relative tangent base of `thickeningSnd T' V C` and a morphism $w_1$ to $U_e$ such that $w_0$ followed by $a_W$ is a tangent of the pair in the sense that it factors as $\operatorname{Spec}$ of a Schlessinger-type ring map $\vartheta$ from `pairRing I C` to the thickening followed by some $\varphi : \operatorname{Spec}(\mathrm{pairRing}\,I\,C) \to Y$ restricting to the two members of the pair along `pairFst` and `pairSnd`; that $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ followed by the inclusion of $W$; and that the map equals `tangentCoords T' V C` of the chart ring homomorphism attached to $U_e$ and $w_1$. Then $c_3 = c_1 + c_2$.
--
--   This is the additivity (cocycle) property of the first-order difference coordinates attached to pairs of lifts of a morphism over a small extension: passing from $u$ to $x$ through $v$ adds the two tangent vectors, here in the variant where the target of the comparison chart is only an open subscheme $W$ of the special fibre, cartesian over $Y$. It is used in the computations showing that the associated two-cochain vanishes and in the construction of overlap isomorphisms whose cocycle is a coboundary of point derivations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add.lean

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

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u v x : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hx : x ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (hvx : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ x)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (c₁ c₂ c₃ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h₁ : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c₁)
    (h₂ : IsTangentCoordsOfPairAtVia I V ι C v x xk Lk W aW Ue c₂)
    (h₃ : IsTangentCoordsOfPairAtVia I V ι C u x xk Lk W aW Ue c₃) :
    c₃ = c₁ + c₂ := by sorry
