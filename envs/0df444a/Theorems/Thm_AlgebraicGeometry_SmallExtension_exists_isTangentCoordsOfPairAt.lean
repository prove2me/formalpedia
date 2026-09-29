-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
-- name    : AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ccd6a63d-f79b-567e-9fa8-7fd2ad488556
-- title:
--   Existence of tangent coordinates at the unit for a pair
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k =$ `ResidueField T'`, let $I \subseteq T'$ be an ideal with $I \le \mathfrak m$ and $I\mathfrak m = 0$, and let $V$ be a $k$-module, finite over $k$, carrying compatible left and right $k$-actions and a $T'$-module structure via the scalar tower, together with an injective $T'$-linear map $\iota : V \to T'$ whose range is $I$ (viewed as a $T'$-submodule). Let $C$ be a flat $T'$-algebra, let $q_Y : Y \to \operatorname{Spec} T'$ be a scheme over $T'$, and let $u, v : \operatorname{Spec} C \to Y$ be two morphisms over $T'$ (i.e. both composed with $q_Y$ give $\operatorname{Spec}$ of the structure map $T' \to C$) which agree after composition with $\operatorname{Spec}$ of the quotient map $C \to C/IC$. Let $x_k : A_k \to \operatorname{Spec} k$ and $a_k : A_k \to Y$ exhibit $A_k$ as the fibre product of $q_Y$ with $\operatorname{Spec}$ of the residue map $T' \to k$, let $L_k$ be a relative group law on $x_k$ (multiplication, unit and inverse on $T$-points over $\operatorname{Spec} k$, with associativity, unit and inverse laws and compatibility with base change), let $U_e \subseteq A_k$ be an affine open, and let $e_1 : \operatorname{Spec} k \to U_e$ be a factorisation of the unit section $L_k.\mathrm{one}$ of the group law through $U_e$. Then there exists a function $c$ from $\Gamma(A_k, U_e)$ to the $k$-linear maps $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} C)$ such that `IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c` holds, i.e. there are a morphism $w_0$ from $\operatorname{Spec}$ of the thickening $E = (k \otimes_{T'} C) \otimes_k (k \oplus V)$ (trivial square-zero extension in the second factor) to $A_k$ lying over the canonical base morphism, and a morphism $w_1 : \operatorname{Spec} E \to U_e$, such that $w_0$ followed by $a_k$ is a tangent morphism of the pair $(u,v)$ — it factors as $\operatorname{Spec}\vartheta$ followed by a morphism $\varphi : \operatorname{Spec}(\text{pairRing } I\,C) \to Y$ pulling back to $u$ and $v$ along the two projections, for some ring map $\vartheta$ from the pair ring to $E$ satisfying `IsSchlessingerMap I V ι C ϑ` — such that $w_1$ followed by the open immersion of $U_e$ is the left translate of $w_0$ to the unit, and such that $c$ is obtained from the chart ring homomorphism attached to $w_1$ by taking the $V$-component of the image of a section and reading it as an element of $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} C)$.
--
--   This is the existence half of the construction of tangent coordinates at the unit for a pair of $C$-points of $Y$ that agree modulo $IC$: the Schlessinger-type tangent morphism of the pair is translated to the group-law unit and read off in an open chart around it. It feeds the additivity and obstruction-cocycle computations for the abelian-scheme property bundle, notably the derivation property of the resulting coordinates and the identification of local obstruction classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt
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
    (v : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    ∃ c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)),
      IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c := by sorry
