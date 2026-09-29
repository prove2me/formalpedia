-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
-- name    : AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e2be7120-e8d3-53f3-b19d-b924d026f69b
-- title:
--   Existence of tangent coordinates for a pair, via an open
-- statement:
--   Let $T'$ be an Artinian local ring, $I\subseteq\mathfrak m$ an ideal with $I\,\mathfrak m=0$, and let $V$ be a $k$-module, $k=\mathrm{ResidueField}\,T'$ (with compatible left, right and $T'$-module structures and finite over $k$), together with a $T'$-linear map $\iota\colon V\to T'$ that is injective and has image exactly $I$ as $T'$-submodule. Let $C$ be a flat $T'$-algebra, $q_Y\colon Y\to\operatorname{Spec}T'$ a scheme over $T'$, and $u,v\colon\operatorname{Spec}C\to Y$ two morphisms over $T'$ which agree after reduction modulo $I\!\cdot\!C$, i.e. become equal upon precomposition with $\operatorname{Spec}$ of the quotient map $C\to C/I^{e}$, $I^{e}=I\,C$ the image ideal. Let $x_k\colon A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$ (functorial multiplication, unit, inverse on $T$-points over $\operatorname{Spec}k$, associative, unital, with inverses and natural in $T$), let $W\subseteq A_k$ be an open with a morphism $a_W\colon W\to Y$ making the square formed by $a_W$, $W\hookrightarrow A_k\to\operatorname{Spec}k$, $q_Y$ and $\operatorname{Spec}$ of the residue map $T'\to k$ cartesian, and let $U_e\subseteq A_k$ be an affine open containing the unit, in the sense that a morphism $e_1\colon\operatorname{Spec}k\to U_e$ is given whose composite with the inclusion is the underlying morphism of $L_k$'s unit section. Then there exists a function $c$ from $\Gamma(A_k,U_e)$ to $\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$ satisfying `IsTangentCoordsOfPairAtVia`: there are morphisms $w_0\colon\operatorname{Spec}E\to W$ and $w_1\colon\operatorname{Spec}E\to U_e$, where $E=(k\otimes_{T'}C)\otimes_k(k\oplus V)$ is the square-zero thickening, such that $w_0$ followed by $W\hookrightarrow A_k\to\operatorname{Spec}k$ is the structure morphism of the relative tangent base, such that $w_0$ followed by $a_W$ is a tangent morphism of the pair $(u,v)$ (it factors as $\operatorname{Spec}\vartheta$ followed by some $\varphi\colon\operatorname{Spec}\mathrm{pairRing}\,I\,C\to Y$ restricting to $u$ and $v$ along the two projections, for some Schlessinger map $\vartheta$), such that $w_1$ followed by $U_e\hookrightarrow A_k$ is the translate of $w_0$ to the unit under $L_k$, and such that $c$ is the tangent-coordinate function of the chart homomorphism determined by $w_1$.
--
--   This is the existence half of the construction of Schlessinger-style tangent coordinates attached to a pair of $I$-congruent points of $Y$, in the variant where the comparison with the special fibre is given only on an open $W\subseteq A_k$ that is cartesian over $\operatorname{Spec}k$ rather than on all of $A_k$. It supplies the cochains used in the cocycle and coboundary computations for the deformation-theoretic input to the Néron model and good-reduction arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia
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
    (v : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    ∃ c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)),
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c := by sorry
