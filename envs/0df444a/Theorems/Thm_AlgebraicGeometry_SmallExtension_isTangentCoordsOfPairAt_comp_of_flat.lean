-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c48fff5a-665c-5d3d-8a58-c36f43a0d562
-- title:
--   Naturality of pair tangent coordinates under flat algebra maps
-- statement:
--   Let $T'$ be an artinian local ring with residue field $k=$ `ResidueField T'`, let $I\subseteq T'$ be an ideal contained in the maximal ideal with $I\cdot\mathfrak m=0$, and let $V$ be a $k$-module, finite over $k$, carrying compatible left and right $k$-actions and a $T'$-module structure compatible with the $k$-action, together with an injective $T'$-linear map $\iota\colon V\to T'$ whose image is exactly $I$ (viewed as a $T'$-submodule). Let $C$ and $C'$ be $T'$-algebras with $C'$ flat over $T'$, let $h\colon C\to C'$ be a $T'$-algebra map, let $Y$ be a scheme and $u,v\colon \operatorname{Spec} C\to Y$ two morphisms. Let $x_k\colon A_k\to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L_k$ (functorial multiplication, unit, inverse on $T$-points over $\operatorname{Spec} k$, associative, unital, with inverses and natural in the parameter scheme), let $a_k\colon A_k\to Y$ and let $U_e\subseteq A_k$ be an open. Let $c$ assign to each $a\in\Gamma(A_k,U_e)$ a $k$-linear map $V^\vee\to k\otimes_{T'}C$, and assume `IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c`, i.e. there are $w_0\colon \operatorname{Spec}\big((k\otimes_{T'}C)\otimes_k k[V]\big)\to A_k$ lying over the base section attached to `thickeningSnd`, and $w_1$ from the same thickening into $U_e$, such that $w_0$ followed by $a_k$ is a tangent vector of the pair $(u,v)$ (there exist a ring map $\vartheta$ from `pairRing I C` to the thickening satisfying `IsSchlessingerMap`, and $\varphi\colon\operatorname{Spec}(\mathrm{pairRing}\,I\,C)\to Y$ restricting along `pairFst`, `pairSnd` to $u$ and $v$, with $w_0\,a_k=\operatorname{Spec}\vartheta$ followed by $\varphi$), such that $w_1$ followed by the inclusion $U_e\hookrightarrow A_k$ is the $L_k$-translate of $w_0$, and such that $c$ is `tangentCoords` of the ring homomorphism $\Gamma(A_k,U_e)\to(k\otimes_{T'}C)\otimes_k k[V]$ induced by $w_1$. The conclusion is that the same predicate holds for $C'$, with $u,v$ replaced by $\operatorname{Spec}(h)$ followed by $u$, respectively $v$, and with coordinate function $a\mapsto (\mathrm{id}_k\otimes h)\circ c(a)$. The proof uses neither the artinian hypothesis on $T'$ nor the finiteness of $V$ over $k$.
--
--   This is the naturality, under a flat change of the affine test algebra $C$ (typically restriction of sections to a smaller affine open, or an automorphism of the chart), of the canonical tangent coordinates attached to a pair of $C$-points of $Y$ relative to a group law on the special fibre. It is used in the comparison of local lifts over the members of an affine cover — for instance in the additivity statement [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq) and in the construction of the obstruction cocycle for lifting homomorphisms of abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat.lean

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

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] [Module.Flat T' C']
    (h : C →ₐ[T'] C')
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    IsTangentCoordsOfPairAt I V ι C'
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u) (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v) xk Lk ak Ue
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toLinearMap ∘ₗ c a) := by sorry
