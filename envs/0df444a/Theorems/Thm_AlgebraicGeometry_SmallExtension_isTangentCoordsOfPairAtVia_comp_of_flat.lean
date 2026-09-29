-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/68615f2b-1a7a-5cd4-965d-3409a76db737
-- title:
--   Naturality of pair tangent coordinates under flat chart change
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k = \mathrm{ResidueField}\,T'$, let $I \subseteq \mathfrak m$ be an ideal with $I\cdot\mathfrak m = 0$, and let $V$ be a $k$-vector space, finite over $k$, carrying left and right $k$-actions that agree and a $T'$-module structure compatible with the $k$-action, together with an injective $T'$-linear map $\iota \colon V \to T'$ whose range is $I$ viewed as a $T'$-submodule. Let $C$ and $C'$ be $T'$-algebras with $C'$ flat over $T'$, and $h \colon C \to C'$ a $T'$-algebra map. Let $Y$ be a scheme, $u, v \colon \operatorname{Spec} C \to Y$ two morphisms, $x_k \colon A_k \to \operatorname{Spec} k$ a scheme over $k$ equipped with a relative group law $L_k$ (functorial group structure on $T$-points over $\operatorname{Spec} k$, natural in the parameter scheme), $W \subseteq A_k$ an open with a morphism $a_W \colon W \to Y$, $U_e \subseteq A_k$ an open, and $c \colon \Gamma(A_k, U_e) \to \mathrm{Hom}_k(V^\vee, k \otimes_{T'} C)$. Assume `IsTangentCoordsOfPairAtVia` holds for these data over $C$: there are morphisms $w_0 \colon \operatorname{Spec} E \to W$, where $E = (k \otimes_{T'} C) \otimes_k (k \oplus V)$ is the thickening, with $w_0$ followed by the inclusion of $W$ and by $x_k$ equal to the base morphism attached to the second projection of $E$, and $w_1 \colon \operatorname{Spec} E \to U_e$, such that $w_0$ followed by $a_W$ is a tangent morphism of the pair $(u,v)$ in the sense of `IsTangentOfPair`, such that $w_1$ followed by the inclusion of $U_e$ is the $L_k$-left translate to the unit of $w_0$ followed by the inclusion of $W$, and such that $c$ is obtained by taking, for each section $a$, the $V$-component of the image of $a$ under the ring map $\Gamma(A_k,U_e) \to E$ induced by $w_1$, read as a $k$-linear map $V^\vee \to k \otimes_{T'} C$. The conclusion is that the same predicate holds over $C'$ for the pair $(\operatorname{Spec}(h) \text{ followed by } u,\ \operatorname{Spec}(h) \text{ followed by } v)$, with the same $x_k$, $L_k$, $W$, $a_W$, $U_e$, and with coordinate function $a \mapsto (\mathrm{id}_k \otimes h) \circ c(a)$. Neither the finiteness of $V$ over $k$ nor the Artinian hypothesis on $T'$ is used in the proof.
--
--   This is the naturality in the affine chart of the canonical tangent coordinates attached to a pair of points of $Y$ over a small extension, in the variant where the target morphism is defined only on an open $W$ of the special fibre rather than on all of $A_k$; no cartesian hypothesis on the data enters. It is used in the cocycle computations that compare such coordinate systems over overlaps, for instance in [`AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin`](thm.html#AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin) and [`AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary`](thm.html#AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat.lean

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

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat
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
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c) :
    IsTangentCoordsOfPairAtVia I V ι C'
      (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ u) (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ v) xk Lk W aW Ue
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toLinearMap ∘ₗ c a) := by sorry
