-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pullback_inv_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/93da8055-c665-560d-b971-afa8a2991dee
-- title:
--   Invariance of geometric fibre h⁰ under an isomorphism over the base
-- statement:
--   Let $S$ be a commutative ring, let $A$ and $A'$ be schemes, and let $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$ be morphisms. Suppose $e : A \cong A'$ is an isomorphism of schemes compatible with the structure morphisms, in the sense that $e$ followed by $f'$ equals $f$. Let $M$ be an $\mathcal{O}_A$-module, let $k$ be a field and let $sk : S \to k$ be a ring homomorphism. The invariant `Scheme.Modules.geomFibreH0Finrank` attached to such data is, by definition, the $k$-dimension of the global sections of the pullback of the module to the base change: one forms the fibre product of the structure morphism with $\operatorname{Spec}$ of $sk$, makes the global sections of that fibre product a $k$-algebra via the inverse of the canonical isomorphism $k \cong \Gamma(\operatorname{Spec} k)$ followed by the map on sections induced by the second projection, pulls the module back along the first projection, and takes the rank of its module of global sections over $k$. The assertion is that this number, computed for $f'$ and for the pullback of $M$ along $e^{-1}$, equals the number computed for $f$ and $M$ itself, for the same $k$ and $sk$.
--
--   This is the transport statement saying that the fibrewise $h^0$ of a quasi-coherent module is unchanged when the total space is replaced by an isomorphic scheme over the same base, the module being carried along by the inverse isomorphism. It is used in the analysis of polarisation data, being cited by [`AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite`](thm.html#AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite) and by [`CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pullback_inv_of_iso
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S))
    (e : A ≅ A') (he : e.hom ≫ f' = f) (M : A.Modules)
    (k : Type u) [Field k] (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f' ((Scheme.Modules.pullback e.inv).obj M) k sk =
      Scheme.Modules.geomFibreH0Finrank f M k sk := by sorry
