-- Prove2me | Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
-- name    : AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/dbca6f05-98ef-56bd-bea5-39ae002b788a
-- title:
--   Valuative criterion with finite-residue-field DVRs over a ℤ-finite-type base
-- statement:
--   Let $B$ be a commutative ring that is of finite type as a $\mathbb{Z}$-algebra, let $X$ be a scheme, and let $f : X \to \operatorname{Spec} B$ be a morphism which is quasi-compact and locally of finite type. Assume the following lifting property: for every valuative commutative square $S$ for $f$ — that is, a valuation ring $S.R$ with fraction field $K$, a morphism $\operatorname{Spec} K \to X$ and a morphism $\operatorname{Spec} S.R \to \operatorname{Spec} B$ making the square with $f$ and the canonical map $\operatorname{Spec} K \to \operatorname{Spec} S.R$ commute — such that $S.R$ is a discrete valuation ring whose residue field is finite, the underlying commutative square admits a lift, i.e. there is a morphism $\operatorname{Spec} S.R \to X$ making both triangles commute. Then $f$ is universally closed. Thus, over a base of finite type over $\mathbb{Z}$, the valuative criterion for universal closedness need only be tested on discrete valuation rings with finite residue field, rather than on all valuation rings.
--
--   This is a sharpening, for bases of finite type over $\mathbb{Z}$, of the valuative criterion for universal closedness (EGA II 7.3.8, where discrete valuation rings suffice over a locally Noetherian base); the restriction to finite residue fields is available because schemes of finite type over $\mathbb{Z}$ are Jacobson with finite residue fields at closed points. It is used by the variant of the criterion in which the discrete valuation rings are moreover assumed adically complete, [`AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift`](thm.html#AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift), and by [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.universallyClosed_of_represents_of_finiteType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.universallyClosed_of_represents_of_finiteType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift
    {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [LocallyOfFiniteType f]
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift) :
    UniversallyClosed f := by sorry
