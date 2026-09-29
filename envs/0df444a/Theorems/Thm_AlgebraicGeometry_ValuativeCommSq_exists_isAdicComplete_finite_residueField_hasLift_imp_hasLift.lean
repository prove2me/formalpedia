-- Prove2me | Theorems.Thm_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
-- name    : AlgebraicGeometry.ValuativeCommSq.exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e2df65d4-0235-5cdc-964a-dc916492458e
-- title:
--   Reduction of valuative squares to complete discrete valuation rings
-- statement:
--   Let $X$ and $Y$ be schemes in a fixed universe, let $f : X \to Y$ be a morphism, and let $S$ be a valuative commutative square for $f$: a valuation ring $S.R$ with fraction field $S.K$ together with morphisms $\operatorname{Spec} S.K \to X$ and $\operatorname{Spec} S.R \to Y$ forming, with $f$ and the morphism $\operatorname{Spec} S.K \to \operatorname{Spec} S.R$ induced by the inclusion, a commutative square `S.commSq`. Assume in addition that $S.R$ is a discrete valuation ring and that its residue field is finite. Then there exists a valuative commutative square $S'$ for the same morphism $f$ such that $S'.R$ is a discrete valuation ring, is complete for the adic topology of its maximal ideal, has finite residue field, and such that the existence of a lift $\operatorname{Spec} S'.R \to X$ for the square `S'.commSq` implies the existence of a lift $\operatorname{Spec} S.R \to X$ for the original square `S.commSq`. No relation between $S'$ and $S$ beyond this implication on liftability is asserted.
--
--   This is the reduction step allowing the valuative criterion for universal closedness to be tested only on complete discrete valuation rings with finite residue field: the new square is obtained by base change to the $\mathfrak m$-adic completion of $S.R$, whose properties come from [`IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete`](thm.html#IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete). It is used by [`AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift`](thm.html#AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ValuativeCommSq_exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ValuativeCommSq.exists_isAdicComplete_finite_residueField_hasLift_imp_hasLift
    {X Y : Scheme.{u}} (f : X ⟶ Y) (S : ValuativeCommSq f)
    [IsDiscreteValuationRing S.R] [Finite (IsLocalRing.ResidueField S.R)] :
    ∃ S' : ValuativeCommSq f, IsDiscreteValuationRing S'.R ∧ IsAdicComplete (IsLocalRing.maximalIdeal S'.R) S'.R ∧
      Finite (IsLocalRing.ResidueField S'.R) ∧ (S'.commSq.HasLift → S.commSq.HasLift) := by sorry
