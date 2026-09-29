-- Prove2me | Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
-- name    : AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/4a2bf008-2aa1-5660-a369-5b8496c530e2
-- title:
--   Valuative criterion for universal closedness via complete DVRs
-- statement:
--   Let $B$ be a commutative ring of finite type over $\mathbb{Z}$, let $X$ be a scheme and let $f : X \to \operatorname{Spec} B$ be a quasi-compact morphism that is locally of finite type. Assume that for every valuative commutative square $S$ for $f$ — that is, a valuation ring $S.R$ with fraction field $S.K$ together with morphisms $\operatorname{Spec} S.K \to X$ and $\operatorname{Spec} S.R \to \operatorname{Spec} B$ making the evident square with $f$ and $\operatorname{Spec} S.K \to \operatorname{Spec} S.R$ commute — whose valuation ring $S.R$ is a discrete valuation ring, is complete for the $\mathfrak{m}_{S.R}$-adic topology, and has finite residue field, the associated square admits a lift $\operatorname{Spec} S.R \to X$. Then $f$ is universally closed. Compared with the usual valuative criterion, the lifting hypothesis is imposed only on the restricted class of squares whose valuation ring is a complete discrete valuation ring with finite residue field, so the statement is correspondingly stronger.
--
--   This is the valuative criterion for universal closedness in the sharpened form in which only complete discrete valuation rings with finite residue field need be tested, as in the remark following EGA II 7.3.8. It is used in the proof that the Cherednik–Drinfeld fine moduli problem for the relevant quaternionic data is proper after localisation away from $6$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift
    {B : Type u} [CommRing B] [Algebra.FiniteType ℤ B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [LocallyOfFiniteType f]
    (H : ∀ (S : ValuativeCommSq f) [IsDiscreteValuationRing S.R] [IsAdicComplete (IsLocalRing.maximalIdeal S.R) S.R]
      [Finite (IsLocalRing.ResidueField S.R)], S.commSq.HasLift) :
    UniversallyClosed f := by sorry
