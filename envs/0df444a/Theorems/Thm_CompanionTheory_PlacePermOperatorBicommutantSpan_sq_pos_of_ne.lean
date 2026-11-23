-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sq_pos_of_ne
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sq_pos_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:59.047102+00:00
-- url     : https://prove2.me/theorems/5df3419c-c5b6-43f9-bc47-1357aeaff241
-- title:
--   Place Perm Operator Bicommutant Span: sq pos of ne
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sq pos of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L137-L145

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sq_pos_of_ne {φ : (ι → R) → ℂ} (hφ : SB φ) (hne : φ ≠ 0) : ∫ u, ‖φ u‖ ^ 2 ∂μ ≠ 0 := by sorry
