-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_impl_mul
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.impl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:50.698548+00:00
-- url     : https://prove2.me/theorems/b65d166d-967d-4c46-8956-aa50403b383d
-- title:
--   Place Perm Operator Bicommutant Span: impl mul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the impl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L59-L73

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
omit H

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.impl_mul {g g' : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g' T') : Impl ψ h B μ (g * g') (T ∘ T') := by sorry
