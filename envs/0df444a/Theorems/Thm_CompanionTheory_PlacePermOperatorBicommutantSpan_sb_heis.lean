-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_heis
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sb_heis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:00.602366+00:00
-- url     : https://prove2.me/theorems/d62e61c4-e7c2-4a0a-b15e-e477a8946a8a
-- title:
--   Place Perm Operator Bicommutant Span: sb heis
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb heis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L26-L34

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sb_heis (x y : ι → R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (Heisenberg₂ ψ h B x y φ) := by sorry
