-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_span
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sb_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:47.278132+00:00
-- url     : https://prove2.me/theorems/68ee7176-9d04-4b55-8f67-83cc28a98330
-- title:
--   Place Perm Operator Bicommutant Span: sb span
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L86-L105

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sb_span [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L := by sorry
