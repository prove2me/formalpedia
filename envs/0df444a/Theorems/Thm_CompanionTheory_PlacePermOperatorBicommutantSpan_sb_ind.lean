-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_ind
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sb_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:49.698809+00:00
-- url     : https://prove2.me/theorems/55a0a934-55cb-46a5-9335-32ac9eaab51f
-- title:
--   Place Perm Operator Bicommutant Span: sb ind
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L55-L61

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
variable [IsTopologicalAddGroup V]

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by sorry
