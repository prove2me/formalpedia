-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_meas_perp
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.meas_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:26.217804+00:00
-- url     : https://prove2.me/theorems/a58b8552-0e81-46d1-b367-fc19b520172f
-- title:
--   Place Perm Operator Bicommutant Span: meas perp
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the meas perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L184-L186

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
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by sorry
