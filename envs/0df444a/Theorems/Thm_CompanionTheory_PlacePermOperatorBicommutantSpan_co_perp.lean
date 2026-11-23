-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_perp
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.co_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:59.35988+00:00
-- url     : https://prove2.me/theorems/be398f3b-19d9-4f89-b98f-86c7ee1ed020
-- title:
--   Place Perm Operator Bicommutant Span: co perp
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the co perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L178-L179

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) := by sorry
