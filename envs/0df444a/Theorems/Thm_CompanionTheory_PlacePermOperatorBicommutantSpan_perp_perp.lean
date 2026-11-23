-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_perp_perp
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.perp_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:59.781774+00:00
-- url     : https://prove2.me/theorems/8fccb711-73ff-45f3-997c-14882681aa73
-- title:
--   Place Perm Operator Bicommutant Span: perp perp
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the perp perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L181-L182

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.perp_perp {L : AddSubgroup V} (hL : CO L) (x : V) : x ∈ perpG h (perpG h L) ↔ x ∈ L := by sorry
