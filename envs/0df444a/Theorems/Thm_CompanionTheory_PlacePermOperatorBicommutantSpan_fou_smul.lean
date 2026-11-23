-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_smul
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.fou_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:42.380156+00:00
-- url     : https://prove2.me/theorems/ab18636b-585c-4cb1-9e54-c66c8550d026
-- title:
--   Place Perm Operator Bicommutant Span: fou smul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the fou smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L206-L208

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
omit h

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.fou_smul (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by sorry
