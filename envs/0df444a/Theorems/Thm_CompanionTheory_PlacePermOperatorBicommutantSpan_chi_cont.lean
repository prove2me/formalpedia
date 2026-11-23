-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_chi_cont
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.chi_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:04.88888+00:00
-- url     : https://prove2.me/theorems/63abad86-6cb8-4748-b2fe-c2a565eb82e3
-- title:
--   Place Perm Operator Bicommutant Span: chi cont
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the chi cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L162-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L162-L162

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.chi_cont : Continuous fun p : V × V => χ p.1 p.2 := by sorry
