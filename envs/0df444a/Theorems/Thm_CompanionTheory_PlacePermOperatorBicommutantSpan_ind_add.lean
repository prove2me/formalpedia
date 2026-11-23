-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_add
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.ind_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:20.238303+00:00
-- url     : https://prove2.me/theorems/5208df8e-e2d5-406e-8f5b-19f6022849f5
-- title:
--   Place Perm Operator Bicommutant Span: ind add
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the ind add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L33-L34

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
omit [TopologicalSpace V]

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x := by sorry
