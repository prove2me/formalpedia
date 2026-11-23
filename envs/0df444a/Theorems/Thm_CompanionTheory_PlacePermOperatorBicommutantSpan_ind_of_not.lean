-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_not
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.ind_of_not
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:30.215936+00:00
-- url     : https://prove2.me/theorems/b3f41946-7dc2-4db0-a8b2-ff76fb0cd9a3
-- title:
--   Place Perm Operator Bicommutant Span: ind of not
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the ind of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L23-L24

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 := by sorry
