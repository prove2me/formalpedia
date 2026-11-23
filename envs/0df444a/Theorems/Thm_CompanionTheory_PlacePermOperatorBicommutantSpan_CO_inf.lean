-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_CO_inf
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.CO.inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:47.49669+00:00
-- url     : https://prove2.me/theorems/dcc671fb-cb6a-4df1-a697-d7999110c08a
-- title:
--   CO: inf
-- statement:
--   The CO construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L43-L44

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.CO.inf {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') := by sorry
