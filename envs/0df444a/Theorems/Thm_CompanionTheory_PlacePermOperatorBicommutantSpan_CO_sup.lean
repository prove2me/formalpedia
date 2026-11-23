-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_CO_sup
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.CO.sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:57.797472+00:00
-- url     : https://prove2.me/theorems/f0acd73c-0150-4b31-a98b-615fcb553df8
-- title:
--   CO: sup
-- statement:
--   The CO construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L40-L41

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') := by sorry
