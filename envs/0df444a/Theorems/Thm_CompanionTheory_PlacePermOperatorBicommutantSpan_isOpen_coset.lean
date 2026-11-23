-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_isOpen_coset
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.isOpen_coset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:18.560298+00:00
-- url     : https://prove2.me/theorems/cfbc07a6-d9d8-4791-a5d4-620fb36e57ac
-- title:
--   Place Perm Operator Bicommutant Span: is Open coset
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the is Open coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L46-L47

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} := by sorry
