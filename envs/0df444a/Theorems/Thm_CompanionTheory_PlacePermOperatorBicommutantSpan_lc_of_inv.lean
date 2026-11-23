-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_lc_of_inv
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.lc_of_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:43.290024+00:00
-- url     : https://prove2.me/theorems/6531785d-7fc7-4a4f-abbb-feca229d0379
-- title:
--   Place Perm Operator Bicommutant Span: lc of inv
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the lc of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L49-L53

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f := by sorry
