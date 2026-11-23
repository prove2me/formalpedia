-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_sum
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sb_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:08.011056+00:00
-- url     : https://prove2.me/theorems/02139b51-370d-4bd1-a08c-831b72084402
-- title:
--   Place Perm Operator Bicommutant Span: sb sum
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L79-L80

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
omit [AddCommGroup V]

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sb_sum {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) := by sorry
