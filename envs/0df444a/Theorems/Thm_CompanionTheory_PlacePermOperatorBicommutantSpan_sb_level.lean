-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_level
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.sb_level
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:30.458401+00:00
-- url     : https://prove2.me/theorems/575a9c23-1942-4a4e-949d-09c20190f73d
-- title:
--   Place Perm Operator Bicommutant Span: sb level
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L123-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L123-L152

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.sb_level (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by sorry
