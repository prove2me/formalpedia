-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_sb
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.fou_sb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:20.404978+00:00
-- url     : https://prove2.me/theorems/5cd56691-3736-4761-b610-66d73336fec0
-- title:
--   Place Perm Operator Bicommutant Span: fou sb
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the fou sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L255-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean#L255-L281

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by sorry
