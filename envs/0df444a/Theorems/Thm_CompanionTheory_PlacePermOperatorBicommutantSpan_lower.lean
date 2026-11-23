-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_lower
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:35.805301+00:00
-- url     : https://prove2.me/theorems/bc986a31-4f25-43e4-884d-725ee1b51c1c
-- title:
--   Place Perm Operator Bicommutant Span: lower
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/Nuabs.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/Nuabs.lean#L8-L35

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_Nuabs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∀ φ : G → ℝ≥0∞, Continuous φ → (∀ c ∈ C, φ c ≠ 0) → ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ p ∈ P, ∀ c ∈ C, m ≤ ∫⁻ q, φ (q⁻¹ * (p * c)) ∂ν := by sorry
