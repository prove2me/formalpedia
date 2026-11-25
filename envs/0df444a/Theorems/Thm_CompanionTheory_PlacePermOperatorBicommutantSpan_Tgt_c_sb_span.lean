-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_Tgt_c_sb_span
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_sb_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:04.411423+00:00
-- url     : https://prove2.me/theorems/9ab61c41-123f-468e-b6fe-fce8d446d66d
-- title:
--   Tgt: c sb span
-- statement:
--   The Tgt construction uses the c sb span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L15-L19

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
open CompanionTheory.PlacePermOperatorBicommutantSpan

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_sb_span : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V, IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) → ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by sorry
