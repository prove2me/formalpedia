-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_Tgt_c_schur
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_schur
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:40.172808+00:00
-- url     : https://prove2.me/theorems/306095ed-957a-4728-933c-22451d6fe25e
-- title:
--   Tgt: c schur
-- statement:
--   The Tgt construction uses the c schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L36-L37

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_schur : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ T : (V → ℂ) → (V → ℂ), (∀ φ, SB φ → SB (T φ)) → (∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ') → (∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) → (∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u) → (∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) → ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by sorry
