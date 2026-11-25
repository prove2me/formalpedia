-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_Tgt_weil_implication_nonarch_quadratic
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.weil_implication_nonarch_quadratic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:09.881864+00:00
-- url     : https://prove2.me/theorems/d28d436d-d955-4011-b892-f7ddbef7336e
-- title:
--   Tgt: weil implication nonarch quadratic
-- statement:
--   The Tgt construction uses the weil implication nonarch quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L54-L55

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.weil_implication_nonarch_quadratic : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → Impl ψ h B μ wMat (fou (chiB ψ B) μ) := by sorry
