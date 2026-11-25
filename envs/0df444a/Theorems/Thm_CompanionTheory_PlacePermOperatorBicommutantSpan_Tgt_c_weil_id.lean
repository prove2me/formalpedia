-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_Tgt_c_weil_id
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_weil_id
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:10.771381+00:00
-- url     : https://prove2.me/theorems/9aa3f00a-2534-5d56-985a-e016bc856205
-- title:
--   Tgt: c weil id
-- statement:
--   The Tgt construction uses the c weil id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L57-L58

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_weil_id : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (b : Rˣ) (m : ℝ), 0 < m → (∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) → ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) = γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R) (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) := by sorry
