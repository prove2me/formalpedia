-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_Tgt_c_impl_D
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_impl_D
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:37.438579+00:00
-- url     : https://prove2.me/theorems/1cb44bbd-a10d-4ffb-9a83-c1598bd5f97f
-- title:
--   Tgt: c impl D
-- statement:
--   The Tgt construction uses the c impl D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/WeilImplicationNonarchQuadratic.lean#L51-L52

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_impl_D : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (a : Rˣ) (m : ℝ), 0 < m → (∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) → Impl ψ h B μ (mMat a) (opD m (a : R)) := by sorry
