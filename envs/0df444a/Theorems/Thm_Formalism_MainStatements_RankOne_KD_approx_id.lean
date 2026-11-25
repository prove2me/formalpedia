-- Prove2me | Theorems.Thm_Formalism_MainStatements_RankOne_KD_approx_id
-- name    : Formalism.MainStatements.RankOne.KD.approx_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:19:09.966237+00:00
-- url     : https://prove2.me/theorems/1209649a-12f6-5043-a399-8f7015f1a6e0
-- title:
--   KD: approx id
-- statement:
--   The KD construction uses the approx id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L47-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L47-L104

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]

theorem Formalism.MainStatements.RankOne.KD.approx_id {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (μ : Measure Γ)
    [IsFiniteMeasure μ] [IsOpenPosMeasure μ] (A : Subalgebra ℝ C(Γ, ℝ)) (hA : A.SeparatesPoints) {ι : Type} [Fintype ι]
    {F : ι → Γ → V} (hF : ∀ i, Continuous (F i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p ∈ A, ∀ i, ‖F i 1 - ∫ x, p x • F i x ∂μ‖ < δ := by sorry
