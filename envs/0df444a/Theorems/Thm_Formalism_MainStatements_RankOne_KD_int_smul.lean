-- Prove2me | Theorems.Thm_Formalism_MainStatements_RankOne_KD_int_smul
-- name    : Formalism.MainStatements.RankOne.KD.int_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:15.389812+00:00
-- url     : https://prove2.me/theorems/bbe80375-d414-5e64-9a2e-41050b869caa
-- title:
--   KD: int smul
-- statement:
--   The KD construction uses the int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L43-L45

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

theorem Formalism.MainStatements.RankOne.KD.int_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure Γ) [IsFiniteMeasure μ] (p : C(Γ, ℝ))
    {F : Γ → V} (hF : Continuous F) : Integrable (fun x => p x • F x) μ := by sorry
