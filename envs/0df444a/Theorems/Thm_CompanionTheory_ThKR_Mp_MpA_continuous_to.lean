-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_continuous_to
-- name    : CompanionTheory.ThKR.Mp.MpA.continuous_to
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:20.642983+00:00
-- url     : https://prove2.me/theorems/9e8daacb-e995-4c1b-a531-1ad33f43095a
-- title:
--   Mp A: continuous to
-- statement:
--   The Mp A construction uses the continuous to property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L29-L31

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA

theorem CompanionTheory.ThKR.Mp.MpA.continuous_to {X : Type} [TopologicalSpace X] {F : X → G l} (h1 : Continuous fun x => pr (F x))
    (h2 : ∀ f, Continuous fun x => om (F x) f) : Continuous F := by sorry
