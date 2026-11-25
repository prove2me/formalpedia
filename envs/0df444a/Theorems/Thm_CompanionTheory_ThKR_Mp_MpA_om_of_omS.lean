-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_om_of_omS
-- name    : CompanionTheory.ThKR.Mp.MpA.om_of_omS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:20:26.587142+00:00
-- url     : https://prove2.me/theorems/c5d6ef02-0dbd-4bd8-a271-ae10de4e9078
-- title:
--   Mp A: om of om S
-- statement:
--   The Mp A construction uses the om of om S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L111-L114

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

theorem CompanionTheory.ThKR.Mp.MpA.om_of_omS {g : G l} {c : ℂ} (hc : ∀ f, omS g f = c • f) (F : L2 l) : om g F = c • F := by sorry
