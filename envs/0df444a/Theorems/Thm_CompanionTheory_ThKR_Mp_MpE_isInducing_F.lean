-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_isInducing_F
-- name    : CompanionTheory.ThKR.Mp.MpE.isInducing_F
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:48.210928+00:00
-- url     : https://prove2.me/theorems/06417001-c52a-4b54-a632-cb82bb0cd5e1
-- title:
--   Mp E: is Inducing F
-- statement:
--   The Mp E construction uses the is Inducing F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L107-L108

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE
open CompanionTheory.ThKR.Mp.MpE

theorem CompanionTheory.ThKR.Mp.MpE.isInducing_F :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := by sorry
