-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_pair
-- name    : CompanionTheory.ThKR.Mp.continuous_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:22.997635+00:00
-- url     : https://prove2.me/theorems/1e24f079-4762-4071-bc38-3681540fa499
-- title:
--   Mp: continuous pair
-- statement:
--   The Mp construction uses the continuous pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L109-L110

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
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
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}

theorem CompanionTheory.ThKR.Mp.continuous_pair : Continuous fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)) := by sorry
