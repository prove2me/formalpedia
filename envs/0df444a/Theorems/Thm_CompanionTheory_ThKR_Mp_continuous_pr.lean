-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_pr
-- name    : CompanionTheory.ThKR.Mp.continuous_pr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:04.453315+00:00
-- url     : https://prove2.me/theorems/2f62c494-faba-4175-bd0a-c247243abf91
-- title:
--   Mp: continuous pr
-- statement:
--   The Mp construction uses the continuous pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L112-L114

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

theorem CompanionTheory.ThKR.Mp.continuous_pr : Continuous (pr : G l → Sp l) := by sorry
