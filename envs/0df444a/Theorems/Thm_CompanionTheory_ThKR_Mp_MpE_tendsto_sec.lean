-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_tendsto_sec
-- name    : CompanionTheory.ThKR.Mp.MpE.tendsto_sec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:35.852705+00:00
-- url     : https://prove2.me/theorems/fb96e268-ee85-4949-9d4f-9c6dc46a2b8f
-- title:
--   Mp E: tendsto sec
-- statement:
--   The Mp E construction uses the tendsto sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L37-L54

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
open CompanionTheory.ThKR.Mp.MpE

theorem CompanionTheory.ThKR.Mp.MpE.tendsto_sec (hD : SecDer l) (f : Sch l) :
    Tendsto (fun s : Sp l => schwartzToL2 l (sec s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by sorry
