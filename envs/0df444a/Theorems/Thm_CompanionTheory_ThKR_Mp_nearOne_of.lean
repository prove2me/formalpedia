-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_nearOne_of
-- name    : CompanionTheory.ThKR.Mp.nearOne_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:02.084424+00:00
-- url     : https://prove2.me/theorems/a6b975a0-b27d-4f0e-9c11-dc9efd932348
-- title:
--   Mp: near One of
-- statement:
--   The Mp construction uses the near One of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L68-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L68-L103

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

theorem CompanionTheory.ThKR.Mp.nearOne_of (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by sorry
