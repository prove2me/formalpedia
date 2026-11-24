-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_exists_sch_ne
-- name    : CompanionTheory.ThKR.Mp.MpE.exists_sch_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:20:08.661798+00:00
-- url     : https://prove2.me/theorems/e961264b-1a44-47fa-baef-17da66097931
-- title:
--   Mp E: exists sch ne
-- statement:
--   The Mp E construction uses the exists sch ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L56-L62

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

theorem CompanionTheory.ThKR.Mp.MpE.exists_sch_ne : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by sorry
