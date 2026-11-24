-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_sp_mul
-- name    : CompanionTheory.ThKR.Mp.MpA.sp_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:44.581945+00:00
-- url     : https://prove2.me/theorems/1d6a6f61-7c79-4d55-b7ab-02dcd989ae97
-- title:
--   Mp A: sp mul
-- statement:
--   The Mp A construction uses the sp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L33-L35

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

theorem CompanionTheory.ThKR.Mp.MpA.sp_mul {X : Type} [TopologicalSpace X] {a b : X → Sp l} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x := by sorry
