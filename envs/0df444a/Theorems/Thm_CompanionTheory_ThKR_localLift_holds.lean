-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_localLift_holds
-- name    : CompanionTheory.ThKR.localLift_holds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:17:49.571328+00:00
-- url     : https://prove2.me/theorems/76c651d3-e47f-4fcc-b709-b123a88c2cfd
-- title:
--   Th KR: local Lift holds
-- statement:
--   The Th KR construction uses the local Lift holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L153-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L153-L228

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR
open LL

theorem CompanionTheory.ThKR.localLift_holds : LocalLift := by sorry
