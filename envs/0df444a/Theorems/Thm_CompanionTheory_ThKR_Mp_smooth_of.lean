-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_smooth_of
-- name    : CompanionTheory.ThKR.Mp.smooth_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:49.358549+00:00
-- url     : https://prove2.me/theorems/367adc66-7e7b-441d-a9a7-b3039934aa55
-- title:
--   Mp: smooth of
-- statement:
--   The Mp construction uses the smooth of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L87-L104

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOrb
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

theorem CompanionTheory.ThKR.Mp.smooth_of (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l := by sorry
