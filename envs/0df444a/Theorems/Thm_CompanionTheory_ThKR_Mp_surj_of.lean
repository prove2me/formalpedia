-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_surj_of
-- name    : CompanionTheory.ThKR.Mp.surj_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:47.564113+00:00
-- url     : https://prove2.me/theorems/bdf3d2b6-9ff8-4e7c-b777-3eb7c6adf447
-- title:
--   Mp: surj of
-- statement:
--   The Mp construction uses the surj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L194-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L194-L210

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
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
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C

theorem CompanionTheory.ThKR.Mp.surj_of (h1 : DdNe l) (h2 : SecEx l) : Surj l := by sorry
