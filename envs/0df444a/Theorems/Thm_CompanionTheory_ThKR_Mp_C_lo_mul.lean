-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_lo_mul
-- name    : CompanionTheory.ThKR.Mp.C.lo_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:50.9469+00:00
-- url     : https://prove2.me/theorems/ce5df9c2-55b9-4e15-9724-43e9a40f7f61
-- title:
--   C: lo mul
-- statement:
--   The C construction uses the lo mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L155-L157

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
open CompanionTheory.ThKR.Mp.C

theorem CompanionTheory.ThKR.Mp.C.lo_mul (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by sorry
