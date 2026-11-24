-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_det_map_ofReal
-- name    : CompanionTheory.ThKR.Mp.C.det_map_ofReal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:35.989707+00:00
-- url     : https://prove2.me/theorems/087ea1a3-5056-4078-9a52-d77fbd145b70
-- title:
--   C: det map of Real
-- statement:
--   The C construction uses the det map of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L28-L29

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
open CompanionTheory.ThKR.Mp.C

theorem CompanionTheory.ThKR.Mp.C.det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) := by sorry
