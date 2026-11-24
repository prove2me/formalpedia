-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_map_ofReal_mul
-- name    : CompanionTheory.ThKR.Mp.C.map_ofReal_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:01.66794+00:00
-- url     : https://prove2.me/theorems/5b4af298-4be3-4a9e-9045-d884f3053b7e
-- title:
--   C: map of Real mul
-- statement:
--   The C construction uses the map of Real mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L23-L26

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

theorem CompanionTheory.ThKR.Mp.C.map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by sorry
