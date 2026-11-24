-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_upperPart_mul
-- name    : CompanionTheory.ThKR.Mp.C.upperPart_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:06.448918+00:00
-- url     : https://prove2.me/theorems/ce08fc7f-3e0a-42bf-9d1b-d424d803ea9b
-- title:
--   C: upper Part mul
-- statement:
--   The C construction uses the upper Part mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L14-L21

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

theorem CompanionTheory.ThKR.Mp.C.upperPart_mul (s s' : Mat l) :
    upperParabolic (s * s') = s.toBlocks₁₁.map Complex.ofReal * upperParabolic s' + s.toBlocks₁₂.map Complex.ofReal * loQ s' := by sorry
