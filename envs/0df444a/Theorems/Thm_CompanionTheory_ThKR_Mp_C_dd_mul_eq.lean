-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_dd_mul_eq
-- name    : CompanionTheory.ThKR.Mp.C.dd_mul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:11.271073+00:00
-- url     : https://prove2.me/theorems/03b25fb2-11d1-4aab-bb92-343035fffb65
-- title:
--   C: dd mul eq
-- statement:
--   The C construction uses the dd mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L31-L40

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

theorem CompanionTheory.ThKR.Mp.C.dd_mul_eq (s s' : Mat l) (hd : s.toBlocks₁₁.det ≠ 0) :
    dd (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (upperParabolic s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * loQ s').det := by sorry
