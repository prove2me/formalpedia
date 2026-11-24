-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_C_sec_apply_zero
-- name    : CompanionTheory.ThKR.Mp.C.sec_apply_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:06.503649+00:00
-- url     : https://prove2.me/theorems/a06eca88-6821-44e8-94e1-88fbbda65ee3
-- title:
--   C: sec apply zero
-- statement:
--   The C construction uses the sec apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MapOfRealMul.lean#L72-L77

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

theorem CompanionTheory.ThKR.Mp.C.sec_apply_zero (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by sorry
