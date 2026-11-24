-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_exp_mem_sp
-- name    : CompanionTheory.ThKR.Mp.exp_mem_sp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:32.369012+00:00
-- url     : https://prove2.me/theorems/aa8bc5d6-4323-4d4b-be9e-2c9da0ccd73e
-- title:
--   Mp: exp mem sp
-- statement:
--   The Mp construction uses the exp mem sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MpFOne.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MpFOne.lean#L54-L69

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
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
open scoped Real ContDiff RealInnerProductSpace
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.exp_mem_sp {X : Mat l} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    NormedSpace.exp X ∈ Matrix.symplecticGroup l ℝ := by sorry
