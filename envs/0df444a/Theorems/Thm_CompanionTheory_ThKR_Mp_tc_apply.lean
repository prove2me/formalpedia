-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_tc_apply
-- name    : CompanionTheory.ThKR.Mp.tc_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:42.267393+00:00
-- url     : https://prove2.me/theorems/56a81d02-0e9d-4765-9b42-155b2a21f2a0
-- title:
--   Mp: tc apply
-- statement:
--   The Mp construction uses the tc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L104-L105

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.tc_apply (M : Matrix l l ℝ) (x : Eu l) (a : l) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) M x a = ∑ b, M a b * x b := by sorry
