-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_upperPart_unipotent_mul
-- name    : CompanionTheory.ThKR.Mp.upperPart_unipotent_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:12.464286+00:00
-- url     : https://prove2.me/theorems/338fd20d-e47c-4c53-8cfd-7a5898c860c8
-- title:
--   Mp: upper Part unipotent mul
-- statement:
--   The Mp construction uses the upper Part unipotent mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L86-L98

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

theorem CompanionTheory.ThKR.Mp.upperPart_unipotent_mul (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) :
    upperParabolic (nn S t * s) = upperParabolic s + (t : ℂ) • (S.map ofReal * loQ s) := by sorry
