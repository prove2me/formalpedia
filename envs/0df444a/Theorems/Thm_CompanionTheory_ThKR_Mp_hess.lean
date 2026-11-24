-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_hess
-- name    : CompanionTheory.ThKR.Mp.hess
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:37.597924+00:00
-- url     : https://prove2.me/theorems/4fcb8c84-3a9c-4a03-87bc-2ed5760b499c
-- title:
--   Mp: hess
-- statement:
--   The Mp construction uses the hess property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L235-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L235-L254

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

theorem CompanionTheory.ThKR.Mp.hess {s : Mat l} {H : Sch l} (hA : Ann s H) (j k : l) :
    ∑ a, upperParabolic s a j * (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} H)) 0 =
      -(2 * π * I) * loQ s k j * H 0 := by sorry
