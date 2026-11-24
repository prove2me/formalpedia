-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_upper
-- name    : CompanionTheory.ThKR.Mp.metaplectic_unipotent_block_upper
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:16.376487+00:00
-- url     : https://prove2.me/theorems/f19f0e5d-5ec1-4255-a8ad-17bd12980293
-- title:
--   Mp: metaplectic unipotent block upper
-- statement:
--   The Mp construction uses the metaplectic unipotent block upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L111-L114

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

theorem CompanionTheory.ThKR.Mp.metaplectic_unipotent_block_upper (S : Matrix l l ℝ) (t : ℝ) :
    bl Sum.inl Sum.inr (nn S t) = t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S := by sorry
