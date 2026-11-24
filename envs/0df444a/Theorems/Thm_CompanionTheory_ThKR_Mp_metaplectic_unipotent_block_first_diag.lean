-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_metaplectic_unipotent_block_first_diag
-- name    : CompanionTheory.ThKR.Mp.metaplectic_unipotent_block_first_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:35.819582+00:00
-- url     : https://prove2.me/theorems/dbc728fd-f8ce-4631-a110-e71ee995f8cc
-- title:
--   Mp: metaplectic unipotent block first diag
-- statement:
--   The Mp construction uses the metaplectic unipotent block first diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L107-L109

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

theorem CompanionTheory.ThKR.Mp.metaplectic_unipotent_block_first_diag (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inl Sum.inl (nn S t) = 1 := by sorry
