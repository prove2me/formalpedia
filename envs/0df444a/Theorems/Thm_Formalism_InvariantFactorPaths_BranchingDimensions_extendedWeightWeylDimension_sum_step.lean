-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_sum_step
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.sum_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:49.617734+00:00
-- url     : https://prove2.me/theorems/c45793c1-5a6c-587b-98fb-447e86d57835
-- title:
--   extended Weight Weyl Dimension: sum step
-- statement:
--   The extended Weight Weyl Dimension construction uses the sum step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L275-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L275-L329

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.sum_step (hP : PieriDim) (hBr : BranchDim) (D : Letters) (hW : D.Wf) (j : ℕ) (x : Fin D.k → ℤ)
    (hj : j < D.Ns) (hg : D.twGood j x) :
    ∑ᶠ (y : Fin D.k → ℤ) (_ : D.twStep (j + 1) x y), D.twG (j + 1) y = D.twG j x * D.twC (j + 1) := by sorry
