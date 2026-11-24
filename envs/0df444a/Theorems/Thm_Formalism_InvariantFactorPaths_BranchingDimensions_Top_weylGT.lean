-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Top_weylGT
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Top.weylGT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:03.531187+00:00
-- url     : https://prove2.me/theorems/e556d758-a912-4f32-bc86-efcc9947ed27
-- title:
--   Top: weyl GT
-- statement:
--   The Top construction uses the weyl GT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/FinalT.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/FinalT.lean#L13-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_FinalT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions Formalism.InvariantFactorPaths.BranchingDimensions.Top

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Top.weylGT : ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ) := by sorry
