-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_hasDerivAt
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.fT_hasDerivAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:08.635949+00:00
-- url     : https://prove2.me/theorems/593e47e0-b987-4523-b7a1-09e4cbb5ae04
-- title:
--   Branching Dimensions: f T has Deriv At
-- statement:
--   The Branching Dimensions construction uses the f T has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L42-L55

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.fT_hasDerivAt (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : HasDerivAt (fT k') (fT' k' y) y := by sorry
