-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_twG_early
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.twG_early
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:12.469833+00:00
-- url     : https://prove2.me/theorems/30abca8a-091c-48f4-9810-6db99dd1fbf5
-- title:
--   extended Weight Weyl Dimension: tw G early
-- statement:
--   The extended Weight Weyl Dimension construction uses the tw G early property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L269-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L269-L273

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.twG_early (D : Letters) {j : ℕ} (hj : j ≤ D.n0) (x : Fin D.k → ℤ) :
    D.twG j x = weylDim D.k (extW x) := by sorry
