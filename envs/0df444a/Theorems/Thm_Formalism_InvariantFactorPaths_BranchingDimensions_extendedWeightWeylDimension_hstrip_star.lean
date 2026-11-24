-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_hstrip_star
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.hstrip_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:10.044823+00:00
-- url     : https://prove2.me/theorems/c49a9f8d-ccac-4d92-bf05-9cbdcaf30265
-- title:
--   extended Weight Weyl Dimension: hstrip star
-- statement:
--   The extended Weight Weyl Dimension construction uses the hstrip star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L63-L75

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.hstrip_star {n : ℕ} {a b : Fin n → ℤ} (h : HStrip n (extW a) (extW b)) :
    HStrip n (extW (star b)) (extW (star a)) := by sorry
