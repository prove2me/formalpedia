-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_ff_diff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.ff_diff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:15.287841+00:00
-- url     : https://prove2.me/theorems/25870ae6-f376-44e8-b9d8-18588c27b424
-- title:
--   Branch: ff diff
-- statement:
--   The Branch construction uses the ff diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L16-L28

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.ff_diff (j : ℕ) (x : ℝ) : ff (j + 1) (x + 1) - ff (j + 1) x = ((j : ℝ) + 1) * ff j x := by sorry
