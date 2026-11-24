-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_W_id_ne_zero
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.W_id_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:48.72496+00:00
-- url     : https://prove2.me/theorems/2ad7f28b-0eb7-438a-94d4-cb35ef22866d
-- title:
--   Branch: W id ne zero
-- statement:
--   The Branch construction uses the W id ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L115-L119

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.W_id_ne_zero (n : ℕ) : W n (fun m => (m : ℝ)) ≠ 0 := by sorry
