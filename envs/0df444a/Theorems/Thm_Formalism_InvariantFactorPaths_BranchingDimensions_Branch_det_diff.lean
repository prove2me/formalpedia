-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_diff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:53.191822+00:00
-- url     : https://prove2.me/theorems/a8b9d450-e26c-4a71-8b1b-a5874d9ebccf
-- title:
--   Branch: det diff
-- statement:
--   The Branch construction uses the det diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L75-L88

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_diff {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : ∀ i, M i 0 = 1) :
    M.det = (Matrix.of fun i j : Fin n => M i.succ j.succ - M i.castSucc j.succ).det := by sorry
