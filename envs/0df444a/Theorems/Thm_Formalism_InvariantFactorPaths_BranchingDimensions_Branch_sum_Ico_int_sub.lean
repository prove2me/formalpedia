-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_Ico_int_sub
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_Ico_int_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:57.200248+00:00
-- url     : https://prove2.me/theorems/d3fcbbc5-56a6-4377-895c-b8ba34f8862c
-- title:
--   Branch: sum Ico int sub
-- statement:
--   The Branch construction uses the sum Ico int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L30-L36

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_Ico_int_sub (F : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∑ x ∈ Ico a b, (F (x + 1) - F x) = F b - F a := by sorry
