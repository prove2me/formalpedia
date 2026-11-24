-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_ff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_ff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:02.368508+00:00
-- url     : https://prove2.me/theorems/03fdcd18-c0a2-4586-8fea-dd3de2986173
-- title:
--   Branch: sum ff
-- statement:
--   The Branch construction uses the sum ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L38-L55

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_ff (j : ℕ) (c : ℝ) (a b : ℤ) (h : a ≤ b) :
    ((j : ℝ) + 1) * ∑ x ∈ Icc a b, ff j (c - (x : ℝ)) =
      ff (j + 1) (c + 1 - (a : ℝ)) - ff (j + 1) (c - (b : ℝ)) := by sorry
