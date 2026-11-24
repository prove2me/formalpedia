-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_wsize_eq_tails
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.wsize_eq_tails
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:20.190821+00:00
-- url     : https://prove2.me/theorems/bdce3b68-7cb4-4a97-840a-131ad875f31e
-- title:
--   Branching Dimensions: wsize eq tails
-- statement:
--   The Branching Dimensions construction uses the wsize eq tails property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L111-L123

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.wsize_eq_tails (n : ℕ) (a : ℕ → ℤ) : wsize n a = tailPos n a 0 - tailPos n (revW n a) 0 := by sorry
