-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tail_pos_shift_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.tail_pos_shift_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:51.706663+00:00
-- url     : https://prove2.me/theorems/d36c28d8-b24e-488e-8417-b190bf7499a0
-- title:
--   Branching Dimensions: tail pos shift le
-- statement:
--   The Branching Dimensions construction uses the tail pos shift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L84-L99

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.tail_pos_shift_le (a b : ℕ → ℤ) (u : ℕ) :
    ∀ n, (∀ m, m + 1 < n + 1 → b (m + 1) ≤ a m) → tailPos (n + 1) b (u + 1) ≤ tailPos n a u := by sorry
