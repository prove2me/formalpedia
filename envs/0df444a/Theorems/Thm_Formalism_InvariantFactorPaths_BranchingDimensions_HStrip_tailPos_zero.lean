-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_zero
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:45.069621+00:00
-- url     : https://prove2.me/theorems/10410655-5449-4886-bc4b-79b853132e5a
-- title:
--   HStrip: tail Pos zero
-- statement:
--   The HStrip construction uses the tail Pos zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L125-L129

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_zero {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) :
    tailPos n b 0 - tailPos n a 0 ≤ wsize n b - wsize n a := by sorry
