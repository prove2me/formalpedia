-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:41.251054+00:00
-- url     : https://prove2.me/theorems/45e62bbd-0334-438d-ba60-62df0f4265c7
-- title:
--   HStrip: tail Pos le
-- statement:
--   The HStrip construction uses the tail Pos le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L108-L109

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_le {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u := by sorry
