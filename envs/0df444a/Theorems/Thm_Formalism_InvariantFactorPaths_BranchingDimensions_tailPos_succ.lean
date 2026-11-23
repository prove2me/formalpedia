-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_succ
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.tailPos_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:38.118811+00:00
-- url     : https://prove2.me/theorems/bf4352c2-7641-4320-a8ac-72c631553775
-- title:
--   Branching Dimensions: tail Pos succ
-- statement:
--   The Branching Dimensions construction uses the tail Pos succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L65-L68

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.tailPos_succ (n : ℕ) (la : ℕ → ℤ) (u : ℕ) :
    tailPos (n + 1) la u = tailPos n la u + if u ≤ n then max (la n) 0 else 0 := by sorry
