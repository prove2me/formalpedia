-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestC_succ
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.latestC_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:51.201858+00:00
-- url     : https://prove2.me/theorems/a0d182de-0939-469a-bb42-1509e4b4b207
-- title:
--   Branching Dimensions: latest C succ
-- statement:
--   The Branching Dimensions construction uses the latest C succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L479-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L479-L483

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
variable {D : Letters} {mu : D.Stages}

theorem Formalism.InvariantFactorPaths.BranchingDimensions.latestC_succ (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestC (i + 1) = if (!D.vec (i + 1)) = true then D.B (i + 1) :: D.latestC i else D.latestC i := by sorry
