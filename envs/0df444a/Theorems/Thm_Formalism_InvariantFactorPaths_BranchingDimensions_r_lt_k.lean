-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_r_lt_k
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.r_lt_k
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:17.030356+00:00
-- url     : https://prove2.me/theorems/f4bded1c-2da9-4b4e-9217-686fa7d55d9b
-- title:
--   Branching Dimensions: r lt k
-- statement:
--   The Branching Dimensions construction uses the r lt k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L224-L227

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.r_lt_k (hW : D.Wf) : D.r < D.k := by sorry
