-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.n0_le_Ns
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:25.193561+00:00
-- url     : https://prove2.me/theorems/d967959c-c9aa-4f33-aeaa-a5ff5b3c8d5e
-- title:
--   Branching Dimensions: n0 le Ns
-- statement:
--   The Branching Dimensions construction uses the n0 le Ns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L217-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L217-L217

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.n0_le_Ns (D : Letters) : D.n0 ≤ D.Ns := by sorry
