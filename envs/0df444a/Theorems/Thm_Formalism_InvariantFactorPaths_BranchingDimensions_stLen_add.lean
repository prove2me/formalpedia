-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_add
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.stLen_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:25.421938+00:00
-- url     : https://prove2.me/theorems/253e94a3-c5b4-4225-9dfe-ddc6ac45b96b
-- title:
--   Branching Dimensions: st Len add
-- statement:
--   The Branching Dimensions construction uses the st Len add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L240-L242

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.stLen_add (j : ℕ) : D.stLen (D.n0 + j) = D.k - j := by sorry
