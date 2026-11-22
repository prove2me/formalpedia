-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.stLen_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:20.468187+00:00
-- url     : https://prove2.me/theorems/19c743b5-0770-4db3-86a4-5b8b1a3ea634
-- title:
--   Branching Dimensions: st Len le
-- statement:
--   The Branching Dimensions construction uses the st Len le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L236-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L236-L238

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.stLen_le (i : ℕ) (h : i ≤ D.n0) : D.stLen i = D.k := by sorry
