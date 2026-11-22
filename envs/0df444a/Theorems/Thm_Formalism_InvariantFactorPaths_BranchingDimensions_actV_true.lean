-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_actV_true
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.actV_true
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:10.637442+00:00
-- url     : https://prove2.me/theorems/a2d76de2-220f-4f73-bb12-1dc056b1f61b
-- title:
--   Branching Dimensions: act V true
-- statement:
--   The Branching Dimensions construction uses the act V true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L500-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L500-L501

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.actV_true {l : ℕ} : actV D l = true ↔ l ≤ D.n0 ∧ D.vec l = true := by sorry
