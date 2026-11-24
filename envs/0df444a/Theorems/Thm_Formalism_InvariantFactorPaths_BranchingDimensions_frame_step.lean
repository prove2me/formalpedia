-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_frame_step
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.frame_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:20.974926+00:00
-- url     : https://prove2.me/theorems/1f99176c-61a4-49f1-b0c1-aab97118496c
-- title:
--   Branching Dimensions: frame step
-- statement:
--   The Branching Dimensions construction uses the frame step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L530-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L530-L545

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.frame_step (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hi : i < D.Ns) (hn : D.n0 ≤ i) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u := by sorry
