-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_vec_step
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.vec_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:54.934185+00:00
-- url     : https://prove2.me/theorems/3d013da9-6e56-4c16-880b-3f5edb9dfa67
-- title:
--   Branching Dimensions: vec step
-- statement:
--   The Branching Dimensions construction uses the vec step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L547-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L547-L555

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.vec_step (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = true) :
    HStrip D.k (ent mu i) (ent mu (i + 1)) ∧
      wsize D.k (ent mu (i + 1)) - wsize D.k (ent mu i) = D.B (i + 1) := by sorry
