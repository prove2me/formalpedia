-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cov_step
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.cov_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:43.139549+00:00
-- url     : https://prove2.me/theorems/468d07b4-1292-4137-8f24-526f38c2aa1b
-- title:
--   Branching Dimensions: cov step
-- statement:
--   The Branching Dimensions construction uses the cov step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L557-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L557-L565

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.cov_step (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = false) :
    HStrip D.k (ent mu (i + 1)) (ent mu i) ∧
      wsize D.k (ent mu i) - wsize D.k (ent mu (i + 1)) = D.B (i + 1) := by sorry
