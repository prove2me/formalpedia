-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pos_A
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.pos_A
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:40.460937+00:00
-- url     : https://prove2.me/theorems/17d1cc60-f96f-4827-b761-fb1e4257df58
-- title:
--   Branching Dimensions: pos A
-- statement:
--   The Branching Dimensions construction uses the pos A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L567-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L567-L577

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.pos_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos (u + 1) (i + 1) = D.SPos u i := by sorry
