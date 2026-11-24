-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pos_I
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.pos_I
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:16.074877+00:00
-- url     : https://prove2.me/theorems/0e2c3569-9747-4198-8563-4e78d12e32e6
-- title:
--   Branching Dimensions: pos I
-- statement:
--   The Branching Dimensions construction uses the pos I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L593-L610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L593-L610

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.pos_I (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actV D (i + 1) = false) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos u (i + 1) = D.SPos u i := by sorry
