-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_neg_active_zero
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.neg_active_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:13.298801+00:00
-- url     : https://prove2.me/theorems/df057be1-7f40-4d0f-a1cc-eb1547005cfd
-- title:
--   Branching Dimensions: neg active zero
-- statement:
--   The Branching Dimensions construction uses the neg active zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L624-L637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L624-L637

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.neg_active_zero (hP : D.IsPATH mu) (i : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailNeg (D.stLen i) (stage mu i) 0 ≤
      (D.SNeg 0 (i + 1) : ℤ) - D.SNeg 0 i := by sorry
