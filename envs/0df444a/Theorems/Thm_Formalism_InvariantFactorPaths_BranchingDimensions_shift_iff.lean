-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_shift_iff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.shift_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:46.514471+00:00
-- url     : https://prove2.me/theorems/a7e9e0bb-0ac7-493d-8f93-c3f922247186
-- title:
--   Branching Dimensions: shift iff
-- statement:
--   The Branching Dimensions construction uses the shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L59-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L59-L79

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.shift_iff (Q a s c : ℕ) (hQ : 1 ≤ Q) :
    (a + s) % Q = c % Q ↔ s % Q = (c + (Q - 1) * a) % Q := by sorry
