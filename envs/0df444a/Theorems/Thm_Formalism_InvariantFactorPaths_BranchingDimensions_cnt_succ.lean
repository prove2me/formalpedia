-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_succ
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.cnt_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:33.045563+00:00
-- url     : https://prove2.me/theorems/a62be477-8f4c-4c6b-af3b-d8b99a319d68
-- title:
--   Branching Dimensions: cnt succ
-- statement:
--   The Branching Dimensions construction uses the cnt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L81-L93

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.cnt_succ (T Q r c : ℕ) (hQ : 1 ≤ Q) :
    cnt T Q (r + 1) c = ∑ a : Fin T, cnt T Q r (c + (Q - 1) * a) := by sorry
