-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_cnt_two
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.cnt_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:37.146279+00:00
-- url     : https://prove2.me/theorems/2eb7e3d2-53f0-4c10-9070-f4032b5c8d79
-- title:
--   Branching Dimensions: cnt two
-- statement:
--   The Branching Dimensions construction uses the cnt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L132-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean#L132-L160

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.cnt_two (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by sorry
