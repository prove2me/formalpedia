-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_pos_idx
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pos_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:47.460174+00:00
-- url     : https://prove2.me/theorems/522db95e-0816-4822-9ed8-de7c8160d8e1
-- title:
--   TDim: pos idx
-- statement:
--   The TDim construction uses the pos idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L98-L108

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
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
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pos_idx {n Ns : ℕ} {la : ℕ → ℤ} (h : Dom n la)
    (hc : ((range n).filter fun m => 0 < la m).card ≤ Ns) {i : ℕ} (hi : i < n) (hp : 0 < la i) :
    i < Ns := by sorry
