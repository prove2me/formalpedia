-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_le_sum_hh
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.le_sum_hh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:49.210821+00:00
-- url     : https://prove2.me/theorems/60d5db8f-4202-4342-b9d6-588d161de84d
-- title:
--   TDim: le sum hh
-- statement:
--   The TDim construction uses the le sum hh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L63-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L63-L82

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.le_sum_hh {z L : ℝ} (hz : 0 ≤ z) (hL : Real.log (1 + z) ≤ L) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (k' : ℕ) :
    fT k' z - ((Icc 1 k' \ D).card : ℝ) * L ≤ ∑ d ∈ D, hh z d := by sorry
