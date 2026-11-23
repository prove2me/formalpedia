-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_hh_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_hh_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.264799+00:00
-- url     : https://prove2.me/theorems/2d084e3e-d587-4408-9473-d8cda4423c34
-- title:
--   TDim: sum hh le
-- statement:
--   The TDim construction uses the sum hh le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L43-L61

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_hh_le {z L : ℝ} (hz : 0 ≤ z) (hL : Real.log (1 + z) ≤ L) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (k' : ℕ) :
    ∑ d ∈ D, hh z d ≤ fT k' z + ((D \ Icc 1 k').card : ℝ) * L := by sorry
