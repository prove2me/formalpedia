-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_pa_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_pa_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:25.336799+00:00
-- url     : https://prove2.me/theorems/16c4ae92-13bd-44f8-921d-cb214780aca1
-- title:
--   TDim: sum pa le
-- statement:
--   The TDim construction uses the sum pa le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L365-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L365-L421

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_pa_le {Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (hL0 : 0 ≤ L)
    (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns)
    (hG : ∀ i j, i < j → j < n → G la i j ≤ L) :
    ∑ j ∈ range n, ∑ i ∈ range j, pa la i j ≤ 4 * (Ns : ℝ) ^ 2 * L := by sorry
