-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_neg_row
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.neg_row
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.534591+00:00
-- url     : https://prove2.me/theorems/21cba04e-d1c9-4e22-b289-6fb0ca27e431
-- title:
--   TDim: neg row
-- statement:
--   The TDim construction uses the neg row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L197-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L197-L272

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.neg_row {r K Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (h2 : 2 * Ns ≤ K) (hK : K ≤ n) (hn : n ≤ r + K)
    (hd : Dom n la) (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns) (hL0 : 0 ≤ L)
    {j : ℕ} (hj : j < n) (hp : la j < 0) (hL : Real.log (1 + ((-la j : ℤ) : ℝ)) ≤ L) :
    fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) - (Ns : ℝ) * L ≤
        ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ∧
      ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ≤
        fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) + ((r : ℝ) + 2 * Ns) * L := by sorry
