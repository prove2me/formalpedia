-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_pos_row
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pos_row
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:53.93382+00:00
-- url     : https://prove2.me/theorems/00679f23-9f9b-4dcb-bad8-cfcb074dd039
-- title:
--   TDim: pos row
-- statement:
--   The TDim construction uses the pos row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L122-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L122-L195

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pos_row {r K Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (h2 : 2 * Ns ≤ K) (hK : K ≤ n) (hn : n ≤ r + K)
    (hd : Dom n la) (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns) (hL0 : 0 ≤ L)
    {i : ℕ} (hi : i < n) (hp : 0 < la i) (hL : Real.log (1 + ((la i : ℤ) : ℝ)) ≤ L) :
    fT (K - 2 * Ns) (la i : ℝ) - (Ns : ℝ) * L ≤
        ∑ j ∈ Ico (i + 1) n, (if la j = 0 then hh (la i : ℝ) (j - i) else 0) ∧
      ∑ j ∈ Ico (i + 1) n, (if la j = 0 then hh (la i : ℝ) (j - i) else 0) ≤
        fT (K - 2 * Ns) (la i : ℝ) + ((r : ℝ) + 2 * Ns) * L := by sorry
