-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_frame_sum
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.frame_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:23.829845+00:00
-- url     : https://prove2.me/theorems/2a5d2743-3e12-4664-b9ce-7c4571b1318f
-- title:
--   extended Weight Weyl Dimension: frame sum
-- statement:
--   The extended Weight Weyl Dimension construction uses the frame sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L151-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L151-L249

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.frame_sum (hBr : BranchDim) (k n c : ℕ) (hk : k = n + (c + 1)) (be : ℤ) (x : Fin k → ℤ)
    (hd : Dom k (extW x)) (h0 : extW x 0 ≤ be) (hh : ∀ m, m < c → extW x m = be) :
    ∑ᶠ (y : Fin k → ℤ) (_ : Dom k (extW y) ∧ HStrip k (extW x) (extW y) ∧ ∀ m, m < c + 1 → extW y m = be),
      weylDim n (fun l => extW y (l + (c + 1))) = weylDim (n + 1) (fun l => extW x (l + c)) := by sorry
