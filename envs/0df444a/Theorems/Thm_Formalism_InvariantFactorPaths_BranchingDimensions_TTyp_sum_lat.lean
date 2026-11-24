-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_sum_lat
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:22.308723+00:00
-- url     : https://prove2.me/theorems/ab7e7eac-6c1b-432c-96cd-cd42e6d58bb3
-- title:
--   TTyp: sum lat
-- statement:
--   The TTyp construction uses the sum lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L102-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L102-L112

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat (g : ℕ → ℝ) (q : ℕ → Bool) (B : ℕ → ℕ) : ∀ n,
    ∑ l ∈ range (lat q B n).length, g ((lat q B n).getD l 0) =
      ∑ i ∈ (Icc 1 n).filter (fun i => q i = true), g (B i)
  := by sorry
