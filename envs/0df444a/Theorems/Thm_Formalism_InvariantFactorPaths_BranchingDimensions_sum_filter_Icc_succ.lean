-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_sum_filter_Icc_succ
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.sum_filter_Icc_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:17.19178+00:00
-- url     : https://prove2.me/theorems/f3999884-9741-46e1-aed7-f7fcbe225c52
-- title:
--   Branching Dimensions: sum filter Icc succ
-- statement:
--   The Branching Dimensions construction uses the sum filter Icc succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L12-L15

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.sum_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) (a i : ℕ) (h : a ≤ i + 1) :
    ∑ l ∈ (Icc a (i + 1)).filter p, f l =
      (∑ l ∈ (Icc a i).filter p, f l) + if p (i + 1) then f (i + 1) else 0 := by sorry
