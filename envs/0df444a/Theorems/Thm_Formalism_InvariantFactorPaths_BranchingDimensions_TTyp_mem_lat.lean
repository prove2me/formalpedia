-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_mem_lat
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:14.510567+00:00
-- url     : https://prove2.me/theorems/ed9ba391-1a74-4008-a046-6e68d997b40c
-- title:
--   TTyp: mem lat
-- statement:
--   The TTyp construction uses the mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L126-L131

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat {q : ℕ → Bool} {B : ℕ → ℕ} {j x : ℕ} (h : x ∈ lat q B j) :
    ∃ l, 1 ≤ l ∧ l ≤ j ∧ q l = true ∧ x = B l := by sorry
