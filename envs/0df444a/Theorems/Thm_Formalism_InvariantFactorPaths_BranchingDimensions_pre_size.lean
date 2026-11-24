-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_size
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.pre_size
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:58.991323+00:00
-- url     : https://prove2.me/theorems/1e678802-87ea-4cd8-bc1d-e3f05f37e88a
-- title:
--   Branching Dimensions: pre size
-- statement:
--   The Branching Dimensions construction uses the pre size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L257-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L257-L288

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
variable {D : Letters} {mu : D.Stages}

theorem Formalism.InvariantFactorPaths.BranchingDimensions.pre_size (hk : 1 ≤ D.k) (hP : D.IsPre mu) : ∀ i, i ≤ D.n0 →
    -((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = false), D.B l : ℕ) : ℤ) ≤ ent mu i (D.k - 1) ∧
    ent mu i 0 ≤ ((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = true), D.B l : ℕ) : ℤ) := by sorry
