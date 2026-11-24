-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_core
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:24.621805+00:00
-- url     : https://prove2.me/theorems/750b9e0c-ac79-42d5-afcd-b1f44302f6b3
-- title:
--   Branch: core
-- statement:
--   The Branch construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L132-L144

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.core {n : ℕ} (mu : Fin (n + 1) → ℤ) (h : ∀ i : Fin n, mu i.succ ≤ mu i.castSucc) :
    (∏ j : Fin n, ((j : ℝ) + 1)) *
      ∑ la ∈ Fintype.piFinset (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)),
        (Matrix.vandermonde fun i : Fin n => (i : ℝ) - (la i : ℝ)).det =
      (Matrix.vandermonde fun i : Fin (n + 1) => (i : ℝ) - (mu i : ℝ)).det := by sorry
