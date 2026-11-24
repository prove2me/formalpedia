-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_det
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:01.51134+00:00
-- url     : https://prove2.me/theorems/3d37962e-3939-4dcc-8ab7-e04857d454cd
-- title:
--   Branch: sum det
-- statement:
--   The Branch construction uses the sum det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L65-L73

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_det {n : ℕ} (S : Fin n → Finset ℤ) (g : Fin n → ℤ → Fin n → ℝ) :
    ∑ r ∈ Fintype.piFinset S, (Matrix.of fun i j : Fin n => g i (r i) j).det =
      (Matrix.of fun i j : Fin n => ∑ x ∈ S i, g i x j).det := by sorry
