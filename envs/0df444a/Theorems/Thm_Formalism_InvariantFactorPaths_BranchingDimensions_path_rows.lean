-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_path_rows
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.path_rows
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:16.590115+00:00
-- url     : https://prove2.me/theorems/5f09273e-4d2c-4fc3-848c-f66a12fda816
-- title:
--   Branching Dimensions: path rows
-- statement:
--   The Branching Dimensions construction uses the path rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L290-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L290-L316

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.path_rows (hP : D.IsPATH mu) : ∀ i, i ≤ D.Ns →
    (∀ m, D.nVec i ≤ m → m < D.k → ent mu i m ≤ 0) ∧ ∀ m, m + D.nCov i < D.k → 0 ≤ ent mu i m := by sorry
