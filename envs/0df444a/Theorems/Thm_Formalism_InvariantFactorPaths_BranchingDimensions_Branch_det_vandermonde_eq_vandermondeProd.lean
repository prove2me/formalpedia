-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_vandermonde_eq_vandermondeProd
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_vandermondeProd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:23.223222+00:00
-- url     : https://prove2.me/theorems/69c13b6e-66c1-436e-b323-83fd67956e57
-- title:
--   Branch: det vandermonde eq vandermonde Prod
-- statement:
--   The Branch construction uses the det vandermonde eq vandermonde Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L92-L100

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_vandermondeProd (n : ℕ) (u : ℕ → ℝ) :
    (Matrix.vandermonde fun i : Fin n => u i).det = W n u := by sorry
