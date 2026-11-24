-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_vandermonde_eq_ff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_ff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:48.442691+00:00
-- url     : https://prove2.me/theorems/0f46a40a-f8de-42ff-ac0f-01d746486ef6
-- title:
--   Branch: det vandermonde eq ff
-- statement:
--   The Branch construction uses the det vandermonde eq ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean#L57-L63

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_ff {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.vandermonde v).det = (Matrix.of fun i j : Fin n => ff j (v i)).det := by sorry
