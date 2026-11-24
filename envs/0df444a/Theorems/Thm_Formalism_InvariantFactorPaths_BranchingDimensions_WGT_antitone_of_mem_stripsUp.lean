-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_antitone_of_mem_stripsUp
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.WGT.antitone_of_mem_stripsUp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:51.465601+00:00
-- url     : https://prove2.me/theorems/a26337a6-975f-4e0f-8a5b-b041900d4e1e
-- title:
--   WGT: antitone of mem strips Up
-- statement:
--   The WGT construction uses the antitone of mem strips Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L87-L95

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
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
open Formalism.InvariantFactorPaths.BranchingDimensions.WGT
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)

theorem Formalism.InvariantFactorPaths.BranchingDimensions.WGT.antitone_of_mem_stripsUp {n : ℕ} {μ ν : Fin n → ℤ} {B : ℕ} (h : ν ∈ stripsUp μ B) : Antitone ν := by sorry
