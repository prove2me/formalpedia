-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_wsize_extW
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.WGT.wsize_extW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:59.868402+00:00
-- url     : https://prove2.me/theorems/d31e94a0-e02d-4bd8-9534-fca09a1c9822
-- title:
--   WGT: wsize ext W
-- statement:
--   The WGT construction uses the wsize ext W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L50-L52

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.WGT.wsize_extW {n : ℕ} (μ : Fin n → ℤ) : wsize n (extW μ) = ∑ m, μ m := by sorry
