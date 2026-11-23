-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_hstrip_iff
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.WGT.hstrip_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:24.157715+00:00
-- url     : https://prove2.me/theorems/61392f46-d511-4f15-9d20-abd6589f8030
-- title:
--   WGT: hstrip iff
-- statement:
--   The WGT construction uses the hstrip iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L54-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/WeylGT.lean#L54-L85

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.WGT.hstrip_iff {n : ℕ} (μ ν : Fin n → ℤ) (B : ℕ) :
    (HStrip n (extW μ) (extW ν) ∧ wsize n (extW ν) - wsize n (extW μ) = B) ↔ ν ∈ stripsUp μ B := by sorry
