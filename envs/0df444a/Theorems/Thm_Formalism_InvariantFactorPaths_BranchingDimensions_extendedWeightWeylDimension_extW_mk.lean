-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_mk
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.extW_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:20.465207+00:00
-- url     : https://prove2.me/theorems/7dab7355-1afe-41da-865b-35aec615416b
-- title:
--   extended Weight Weyl Dimension: ext W mk
-- statement:
--   The extended Weight Weyl Dimension construction uses the ext W mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L17-L20

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.extW_mk {n : ℕ} (f : ℕ → ℤ) (m : ℕ) :
    extW (fun l : Fin n => f l.val) m = if m < n then f m else 0 := by sorry
