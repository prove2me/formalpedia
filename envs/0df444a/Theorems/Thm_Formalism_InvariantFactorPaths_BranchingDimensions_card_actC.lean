-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_actC
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.card_actC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:38.879806+00:00
-- url     : https://prove2.me/theorems/22683fd8-bd43-47e3-bbbe-3bf6f13c6aab
-- title:
--   Branching Dimensions: card act C
-- statement:
--   The Branching Dimensions construction uses the card act C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L518-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L518-L528

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.card_actC (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actC D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card := by sorry
