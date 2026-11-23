-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_filter_Icc_succ
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.card_filter_Icc_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:20.450213+00:00
-- url     : https://prove2.me/theorems/13166dbc-3bbb-47ff-bdee-dafe8e97e3f0
-- title:
--   Branching Dimensions: card filter Icc succ
-- statement:
--   The Branching Dimensions construction uses the card filter Icc succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L17-L19

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.card_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (a i : ℕ) (h : a ≤ i + 1) :
    ((Icc a (i + 1)).filter p).card = ((Icc a i).filter p).card + if p (i + 1) then 1 else 0 := by sorry
