-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_term_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.term_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:51.412623+00:00
-- url     : https://prove2.me/theorems/518a5046-8c37-5f05-bae2-0b434c8cd43a
-- title:
--   extended Weight Weyl Dimension: term le
-- statement:
--   The extended Weight Weyl Dimension construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L40-L45

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.term_le {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) {m : ℕ} (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by sorry
