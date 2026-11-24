-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_abel_tails
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.abel_tails
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:42.469969+00:00
-- url     : https://prove2.me/theorems/bd9f4ccd-6a65-4978-b09f-ec29887f970e
-- title:
--   Branching Dimensions: abel tails
-- statement:
--   The Branching Dimensions construction uses the abel tails property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L140-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L140-L155

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.abel_tails (g d : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ range L, g l * d l =
      ∑ u ∈ range L, (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u L, d l := by sorry
