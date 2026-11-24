-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_sum_drop
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_drop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:03.319324+00:00
-- url     : https://prove2.me/theorems/faef33c5-4a3a-4680-af62-bfc8dda7d8c4
-- title:
--   TTyp: sum drop
-- statement:
--   The TTyp construction uses the sum drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L89-L100

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_drop : ∀ (l : List ℕ) (u : ℕ), (l.drop u).sum = ∑ j ∈ Ico u l.length, l.getD j 0
  := by sorry
