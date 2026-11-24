-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_a_fin
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:04.816544+00:00
-- url     : https://prove2.me/theorems/d6482d4c-227a-44b6-9a52-b55bb6b7c20c
-- title:
--   TTyp: a fin
-- statement:
--   The TTyp construction uses the a fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L338-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L338-L344

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin {La b p k k' g : ℝ} (hLa : 0 < La) (hp : 0 < p) (hk : 0 < k) (hk' : 0 ≤ k')
    (hg0 : 0 < g) (hg : g ≤ 4 * b / p) : La * k' / (16 * k) ≤ (La * b / (p * k)) * k' / (4 * g) := by sorry
