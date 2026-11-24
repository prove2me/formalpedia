-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_geom_range_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.geom_range_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:31.263183+00:00
-- url     : https://prove2.me/theorems/03371e7b-c127-40e1-9d5a-db8784aa5a98
-- title:
--   Branching Dimensions: geom range le
-- statement:
--   The Branching Dimensions construction uses the geom range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AdmissibleSmallRatio.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AdmissibleSmallRatio.lean#L10-L23

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementN
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AdmissibleSmallRatio
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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.geom_range_le (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by sorry
