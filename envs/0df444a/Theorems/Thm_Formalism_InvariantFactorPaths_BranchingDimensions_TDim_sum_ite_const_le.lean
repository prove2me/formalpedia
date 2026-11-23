-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_ite_const_le
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_ite_const_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:53.185409+00:00
-- url     : https://prove2.me/theorems/536ef5f0-5c5e-4295-a117-baed8de2f7b1
-- title:
--   TDim: sum ite const le
-- statement:
--   The TDim construction uses the sum ite const le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L309-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean#L309-L313

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
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
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_ite_const_le {n Ns : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hc : ((range n).filter p).card ≤ Ns) {c : ℝ} (h0 : 0 ≤ c) :
    ∑ i ∈ range n, (if p i then c else 0) ≤ (Ns : ℝ) * c := by sorry
