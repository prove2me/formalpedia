-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_shift
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:07.839101+00:00
-- url     : https://prove2.me/theorems/9efb612d-227a-45e6-a0af-9ddf6c72125a
-- title:
--   TTyp: lat shift
-- statement:
--   The TTyp construction uses the lat shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L150-L158

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_shift (q : ℕ → Bool) (B : ℕ → ℕ) {i n : ℕ} (h : i ≤ n) :
    (∀ u, (lat q B n).getD (u + ((Icc (i + 1) n).filter (fun l => q l = true)).card) 0 =
      (lat q B i).getD u 0) ∧
    (lat q B n).length = ((Icc (i + 1) n).filter (fun l => q l = true)).card + (lat q B i).length := by sorry
