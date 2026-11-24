-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_split
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.583737+00:00
-- url     : https://prove2.me/theorems/966cab17-8574-423e-b5ff-cfda023c37b9
-- title:
--   TTyp: lat split
-- statement:
--   The TTyp construction uses the lat split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L114-L124

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_split (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) : ∀ d, ∃ pre : List ℕ,
    lat q B (i + d) = pre ++ lat q B i ∧
    pre.length = ((Icc (i + 1) (i + d)).filter (fun l => q l = true)).card
  := by sorry
