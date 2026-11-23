-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Dom_anti
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.Dom.anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:55.552983+00:00
-- url     : https://prove2.me/theorems/6f9a2120-d4a7-48df-8d6b-054bb78a0176
-- title:
--   Dom: anti
-- statement:
--   The Dom construction uses the anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L21-L25

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.Dom.anti {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) : ∀ a b, a ≤ b → b < n → la b ≤ la a := by sorry
