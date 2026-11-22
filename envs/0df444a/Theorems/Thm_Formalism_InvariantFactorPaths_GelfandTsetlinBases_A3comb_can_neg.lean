-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_can_neg
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.can_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:41.201996+00:00
-- url     : https://prove2.me/theorems/fa8b9f2e-2b83-49ab-98c6-7e46976bb537
-- title:
--   A3comb: can neg
-- statement:
--   The A3comb construction uses the can neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L400-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L400-L405

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.can_neg {n : ℕ} (μ : Fin n → ℤ) {c : ℤ} (hc : ¬ 1 ≤ c) :
    canIdx μ c = (rowsLt n (colHeight μ c))ᶜ := by sorry
