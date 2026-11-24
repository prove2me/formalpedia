-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_col_eq
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.col_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:31.326602+00:00
-- url     : https://prove2.me/theorems/e1cab08a-fbcf-4522-b9ad-0a69b078bc10
-- title:
--   A3comb: col eq
-- statement:
--   The A3comb construction uses the col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L429-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L429-L465

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.col_eq {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ)
    (h : ((rowsLt n (colHeight μ c)).filter fun m => m ∈ I c).card =
      ((rowsLt n (colHeight μ c)).filter fun m => m ∈ canIdx μ c).card) : I c = canIdx μ c := by sorry
