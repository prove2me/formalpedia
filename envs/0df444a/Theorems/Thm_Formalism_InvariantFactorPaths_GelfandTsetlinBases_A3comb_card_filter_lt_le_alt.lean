-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_card_filter_lt_le_alt
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.card_filter_lt_le_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:32.366894+00:00
-- url     : https://prove2.me/theorems/d2a4919e-8a60-410b-a9e1-f2061adee368
-- title:
--   A3comb: card filter lt le alt
-- statement:
--   The A3comb construction uses the card filter lt le alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L362-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean#L362-L393

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.card_filter_lt_le_alt {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = ((rowsLt n h)ᶜ).card) :
    ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ).card ≤ ((rowsLt n j).filter fun m => m ∈ J).card := by sorry
