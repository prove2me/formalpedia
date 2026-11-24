-- Prove2me | Theorems.Thm_Formalism_REAL_indexArrayAction_mul_permutePositions
-- name    : Formalism.REAL.indexArrayAction_mul_permutePositions
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:05.034524+00:00
-- url     : https://prove2.me/theorems/594471b5-e968-49ba-a9a7-afce32c69755
-- title:
--   REAL: index Array Action mul permute Positions
-- statement:
--   The REAL construction uses the index Array Action mul permute Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L286-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L286-L290

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.indexArrayAction_mul_permutePositions (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (a b : Fin n) :
    arrE E j a b * permArr V n σ = permArr V n σ * arrE E j a b := by sorry
