-- Prove2me | Theorems.Thm_Formalism_REAL_firstPositionSlice_indexArrayAction
-- name    : Formalism.REAL.firstPositionSlice_indexArrayAction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:26.953956+00:00
-- url     : https://prove2.me/theorems/7328c635-6269-433e-84e4-3c09ed6d49a5
-- title:
--   REAL: first Position Slice index Array Action
-- statement:
--   The REAL construction uses the first Position Slice index Array Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L439-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L439-L450

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

theorem Formalism.REAL.firstPositionSlice_indexArrayAction (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (arrE E (j+1) a b F) = arrE E 1 a b (sliceLin V n α' F) +
      ∑ k : Fin j, sliceLin V n α' (factorAction k.succ a b F) := by sorry
