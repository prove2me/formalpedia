-- Prove2me | Theorems.Thm_Formalism_REAL_firstPositionSlice_positionAction_succ_apply
-- name    : Formalism.REAL.firstPositionSlice_positionAction_succ_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:39.69254+00:00
-- url     : https://prove2.me/theorems/fce24b13-4099-4126-8d29-a45020b6dee9
-- title:
--   REAL: first Position Slice position Action succ apply
-- statement:
--   The REAL construction uses the first Position Slice position Action succ apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L331-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L331-L337

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

theorem Formalism.REAL.firstPositionSlice_positionAction_succ_apply (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) (β : Fin 1 → Fin n × Fin n) :
    sliceLin V n α' (factorAction k.succ a b F) β =
      (if (α' k).1 = a then F (Fin.cons (β 0) (Function.update α' k (b, (α' k).2))) else 0) -
      (if (α' k).2 = b then F (Fin.cons (β 0) (Function.update α' k ((α' k).1, a))) else 0) := by sorry
