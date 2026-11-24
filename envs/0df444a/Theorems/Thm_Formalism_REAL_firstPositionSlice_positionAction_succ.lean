-- Prove2me | Theorems.Thm_Formalism_REAL_firstPositionSlice_positionAction_succ
-- name    : Formalism.REAL.firstPositionSlice_positionAction_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:30.617801+00:00
-- url     : https://prove2.me/theorems/9a04da3a-dbf2-4105-98d5-0d3fb4ff2851
-- title:
--   REAL: first Position Slice position Action succ
-- statement:
--   The REAL construction uses the first Position Slice position Action succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L339-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L339-L355

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

theorem Formalism.REAL.firstPositionSlice_positionAction_succ (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (factorAction k.succ a b F) =
      (if (α' k).1 = a then sliceLin V n (Function.update α' k (b, (α' k).2)) F else (0 : Arr V n 1)) -
      (if (α' k).2 = b then sliceLin V n (Function.update α' k ((α' k).1, a)) F else (0 : Arr V n 1)) := by sorry
