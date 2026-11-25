-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_trueT_iff
-- name    : Formalism.L2.FormalSeriesBounds.RF.trueT_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:16:47.895375+00:00
-- url     : https://prove2.me/theorems/856def37-8149-4a51-8130-e85eb9120e20
-- title:
--   RF: true T iff
-- statement:
--   The RF construction uses the true T iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCDeg.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCDeg.lean#L12-L15

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem Formalism.L2.FormalSeriesBounds.RF.trueT_iff (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by sorry
