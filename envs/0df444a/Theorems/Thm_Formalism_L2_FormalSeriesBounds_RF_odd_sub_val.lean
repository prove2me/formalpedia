-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_odd_sub_val
-- name    : Formalism.L2.FormalSeriesBounds.RF.odd_sub_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:51.556821+00:00
-- url     : https://prove2.me/theorems/bfd2f2f3-a69c-4a44-a5b3-f39295aadf3e
-- title:
--   RF: odd sub val
-- statement:
--   The RF construction uses the odd sub val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L30-L40

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
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
open Formalism.IncomingBounds

theorem Formalism.L2.FormalSeriesBounds.RF.odd_sub_val {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by sorry
