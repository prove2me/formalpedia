-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_zmod_two_even_succ_iff
-- name    : Formalism.L2.FormalSeriesBounds.RF.zmod_two_even_succ_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:11.600068+00:00
-- url     : https://prove2.me/theorems/d42f2092-e26c-4cd5-a025-1e175be97307
-- title:
--   RF: zmod two even succ iff
-- statement:
--   The RF construction uses the zmod two even succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L184-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L184-L184

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

theorem Formalism.L2.FormalSeriesBounds.RF.zmod_two_even_succ_iff (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by sorry
