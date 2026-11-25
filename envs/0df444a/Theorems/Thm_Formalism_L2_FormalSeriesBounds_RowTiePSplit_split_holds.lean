-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_split_holds
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.split_holds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:26.153057+00:00
-- url     : https://prove2.me/theorems/aba63cd7-2f28-4f29-a1f3-c8fbb62f81a8
-- title:
--   Row Tie PSplit: split holds
-- statement:
--   The Row Tie PSplit construction uses the split holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L159-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L159-L212

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.split_holds : SplitSt := by sorry
