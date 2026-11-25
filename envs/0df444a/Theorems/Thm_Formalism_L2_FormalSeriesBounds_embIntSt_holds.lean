-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_embIntSt_holds
-- name    : Formalism.L2.FormalSeriesBounds.embIntSt_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:32.531557+00:00
-- url     : https://prove2.me/theorems/19371b94-c6f2-4e06-ae07-5ca35a34d20a
-- title:
--   Formal Series Bounds: emb Int St holds
-- statement:
--   The Formal Series Bounds construction uses the emb Int St holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePEmbIntSt.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePEmbIntSt.lean#L24-L39

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.embIntSt_holds : EmbIntSt := by sorry
