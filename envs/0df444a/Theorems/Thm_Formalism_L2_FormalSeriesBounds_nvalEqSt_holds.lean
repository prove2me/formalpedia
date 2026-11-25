-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_nvalEqSt_holds
-- name    : Formalism.L2.FormalSeriesBounds.nvalEqSt_holds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:46.463306+00:00
-- url     : https://prove2.me/theorems/59c29910-c078-44d0-ab0e-b0ce9263f2bd
-- title:
--   Formal Series Bounds: nval Eq St holds
-- statement:
--   The Formal Series Bounds construction uses the nval Eq St holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNvalEqSt.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePNvalEqSt.lean#L12-L28

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNvalEqSt
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

theorem Formalism.L2.FormalSeriesBounds.nvalEqSt_holds : NvalEqSt := by sorry
