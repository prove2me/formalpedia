-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ptFB_of
-- name    : Formalism.L2.FormalSeriesBounds.ptFB_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:54.285471+00:00
-- url     : https://prove2.me/theorems/426f7953-9fc3-5ad5-a5c0-8d90fce962b2
-- title:
--   Formal Series Bounds: pt FB of
-- statement:
--   The Formal Series Bounds construction uses the pt FB of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePPTFBSt.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePPTFBSt.lean#L22-L44

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePPTFBSt
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds

theorem Formalism.L2.FormalSeriesBounds.ptFB_of (hEx : PTExFBSt) (hAvg : PTAvgFBSt) (hG : GermIAllSt) (hStab : HStabFBSt) : PTFBSt := by sorry
