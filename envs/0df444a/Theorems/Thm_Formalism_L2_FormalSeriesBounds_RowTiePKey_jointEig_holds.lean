-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePKey_jointEig_holds
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePKey.jointEig_holds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:13.221796+00:00
-- url     : https://prove2.me/theorems/59dd03f5-ab91-562d-99e2-040bf282436d
-- title:
--   Row Tie PKey: joint Eig holds
-- statement:
--   The Row Tie PKey construction uses the joint Eig holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePKeyJoint.lean#L77-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePKeyJoint.lean#L77-L98

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJointDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePKey

theorem Formalism.L2.FormalSeriesBounds.RowTiePKey.jointEig_holds : JointEigSt := by sorry
