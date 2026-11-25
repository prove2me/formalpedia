-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_leaf_holds
-- name    : Formalism.L2.FormalSeriesBounds.leaf_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:46.854893+00:00
-- url     : https://prove2.me/theorems/50850f6f-f797-4b58-aedd-28ff0f499513
-- title:
--   Formal Series Bounds: leaf holds
-- statement:
--   The Formal Series Bounds construction uses the leaf holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L75-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean#L75-L102

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
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

theorem Formalism.L2.FormalSeriesBounds.leaf_holds : LeafSt := by sorry
