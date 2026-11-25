-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_tcoordFB_holds
-- name    : Formalism.L2.FormalSeriesBounds.tcoordFB_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:38.646969+00:00
-- url     : https://prove2.me/theorems/b658895b-fdc3-4c24-9aea-68ce14bd0849
-- title:
--   Formal Series Bounds: tcoord FB holds
-- statement:
--   The Formal Series Bounds construction uses the tcoord FB holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieP_TCoord.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieP_TCoord.lean#L133-L139

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieP_TCoord
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.tcoordFB_holds : AllFB fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc := by sorry
