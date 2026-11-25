-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_expSeriesWeight
-- name    : Formalism.IncomingBounds.expSeriesWeight
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:06.819637+00:00
-- url     : https://prove2.me/theorems/6dfcc684-ad2d-4ac8-a627-855c6117e447
-- title:
--   Incoming Bounds: exp Series Weight
-- statement:
--   The Incoming Bounds construction uses the exp Series Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L205-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L205-L205

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.expSeriesWeight : ExpWeight := by sorry
