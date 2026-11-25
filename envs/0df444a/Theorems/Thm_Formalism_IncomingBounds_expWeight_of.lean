-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_expWeight_of
-- name    : Formalism.IncomingBounds.expWeight_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:19.717144+00:00
-- url     : https://prove2.me/theorems/2d48d352-0949-4634-9808-9976d92f9e88
-- title:
--   Incoming Bounds: exp Weight of
-- statement:
--   The Incoming Bounds construction uses the exp Weight of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L158-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L158-L185

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

theorem Formalism.IncomingBounds.expWeight_of (hV : ValNat) : ExpWeight := by sorry
