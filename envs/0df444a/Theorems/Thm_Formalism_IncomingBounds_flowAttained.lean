-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_flowAttained
-- name    : Formalism.IncomingBounds.flowAttained
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:31.679958+00:00
-- url     : https://prove2.me/theorems/89b6cd3d-6642-44c5-aaeb-0081f8b211ab
-- title:
--   Incoming Bounds: flow Attained
-- statement:
--   The Incoming Bounds construction uses the flow Attained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/WeightIdentities.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/WeightIdentities.lean#L16-L16

import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Series
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.flowAttained : FlowAttained := by sorry
