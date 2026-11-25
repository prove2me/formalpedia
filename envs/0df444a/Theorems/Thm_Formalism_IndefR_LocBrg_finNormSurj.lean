-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_finNormSurj
-- name    : Formalism.IndefR.LocBrg.finNormSurj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:59.624676+00:00
-- url     : https://prove2.me/theorems/b88d070c-2f10-4a03-a86a-6cf61cb0bd5e
-- title:
--   Loc Brg: fin Norm Surj
-- statement:
--   The Loc Brg construction uses the fin Norm Surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittFN.lean#L7-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittFN.lean#L7-L87

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittFN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg

theorem Formalism.IndefR.LocBrg.finNormSurj : FinNormSurj := by sorry
