-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_henselSqrt
-- name    : Formalism.IndefR.LocBrg.henselSqrt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:55.060639+00:00
-- url     : https://prove2.me/theorems/ef3f2921-bb7f-4707-9350-9f392946d4f0
-- title:
--   Loc Brg: hensel Sqrt
-- statement:
--   The Loc Brg construction uses the hensel Sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L149-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L149-L192

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
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

theorem Formalism.IndefR.LocBrg.henselSqrt : HenselSqrt := by sorry
