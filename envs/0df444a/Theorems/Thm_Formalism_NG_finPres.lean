-- Prove2me | Theorems.Thm_Formalism_NG_finPres
-- name    : Formalism.NG.finPres
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:33.299997+00:00
-- url     : https://prove2.me/theorems/45e4efdb-ef5e-4bee-bd50-186c3cb1e0b8
-- title:
--   NG: fin Pres
-- statement:
--   The NG construction uses the fin Pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CupKillAdm.lean#L275-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CupKillAdm.lean#L275-L295

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NG
open Module

theorem Formalism.NG.finPres : StatFinPres := by sorry
