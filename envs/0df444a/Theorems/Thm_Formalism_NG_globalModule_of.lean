-- Prove2me | Theorems.Thm_Formalism_NG_globalModule_of
-- name    : Formalism.NG.globalModule_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:17.739848+00:00
-- url     : https://prove2.me/theorems/41ae67b9-fe98-4ec1-8f36-7bfcfffd2716
-- title:
--   NG: global Module of
-- statement:
--   The NG construction uses the global Module of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalModuleOf.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalModuleOf.lean#L14-L41

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
universe u v w x

theorem Formalism.NG.globalModule_of (hF : StatFinPres.{max u w, x}) : StatGlobalModule.{u, v, w, x} := by sorry
