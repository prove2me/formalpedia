-- Prove2me | Theorems.Thm_Formalism_NG_genericFin
-- name    : Formalism.NG.genericFin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:31.436845+00:00
-- url     : https://prove2.me/theorems/0e35a4f2-a68a-4561-bcef-206500a9049b
-- title:
--   NG: generic Fin
-- statement:
--   The NG construction uses the generic Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L29-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L29-L134

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
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

theorem Formalism.NG.genericFin : StatGenericFin := by sorry
