-- Prove2me | Theorems.Thm_Formalism_NG_globalConcrete_of
-- name    : Formalism.NG.globalConcrete_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:52.738444+00:00
-- url     : https://prove2.me/theorems/21882205-f189-47a9-9818-653eaf488355
-- title:
--   NG: global Concrete of
-- statement:
--   The NG construction uses the global Concrete of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L75-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean#L75-L166

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
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
universe u v w
open GlobalDeterminantRelations

theorem Formalism.NG.globalConcrete_of (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by sorry
