-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_length_quot_smulRange_free
-- name    : Formalism.NG.QuotientPowerLengths.length_quot_smulRange_free
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:07.13626+00:00
-- url     : https://prove2.me/theorems/36c3b115-ebfd-4c21-9b03-46bde0ed7e71
-- title:
--   Quotient Power Lengths: length quot smul Range free
-- statement:
--   The Quotient Power Lengths construction uses the length quot smul Range free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L146-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L146-L178

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.QuotientPowerLengths.length_quot_smulRange_free (Q : Type*) [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    [IsTorsionFree O Q] (l : O) :
    Module.length O (Q ⧸ smulRange Q l) = finrank O Q * addVal O l := by sorry
