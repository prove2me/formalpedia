-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_smulRange
-- name    : Formalism.NG.QuotientPowerLengths.mem_smulRange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:52.131397+00:00
-- url     : https://prove2.me/theorems/c91cbf01-8f0e-46ec-8966-8fe332a29f8d
-- title:
--   Quotient Power Lengths: mem smul Range
-- statement:
--   The Quotient Power Lengths construction uses the mem smul Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L17-L21

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

theorem Formalism.NG.QuotientPowerLengths.mem_smulRange {M : Type*} [AddCommGroup M] [Module O M] (l : O) (x : M) :
    x ∈ smulRange M l ↔ ∃ y, l • y = x := by sorry
