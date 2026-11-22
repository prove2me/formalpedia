-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_quot_mono
-- name    : Formalism.NG.QuotientPowerLengths.quot_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:36.47196+00:00
-- url     : https://prove2.me/theorems/91565a34-8e69-415e-a6a8-c2c8ec6c4d1b
-- title:
--   Quotient Power Lengths: quot mono
-- statement:
--   The Quotient Power Lengths construction uses the quot mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L23-L25

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

theorem Formalism.NG.QuotientPowerLengths.quot_mono {M : Type*} [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O (M ⧸ B) ≤ Module.length O (M ⧸ A) := by sorry
