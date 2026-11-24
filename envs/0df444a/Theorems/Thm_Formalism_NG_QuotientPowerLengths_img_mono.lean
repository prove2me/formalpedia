-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_img_mono
-- name    : Formalism.NG.QuotientPowerLengths.img_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:55.044474+00:00
-- url     : https://prove2.me/theorems/659170a5-e91a-466a-84a0-3dca5d00c693
-- title:
--   Quotient Power Lengths: img mono
-- statement:
--   The Quotient Power Lengths construction uses the img mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L344-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L344-L349

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
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]

theorem Formalism.NG.QuotientPowerLengths.img_mono {E : Set (Module.End (FractionRing O) V)} {N N' : Submodule O V} (h : N ≤ N') :
    img E N ≤ img E N' := by sorry
