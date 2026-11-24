-- Prove2me | Theorems.Thm_Formalism_NG_QuotientPowerLengths_img_le
-- name    : Formalism.NG.QuotientPowerLengths.img_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:15.044375+00:00
-- url     : https://prove2.me/theorems/e1cfe5b7-854e-4d1d-a2c4-07cd9f0f8b5b
-- title:
--   Quotient Power Lengths: img le
-- statement:
--   The Quotient Power Lengths construction uses the img le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L337-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L337-L342

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

theorem Formalism.NG.QuotientPowerLengths.img_le {E : Set (Module.End (FractionRing O) V)} {N : Submodule O V}
    (hNE : ∀ f ∈ E, ∀ n ∈ N, f n ∈ N) : img E N ≤ N := by sorry
