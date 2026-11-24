-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_precomplete_of_surjective
-- name    : Formalism.NG.IdemLiftAlt.precomplete_of_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:31.013057+00:00
-- url     : https://prove2.me/theorems/122743de-6f72-4707-8d2c-cfd6d0b38bb8
-- title:
--   Idem Lift Alt: precomplete of surjective
-- statement:
--   The Idem Lift Alt construction uses the precomplete of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L85-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L85-L124

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

theorem Formalism.NG.IdemLiftAlt.precomplete_of_surjective (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [IsPrecomplete I M] (π : M →ₗ[O] N)
    (hπ : Function.Surjective π) : IsPrecomplete I N := by sorry
