-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_precomplete_of_finite
-- name    : Formalism.NG.IdemLiftAlt.precomplete_of_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:17.906337+00:00
-- url     : https://prove2.me/theorems/e614fa82-37bb-4c5c-815d-9dea8dcd15f2
-- title:
--   Idem Lift Alt: precomplete of finite
-- statement:
--   The Idem Lift Alt construction uses the precomplete of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L126-L130

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

theorem Formalism.NG.IdemLiftAlt.precomplete_of_finite (I : Ideal O) [IsNoetherianRing O] [IsAdicComplete I O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by sorry
