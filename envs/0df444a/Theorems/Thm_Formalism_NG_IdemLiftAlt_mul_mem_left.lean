-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_left
-- name    : Formalism.NG.IdemLiftAlt.mul_mem_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:29.819603+00:00
-- url     : https://prove2.me/theorems/8e5767d6-617a-42a0-b3ed-dac121cf017e
-- title:
--   Idem Lift Alt: mul mem left
-- statement:
--   The Idem Lift Alt construction uses the mul mem left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L35-L39

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

theorem Formalism.NG.IdemLiftAlt.mul_mem_left (I : Ideal O) {x : A} (y : A) (hx : x ∈ I • (⊤ : Submodule O A)) :
    x * y ∈ I • (⊤ : Submodule O A) := by sorry
