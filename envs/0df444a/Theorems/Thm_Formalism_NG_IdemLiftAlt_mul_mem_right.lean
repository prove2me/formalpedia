-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_right
-- name    : Formalism.NG.IdemLiftAlt.mul_mem_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:12.762865+00:00
-- url     : https://prove2.me/theorems/928b5274-c926-497e-9d5f-2104d7bb6b4c
-- title:
--   Idem Lift Alt: mul mem right
-- statement:
--   The Idem Lift Alt construction uses the mul mem right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L41-L45

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

theorem Formalism.NG.IdemLiftAlt.mul_mem_right (I : Ideal O) (y : A) {x : A} (hx : x ∈ I • (⊤ : Submodule O A)) :
    y * x ∈ I • (⊤ : Submodule O A) := by sorry
