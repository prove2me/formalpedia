-- Prove2me | Theorems.Thm_Formalism_HC_Der_val_one_modEq
-- name    : Formalism.HC.Der.val_one_modEq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:46:09.491334+00:00
-- url     : https://prove2.me/theorems/6a7e61ae-cb78-4970-b19d-60e9690a7c7e
-- title:
--   Der: val one mod Eq
-- statement:
--   The Der construction uses the val one mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L233-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L233-L235

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.val_one_modEq (M N : ℕ) [NeZero N] (h : M ∣ N) : (((1 : (ZMod N)ˣ) : ZMod N)).val ≡ 1 [MOD M] := by sorry
