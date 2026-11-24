-- Prove2me | Theorems.Thm_Formalism_HC_Der_val_modEq_iff
-- name    : Formalism.HC.Der.val_modEq_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:27.545698+00:00
-- url     : https://prove2.me/theorems/ce19543d-82ed-4129-9e78-79dd7f1ef7fd
-- title:
--   Der: val mod Eq iff
-- statement:
--   The Der construction uses the val mod Eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L44-L47

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
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

theorem Formalism.HC.Der.val_modEq_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) (x : ℕ) :
    (u : ZMod N).val ≡ x [MOD M] ↔ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (x : ZMod M) := by sorry
