-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_integ_iff
-- name    : Formalism.HC.Der.kc_integ_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:10.96186+00:00
-- url     : https://prove2.me/theorems/673be6d8-41b7-4cde-843c-c273791ed350
-- title:
--   Der: kc integ iff
-- statement:
--   The Der construction uses the kc integ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L143-L145

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem Formalism.HC.Der.kc_integ_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t := by sorry
