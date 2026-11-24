-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_mem_diff_iff
-- name    : Formalism.HC.Der.kc_mem_diff_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:11:04.616319+00:00
-- url     : https://prove2.me/theorems/17869971-56c9-481a-92d1-396016d16ed3
-- title:
--   Der: kc mem diff iff
-- statement:
--   The Der construction uses the kc mem diff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L72-L88

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

theorem Formalism.HC.Der.kc_mem_diff_iff (z : 𝓞 H.E) :
    z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      ∀ y : H.E, (∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) →
        IsIntegral ℤ ((z : H.E) * y) := by sorry
