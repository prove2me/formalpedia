-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_mem_inv_smul
-- name    : Formalism.HC.Der.kc_mem_inv_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:22.630948+00:00
-- url     : https://prove2.me/theorems/8fad3af7-0c8a-4326-b20d-88d488feb488
-- title:
--   Der: kc mem inv smul
-- statement:
--   The Der construction uses the kc mem inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L155-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L155-L186

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

theorem Formalism.HC.Der.kc_mem_inv_smul (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) (y : H.E) :
    σ y ∈ ((σ • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by sorry
