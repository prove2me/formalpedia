-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_diff_smul_le
-- name    : Formalism.HC.Der.kc_diff_smul_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:36.114948+00:00
-- url     : https://prove2.me/theorems/ebf55b76-45ec-4b6d-ac91-49287ec3e195
-- title:
--   Der: kc diff smul le
-- statement:
--   The Der construction uses the kc diff smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiffSmulMem.lean#L119-L125

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

theorem Formalism.HC.Der.kc_diff_smul_le (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ differentIdeal (𝓞 H.K) (𝓞 H.E) := by sorry
