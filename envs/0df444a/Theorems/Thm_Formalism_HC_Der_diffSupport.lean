-- Prove2me | Theorems.Thm_Formalism_HC_Der_diffSupport
-- name    : Formalism.HC.Der.diffSupport
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:26:33.390939+00:00
-- url     : https://prove2.me/theorems/10244b66-2126-444b-9825-8565e7154376
-- title:
--   Der: diff Support
-- statement:
--   The Der construction uses the diff Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiff.lean#L75-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiff.lean#L75-L105

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
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
variable (C : HostCore H)
include C

theorem Formalism.HC.Der.diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P := by sorry
