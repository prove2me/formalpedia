-- Prove2me | Theorems.Thm_Formalism_HC_Der_inertia_d
-- name    : Formalism.HC.Der.inertia_d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:07:06.516331+00:00
-- url     : https://prove2.me/theorems/7da34ae7-d47f-48d7-9327-6fe985843306
-- title:
--   Der: inertia d
-- statement:
--   The Der construction uses the inertia d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L399-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L399-L426

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_D7_inertia_d

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

theorem Formalism.HC.Der.inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod) := by sorry
