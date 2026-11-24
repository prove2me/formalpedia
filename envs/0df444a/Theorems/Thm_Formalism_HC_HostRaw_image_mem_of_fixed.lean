-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_image_mem_of_fixed
-- name    : Formalism.HC.HostRaw.image_mem_of_fixed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:00:09.618843+00:00
-- url     : https://prove2.me/theorems/b7e05087-3a6d-4993-b7e3-071161d7195b
-- title:
--   Host Raw: image mem of fixed
-- statement:
--   The Host Raw construction uses the image mem of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L33-L53

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.image_mem_of_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    J x ∈ M := by sorry
