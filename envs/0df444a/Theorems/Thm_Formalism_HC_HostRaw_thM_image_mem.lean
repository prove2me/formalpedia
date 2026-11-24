-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_thM_image_mem
-- name    : Formalism.HC.HostRaw.thM_image_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:01.637643+00:00
-- url     : https://prove2.me/theorems/1778f0ce-821f-4e66-b10c-bbf06edcdb50
-- title:
--   Host Raw: th M image mem
-- statement:
--   The Host Raw construction uses the th M image mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L104-L107

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

theorem Formalism.HC.HostRaw.thM_image_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) : J (H.thM m) ∈ M := by sorry
