-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_ne_bot
-- name    : Formalism.HC.Der.kc_ne_bot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:25.966947+00:00
-- url     : https://prove2.me/theorems/9828a88a-92ab-4b9c-b05a-c8241431cb7e
-- title:
--   Der: kc ne bot
-- statement:
--   The Der construction uses the kc ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcBase.lean#L78-L81

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
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

theorem Formalism.HC.Der.kc_ne_bot {M : Type} [Field M] [NumberField M] (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 M))
    [P.LiesOver (span {(p : ℤ)})] : P ≠ ⊥ := by sorry
