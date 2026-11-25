-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_ramificationIdx_eq_one_iff
-- name    : Formalism.HC.HostAx.ramificationIdx_eq_one_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:59.386821+00:00
-- url     : https://prove2.me/theorems/d09541f3-625c-5e94-9096-a37b9672ea3f
-- title:
--   Host Ax: ramification Idx eq one iff
-- statement:
--   The Host Ax construction uses the ramification Idx eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L176-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L176-L185

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.ramificationIdx_eq_one_iff (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.ramificationIdx ℤ = 1 ↔ ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) → σ = 1 := by sorry
