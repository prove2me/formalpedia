-- Prove2me | Theorems.Thm_Formalism_HC_Der_exists_frob
-- name    : Formalism.HC.Der.exists_frob
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:35.227043+00:00
-- url     : https://prove2.me/theorems/d4ecd435-b400-46c6-a490-29d02357032b
-- title:
--   Der: exists frob
-- statement:
--   The Der construction uses the exists frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L253-L259

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
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

theorem Formalism.HC.Der.exists_frob (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (F : H.E ≃ₐ[ℚ] H.E) (w : (ZMod H.condN)ˣ), IsArithFrobAt ℤ F P ∧
      (w : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal F = H.art w := by sorry
