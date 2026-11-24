-- Prove2me | Theorems.Thm_Formalism_HC_Der_decompConj
-- name    : Formalism.HC.Der.decompConj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:45:49.614035+00:00
-- url     : https://prove2.me/theorems/2a169633-00aa-4ef3-b383-27447472cbf6
-- title:
--   Der: decomp Conj
-- statement:
--   The Der construction uses the decomp Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L528-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L528-L602

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

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

theorem Formalism.HC.Der.decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P := by sorry
