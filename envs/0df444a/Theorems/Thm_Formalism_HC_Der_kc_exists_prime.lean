-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_exists_prime
-- name    : Formalism.HC.Der.kc_exists_prime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:26:57.19934+00:00
-- url     : https://prove2.me/theorems/bcf47e5f-06f9-400a-a767-2dc22b59eb22
-- title:
--   Der: kc exists prime
-- statement:
--   The Der construction uses the kc exists prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiff.lean#L41-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcDiff.lean#L41-L65

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

theorem Formalism.HC.Der.kc_exists_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hm : (n : 𝓞 M) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P.LiesOver (span {(p : ℤ)}) := by sorry
