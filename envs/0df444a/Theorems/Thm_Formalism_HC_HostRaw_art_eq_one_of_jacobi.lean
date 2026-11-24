-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_art_eq_one_of_jacobi
-- name    : Formalism.HC.HostRaw.art_eq_one_of_jacobi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:20.043139+00:00
-- url     : https://prove2.me/theorems/36ec127a-f48e-4987-9311-45086b42a1c4
-- title:
--   Host Raw: art eq one of jacobi
-- statement:
--   The Host Raw construction uses the art eq one of jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L113-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L113-L139

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

theorem Formalism.HC.HostRaw.art_eq_one_of_jacobi (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d])
    (hj : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q = 1) : H.art u = 1 := by sorry
