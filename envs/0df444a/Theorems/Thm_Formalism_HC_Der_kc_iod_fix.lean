-- Prove2me | Theorems.Thm_Formalism_HC_Der_kc_iod_fix
-- name    : Formalism.HC.Der.kc_iod_fix
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:05:26.408875+00:00
-- url     : https://prove2.me/theorems/3aafa3e3-bb61-429a-aea8-4e2f511b20c9
-- title:
--   Der: kc iod fix
-- statement:
--   The Der construction uses the kc iod fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcEqOfPowEqOne.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcEqOfPowEqOne.lean#L45-L69

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
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

theorem Formalism.HC.Der.kc_iod_fix (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ = φ.iod) (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by sorry
