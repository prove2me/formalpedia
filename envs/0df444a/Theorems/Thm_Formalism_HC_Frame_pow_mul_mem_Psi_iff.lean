-- Prove2me | Theorems.Thm_Formalism_HC_Frame_pow_mul_mem_Psi_iff
-- name    : Formalism.HC.Frame.pow_mul_mem_Psi_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:23.484086+00:00
-- url     : https://prove2.me/theorems/08a9b4bd-4338-4eab-957e-8fbda625980c
-- title:
--   Frame: pow mul mem Psi iff
-- statement:
--   The Frame construction uses the pow mul mem Psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L584-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L584-L591

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)

theorem Formalism.HC.Frame.pow_mul_mem_Psi_iff {g : φ.GG} (hg : g ∉ φ.Psi) {τ : φ.GG} (hτ : τ ∈ φ.Psi) (i : ℕ) :
    g ^ i * τ ∈ φ.Psi ↔ Even i := by sorry
