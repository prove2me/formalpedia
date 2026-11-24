-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostCharSum
-- name    : Formalism.HC.Frame.hostCharSum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:53:32.038078+00:00
-- url     : https://prove2.me/theorems/7aecfc1e-9563-4bbc-9e9d-fdabb4ec0984
-- title:
--   Frame: host Char Sum
-- statement:
--   The Frame construction uses the host Char Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L508-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L508-L582

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostCharSum

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
open Classical

theorem Formalism.HC.Frame.hostCharSum :
    (∀ χ : φ.GG →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 * φ.ord : ℂ) else if χ = φ.chC then -(2 * φ.ord : ℂ) else 0) ∧
    ∀ g : φ.GG,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((φ.chD g : ℤˣ) : ℤ)) * (1 + ((φ.chQ g : ℤˣ) : ℤ)) := by sorry
