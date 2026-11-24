-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostOrbitsPlaces
-- name    : Formalism.HC.Frame.hostOrbitsPlaces
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:54:33.6288+00:00
-- url     : https://prove2.me/theorems/6220cba2-0f56-4ef2-8d30-f9ee2d26820f
-- title:
--   Frame: host Orbits Places
-- statement:
--   The Frame construction uses the host Orbits Places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L619-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L619-L641

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitsPlaces

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

theorem Formalism.HC.Frame.hostOrbitsPlaces (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi)
    (i : ℕ) :
    (placeOf (g ^ i * τ)).2 = g.2 ^ i * τ.2 ∧
    (g.1 = c0 → (placeOf (g ^ i * τ)).1 = τ.1) ∧
    (g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (g ^ i * τ)).1 = (if Even i then 1 else φ.sg.1) * τ.1) := by sorry
