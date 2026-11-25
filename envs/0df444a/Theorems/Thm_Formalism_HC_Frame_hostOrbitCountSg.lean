-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostOrbitCountSg
-- name    : Formalism.HC.Frame.hostOrbitCountSg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:44.422615+00:00
-- url     : https://prove2.me/theorems/12068f47-c2d8-446d-ab0f-7ca40926d07b
-- title:
--   Frame: host Orbit Count Sg
-- statement:
--   The Frame construction uses the host Orbit Count Sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L681-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L681-L701

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitCountSg

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

theorem Formalism.HC.Frame.hostOrbitCountSg (g : φ.GG) (h0 : g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    orderOf g = Nat.lcm 2 (orderOf g.2) ∧
    (Set.range fun i : ℕ => placeOf (g ^ i * τ)).ncard = orderOf g := by sorry
