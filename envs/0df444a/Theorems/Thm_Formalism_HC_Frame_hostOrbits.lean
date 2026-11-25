-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostOrbits
-- name    : Formalism.HC.Frame.hostOrbits
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:53:14.478823+00:00
-- url     : https://prove2.me/theorems/eab72194-a4a0-45d4-8676-6283d2ba2db2
-- title:
--   Frame: host Orbits
-- statement:
--   The Frame construction uses the host Orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L611-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L611-L617

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbits

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

theorem Formalism.HC.Frame.hostOrbits (h2 : φ.TwoGroup) (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    (∀ τ ∈ φ.Psi, ∀ i : ℕ, g ^ i * τ ∈ φ.Psi ↔ Even i) ∧
    (g.1 = c0 → g.2 ≠ 1 → Even (orderOf g.2) ∧ orderOf g = orderOf g.2) := by sorry
