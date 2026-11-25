-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostOrdersFrob
-- name    : Formalism.HC.Frame.hostOrdersFrob
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:37.112913+00:00
-- url     : https://prove2.me/theorems/2bd49757-4aa0-4eaf-b12e-993b76ae85c0
-- title:
--   Frame: host Orders Frob
-- statement:
--   The Frame construction uses the host Orders Frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L435-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L435-L447

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

theorem Formalism.HC.Frame.hostOrdersFrob (g : φ.GG) :
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ), ((u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) →
      φ.hH g.2 = hcl φ.e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by sorry
