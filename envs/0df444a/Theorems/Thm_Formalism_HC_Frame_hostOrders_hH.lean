-- Prove2me | Theorems.Thm_Formalism_HC_Frame_hostOrders_hH
-- name    : Formalism.HC.Frame.hostOrders_hH
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:30.827475+00:00
-- url     : https://prove2.me/theorems/df837125-0da5-4fb5-97fd-5907dbf9941e
-- title:
--   Frame: host Orders h H
-- statement:
--   The Frame construction uses the host Orders h H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L428-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L428-L433

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

theorem Formalism.HC.Frame.hostOrders_hH (a : φ.MA) (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) (ha : φ.hH a = hcl φ.e u) :
    orderOf (φ.hH a) ≤ 2 ^ j ↔
      ((l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by sorry
