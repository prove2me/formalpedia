-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_ofRaw_toHostRaw
-- name    : Formalism.HC.HostAx.ofRaw_toHostRaw
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:02.859132+00:00
-- url     : https://prove2.me/theorems/8ed56784-4522-5c5d-8d19-3cf361bca72f
-- title:
--   Host Ax: of Raw to Host Raw
-- statement:
--   The Host Ax construction uses the of Raw to Host Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean#L44-L44

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_Imports
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfRawToHostRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC

theorem Formalism.HC.HostAx.ofRaw_toHostRaw {φ : Frame} (H : HostRaw φ) : (HostAx.ofRaw H).toHostRaw = H := by sorry

attribute [defeq] Formalism.HC.HostAx.ofRaw_toHostRaw
