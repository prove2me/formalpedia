-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_ordCompl_q
-- name    : Formalism.HC.HostRaw.ordCompl_q
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:43.407004+00:00
-- url     : https://prove2.me/theorems/c9e59fa8-6e1d-5a15-ae2c-b4c90d03ffd7
-- title:
--   Host Raw: ord Compl q
-- statement:
--   The Host Raw construction uses the ord Compl q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L69-L74

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by sorry
