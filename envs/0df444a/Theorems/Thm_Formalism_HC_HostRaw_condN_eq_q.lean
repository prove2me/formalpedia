-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_condN_eq_q
-- name    : Formalism.HC.HostRaw.condN_eq_q
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:15.864876+00:00
-- url     : https://prove2.me/theorems/47deeca2-c8a9-4075-9010-20673b0dacf4
-- title:
--   Host Raw: cond N eq q
-- statement:
--   The Host Raw construction uses the cond N eq q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostRam.lean#L57-L59

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

theorem Formalism.HC.HostRaw.condN_eq_q : H.condN = H.QS * H.d * H.q := by sorry
