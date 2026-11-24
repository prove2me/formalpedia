-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_PsQ_psAt_prime
-- name    : Formalism.HC.HostRaw.PsQ.psAt_prime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:15.81299+00:00
-- url     : https://prove2.me/theorems/f26969ed-e3c1-4665-90be-035175d42c92
-- title:
--   Ps Q: ps At prime
-- statement:
--   The Ps Q construction uses the ps At prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L202-L204

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
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
variable {H}

theorem Formalism.HC.HostRaw.PsQ.psAt_prime (hP : H.PsQ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) :
    H.psAt p = jacobiSym (-(H.q : ℤ)) p := by sorry
