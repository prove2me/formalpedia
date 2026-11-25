-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_CoprimeFifteen_five_not_dvd_condN
-- name    : Formalism.HC.HostRaw.CoprimeFifteen.five_not_dvd_condN
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:28.390062+00:00
-- url     : https://prove2.me/theorems/20b31973-2c23-484c-a72e-2e282cbbc155
-- title:
--   Coprime Fifteen: five not dvd cond N
-- statement:
--   The Coprime Fifteen construction uses the five not dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L163-L165

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

theorem Formalism.HC.HostRaw.CoprimeFifteen.five_not_dvd_condN (h : H.CoprimeFifteen) : ¬ 5 ∣ H.condN := by sorry
