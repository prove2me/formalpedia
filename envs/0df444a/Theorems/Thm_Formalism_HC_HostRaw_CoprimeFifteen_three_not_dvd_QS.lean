-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_CoprimeFifteen_three_not_dvd_QS
-- name    : Formalism.HC.HostRaw.CoprimeFifteen.three_not_dvd_QS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:55:00.12822+00:00
-- url     : https://prove2.me/theorems/94c280fb-4b2d-442f-8d2f-3956e08c0563
-- title:
--   Coprime Fifteen: three not dvd QS
-- statement:
--   The Coprime Fifteen construction uses the three not dvd QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L153-L155

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

theorem Formalism.HC.HostRaw.CoprimeFifteen.three_not_dvd_QS (h : H.CoprimeFifteen) : ¬ 3 ∣ H.QS := by sorry
