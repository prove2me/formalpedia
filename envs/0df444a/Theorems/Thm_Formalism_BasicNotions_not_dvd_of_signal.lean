-- Prove2me | Theorems.Thm_Formalism_BasicNotions_not_dvd_of_signal
-- name    : Formalism.BasicNotions.not_dvd_of_signal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:13.178198+00:00
-- url     : https://prove2.me/theorems/44f94baa-4e9f-4c80-9a11-66cf8c93898f
-- title:
--   Basic Notions: not dvd of signal
-- statement:
--   The Basic Notions construction uses the not dvd of signal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L92-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L92-L92

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}

theorem Formalism.BasicNotions.not_dvd_of_signal (hp : p.Prime) (h : primeClass H p = .signal) : ¬ p ∣ H.condN := by sorry
