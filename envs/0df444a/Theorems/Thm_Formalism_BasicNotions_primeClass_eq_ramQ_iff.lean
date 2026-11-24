-- Prove2me | Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramQ_iff
-- name    : Formalism.BasicNotions.primeClass_eq_ramQ_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:39.467171+00:00
-- url     : https://prove2.me/theorems/3bfbe858-a556-4a57-9f6e-6f948a5ebe48
-- title:
--   Basic Notions: prime Class eq ram Q iff
-- statement:
--   The Basic Notions construction uses the prime Class eq ram Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L32-L35

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

theorem Formalism.BasicNotions.primeClass_eq_ramQ_iff : primeClass H p = .ramQ ↔ p = H.q := by sorry
