-- Prove2me | Theorems.Thm_Formalism_BasicNotions_primeClass_q
-- name    : Formalism.BasicNotions.primeClass_q
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:55.77832+00:00
-- url     : https://prove2.me/theorems/eed27a7e-0d74-4f46-80ed-bfbbf56204a7
-- title:
--   Basic Notions: prime Class q
-- statement:
--   The Basic Notions construction uses the prime Class q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L68-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L68-L68

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

theorem Formalism.BasicNotions.primeClass_q : primeClass H H.q = .ramQ := by sorry
