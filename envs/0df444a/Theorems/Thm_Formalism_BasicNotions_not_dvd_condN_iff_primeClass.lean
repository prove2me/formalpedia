-- Prove2me | Theorems.Thm_Formalism_BasicNotions_not_dvd_condN_iff_primeClass
-- name    : Formalism.BasicNotions.not_dvd_condN_iff_primeClass
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:36.309795+00:00
-- url     : https://prove2.me/theorems/57aef1ba-1cb2-4372-a9ec-ca18c60e4e83
-- title:
--   Basic Notions: not dvd cond N iff prime Class
-- statement:
--   The Basic Notions construction uses the not dvd cond N iff prime Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L82-L86

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

theorem Formalism.BasicNotions.not_dvd_condN_iff_primeClass (hp : p.Prime) : ¬ p ∣ H.condN ↔
    primeClass H p = .splitK ∨ primeClass H p = .signal ∨ primeClass H p = .inertClass := by sorry
