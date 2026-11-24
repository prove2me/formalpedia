-- Prove2me | Theorems.Thm_Formalism_BasicNotions_dvd_condN_iff_primeClass
-- name    : Formalism.BasicNotions.dvd_condN_iff_primeClass
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:27.830954+00:00
-- url     : https://prove2.me/theorems/a34d7808-9ba7-4a25-bacd-74eda1ac485b
-- title:
--   Basic Notions: dvd cond N iff prime Class
-- statement:
--   The Basic Notions construction uses the dvd cond N iff prime Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L71-L80

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

theorem Formalism.BasicNotions.dvd_condN_iff_primeClass (hp : p.Prime) : p ∣ H.condN ↔
    primeClass H p = .ram2 ∨ primeClass H p = .ramQ ∨ primeClass H p = .ramD := by sorry
