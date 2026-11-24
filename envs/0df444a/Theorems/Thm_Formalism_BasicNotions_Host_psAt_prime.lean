-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_psAt_prime
-- name    : Formalism.BasicNotions.Host.psAt_prime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:49.094674+00:00
-- url     : https://prove2.me/theorems/401e11f5-c127-4cbe-b99d-8824347fc676
-- title:
--   Host: ps At prime
-- statement:
--   The Host construction uses the ps At prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L179-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L179-L207

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_HC_HostRaw_PsQ_psAt_prime

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
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H

theorem Formalism.BasicNotions.Host.psAt_prime {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) : H.psAt p = jacobiSym (-(H.q : ℤ)) p := by sorry
