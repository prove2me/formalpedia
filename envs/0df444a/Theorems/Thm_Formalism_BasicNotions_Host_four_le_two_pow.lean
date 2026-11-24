-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Host_four_le_two_pow
-- name    : Formalism.BasicNotions.Host.four_le_two_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:35.942238+00:00
-- url     : https://prove2.me/theorems/91689955-a6fd-4dc8-b6d8-edbbb33cfb52
-- title:
--   Host: four le two pow
-- statement:
--   The Host construction uses the four le two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L170-L173

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
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H

theorem Formalism.BasicNotions.Host.four_le_two_pow : 4 ≤ 2 ^ R.e := by sorry
