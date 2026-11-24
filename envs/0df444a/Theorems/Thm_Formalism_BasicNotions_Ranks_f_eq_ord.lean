-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Ranks_f_eq_ord
-- name    : Formalism.BasicNotions.Ranks.f_eq_ord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:30:50.863734+00:00
-- url     : https://prove2.me/theorems/7006bbc9-6a1c-4812-a0ab-19adaa274aa0
-- title:
--   Ranks: f eq ord
-- statement:
--   The Ranks construction uses the f eq ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L154-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L154-L154

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
open Formalism.BasicNotions.Ranks
variable (R : Ranks)

theorem Formalism.BasicNotions.Ranks.f_eq_ord : R.f = 2 * R.ord := by sorry
