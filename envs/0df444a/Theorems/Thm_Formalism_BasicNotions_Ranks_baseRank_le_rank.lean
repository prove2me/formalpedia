-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Ranks_baseRank_le_rank
-- name    : Formalism.BasicNotions.Ranks.baseRank_le_rank
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:12.462715+00:00
-- url     : https://prove2.me/theorems/1d3cf874-6f33-4c17-9d31-29048ade02aa
-- title:
--   Ranks: base Rank le rank
-- statement:
--   The Ranks construction uses the base Rank le rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L161-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/HostCls.lean#L161-L161

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

theorem Formalism.BasicNotions.Ranks.baseRank_le_rank : R.n0 ≤ R.n := by sorry
