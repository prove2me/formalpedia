-- Prove2me | Theorems.Thm_Formalism_GrowthSums_next_even_top_holds
-- name    : Formalism.GrowthSums.next_even_top_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:33.003068+00:00
-- url     : https://prove2.me/theorems/7b63d8aa-11f6-4c62-841e-4672b49bec8d
-- title:
--   Growth Sums: next even top holds
-- statement:
--   The Growth Sums construction uses the next even top holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/NextEvenTopHolds.lean#L12-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/NextEvenTopHolds.lean#L12-L69

import Definitions.Def_Formalism_GrowthSums_StatementB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_NextEvenTopHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
open Formalism.G0

theorem Formalism.GrowthSums.next_even_top_holds : NextEvenTop := by sorry
