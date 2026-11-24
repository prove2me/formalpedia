-- Prove2me | Theorems.Thm_Formalism_GrowthSums_top_count_holds
-- name    : Formalism.GrowthSums.top_count_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:50.384798+00:00
-- url     : https://prove2.me/theorems/04be2756-fa7e-461b-a7b4-b19e40914366
-- title:
--   Growth Sums: top count holds
-- statement:
--   The Growth Sums construction uses the top count holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/NextEvenTopHolds.lean#L71-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/NextEvenTopHolds.lean#L71-L146

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

theorem Formalism.GrowthSums.top_count_holds : TopCount := by sorry
