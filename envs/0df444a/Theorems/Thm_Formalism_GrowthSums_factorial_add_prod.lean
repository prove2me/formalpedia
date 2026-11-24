-- Prove2me | Theorems.Thm_Formalism_GrowthSums_factorial_add_prod
-- name    : Formalism.GrowthSums.factorial_add_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:13.769019+00:00
-- url     : https://prove2.me/theorems/ccb8a895-96c2-4df3-b83c-ccdca617eadb
-- title:
--   Growth Sums: factorial add prod
-- statement:
--   The Growth Sums construction uses the factorial add prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Coarse.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Coarse.lean#L8-L21

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Coarse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums

theorem Formalism.GrowthSums.factorial_add_prod (m k : ℕ) :
    (((m + k).factorial : ℕ) : ℚ) =
      (m.factorial : ℚ) * (k.factorial : ℚ) * ∏ y ∈ Ico 1 (k + 1), (1 + (m : ℚ) / y) := by sorry
