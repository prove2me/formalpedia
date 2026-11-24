-- Prove2me | Theorems.Thm_Formalism_GrowthSums_four_mul_add_two_le_three_mul_five_pow
-- name    : Formalism.GrowthSums.four_mul_add_two_le_three_mul_five_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:04.985858+00:00
-- url     : https://prove2.me/theorems/87eee3e7-0c71-4e7b-bffd-5af1a755529d
-- title:
--   Growth Sums: four mul add two le three mul five pow
-- statement:
--   The Growth Sums construction uses the four mul add two le three mul five pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/LogCoef.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/LogCoef.lean#L11-L17

import Definitions.Def_Formalism_GrowthSums_StatementC
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_LogCoef
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

theorem Formalism.GrowthSums.four_mul_add_two_le_three_mul_five_pow (v : ℕ) : 4 * v + 2 ≤ 3 * 5 ^ v := by sorry
