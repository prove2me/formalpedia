-- Prove2me | Theorems.Thm_Formalism_GrowthSums_four_padicValNat_le
-- name    : Formalism.GrowthSums.four_padicValNat_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:07.982799+00:00
-- url     : https://prove2.me/theorems/54c45f88-dae4-4979-b51a-03d8ca4d9aa4
-- title:
--   Growth Sums: four padic Val Nat le
-- statement:
--   The Growth Sums construction uses the four padic Val Nat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/LogCoef.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/LogCoef.lean#L19-L24

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

theorem Formalism.GrowthSums.four_padicValNat_le (p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    4 * padicValNat p s + 2 ≤ 3 * s := by sorry
