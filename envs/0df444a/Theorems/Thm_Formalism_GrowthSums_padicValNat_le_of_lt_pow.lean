-- Prove2me | Theorems.Thm_Formalism_GrowthSums_padicValNat_le_of_lt_pow
-- name    : Formalism.GrowthSums.padicValNat_le_of_lt_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:25.534802+00:00
-- url     : https://prove2.me/theorems/cf3417f6-58d5-4b98-91d8-3155c4586160
-- title:
--   Growth Sums: padic Val Nat le of lt pow
-- statement:
--   The Growth Sums construction uses the padic Val Nat le of lt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Harmonic.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Harmonic.lean#L29-L35

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic
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

theorem Formalism.GrowthSums.padicValNat_le_of_lt_pow {p t y : ℕ} [hp : Fact p.Prime] (hy : 1 ≤ y)
    (hyP : y < p ^ (t + 1)) : padicValNat p y ≤ t := by sorry
