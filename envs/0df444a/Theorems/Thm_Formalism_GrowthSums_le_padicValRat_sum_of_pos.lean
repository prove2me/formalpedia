-- Prove2me | Theorems.Thm_Formalism_GrowthSums_le_padicValRat_sum_of_pos
-- name    : Formalism.GrowthSums.le_padicValRat_sum_of_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:30.326688+00:00
-- url     : https://prove2.me/theorems/35701e44-c730-4332-96b3-179161d585b1
-- title:
--   Growth Sums: le padic Val Rat sum of pos
-- statement:
--   The Growth Sums construction uses the le padic Val Rat sum of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Harmonic.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/Harmonic.lean#L8-L27

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

theorem Formalism.GrowthSums.le_padicValRat_sum_of_pos {p : ℕ} [Fact p.Prime] (s : ℤ) {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hpos : ∀ i ∈ S, 0 < F i) (hv : ∀ i ∈ S, s ≤ padicValRat p (F i)) :
    s ≤ padicValRat p (∑ i ∈ S, F i) := by sorry
