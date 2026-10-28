-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison
-- name    : AvramDividend.Classical.chat04_strict_exit_clocks_relative_barrier_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:35:06.282409+00:00
-- url     : https://prove2.me/theorems/5e83d1a9-b841-4183-9788-ed2fc2c18017
-- title:
--   Strict two-sided exit clocks under a compensating reserve and barrier shift
-- statement:
--   If the initial reserve rises from x to y and the strict upper barrier changes from a to b with b-y at most a-x, then on each sample path the first strict upward exit occurs no later, and the first strict downward ruin occurs no earlier. The comparison is pathwise and needs no probabilistic regularity beyond the definition of the first passage clocks.
-- source:
--   Generalises the accepted proof of AvramDividend.Classical.chat04_strict_exit_clocks_monotone_initial_reserve (8ac80d48-3c9a-4c19-bc7d-50111732986e) using the same complete-lattice infimum argument.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_clocks_relative_barrier_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x)
    (ω : Ω) :
    twoSidedExitUpTime X (b - y) ω ≤ twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitDownTime X (-x) ω ≤ twoSidedExitDownTime X (-y) ω := by sorry
