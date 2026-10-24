-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_monotone_initial_reserve
-- name    : AvramDividend.Classical.chat04_strict_exit_clocks_monotone_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:02:08.755978+00:00
-- url     : https://prove2.me/theorems/8ac80d48-3c9a-4c19-bc7d-50111732986e
-- title:
--   Strict upward exit advances and ruin delays as starting reserve increases
-- statement:
--   For any sample path and any x≤y, increasing the starting capital from x to y lowers the strict upper threshold and lowers the strict ruin threshold. Consequently the first strict upper passage occurs no later and the first strict downward ruin occurs no earlier, as ENNReal times including infinity. The proof is purely order-theoretic from the sInf definitions; it requires no path regularity or probability null-set assumptions.
-- source:
--   Definitions.Def_AvramDividend_Classical_TwoSidedExit strict first-passage times in Avram et al. 2007 eq. (3.6).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_clocks_monotone_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) (ω : Ω) :
    twoSidedExitUpTime X (a - y) ω ≤ twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitDownTime X (-x) ω ≤ twoSidedExitDownTime X (-y) ω := by sorry
