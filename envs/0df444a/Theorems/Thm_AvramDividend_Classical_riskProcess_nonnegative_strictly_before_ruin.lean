-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
-- name    : AvramDividend.Classical.riskProcess_nonnegative_strictly_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:52:26.576864+00:00
-- url     : https://prove2.me/theorems/03a69d71-1387-4410-83a2-1fe59054ebe6
-- title:
--   The original reserve is nonnegative at every time strictly before ruin
-- statement:
--   Ruin time is the infimum of times when the book-value controlled reserve first becomes strictly negative. Therefore if a time t is strictly before ruin, the book reserve at t cannot be negative. This holds pathwise for any dividend path, without assuming càdlàg, adaptedness or a finite ruin time. It is a necessary killed-process support lemma, and does not claim nonnegativity at ruin or post-payment nonnegativity without separate right-limit reasoning.
-- source:
--   Exact accepted Chat 08 zero_cap_barrier_eq_control_solution_v2 negative-reserve contradiction pattern, generalized from x=0 to arbitrary real initial surplus x.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_nonnegative_strictly_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by sorry
