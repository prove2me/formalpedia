-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative
-- name    : AvramDividend.Classical.barrierStrategy_plus_linear_drain_reserve_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:21:51.32679+00:00
-- url     : https://prove2.me/theorems/50cad288-014a-4651-9e48-c4391df764dc
-- title:
--   Zero-barrier dividends with a further linear drain make reserves negative at every positive time
-- statement:
--   Starting from an arbitrary nonnegative surplus, run the zero-barrier dividend strategy and add a deterministic linear dividend drain t. The zero-barrier controlled surplus is at most zero at every strictly positive time. Subtracting the additional payment t makes the new reserve strictly negative at every positive time and every sample path. This provides a pathwise immediate-ruin witness for auditing the time-zero dividend boundary in the stochastic verification theorem, without assuming regularity of zero for Brownian motion.
-- source:
--   Direct consequence of the established zero-barrier reserve cap in Avram, Palmowski and Pistorius (2007), equations (2.1) and the barrier strategy definition, used in the Proposition 4(i) initial-boundary audit.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_plus_linear_drain_reserve_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x) :
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      riskProcess X x
        (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω < 0 := by sorry
