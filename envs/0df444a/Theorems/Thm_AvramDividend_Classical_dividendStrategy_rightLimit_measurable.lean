-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
-- name    : AvramDividend.Classical.dividendStrategy_rightLimit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:39:58.095956+00:00
-- url     : https://prove2.me/theorems/33d03152-4097-405e-91ad-840f7b5be098
-- title:
--   Measurability of the strict-right dividend limit at a fixed time
-- statement:
--   For a dividend strategy, the strict-right limit D_{t+} at any fixed deterministic time t is a measurable random variable. Monotonicity identifies D_{t+} as the right limit of the path, fixed-time adaptedness gives measurable approximating evaluations, and a deterministic sequence of times decreasing to t from above gives the measurable pointwise limit.
-- source:
--   Measure-theoretic helper for Proposition 4(i), needed to show that the random Lebesgue–Stieltjes dividend measure and deterministic-horizon discounted dividend payoff are measurable in the sample point.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightLimit_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) :
    Measurable (fun ω => rightLimit D t ω) := by sorry
