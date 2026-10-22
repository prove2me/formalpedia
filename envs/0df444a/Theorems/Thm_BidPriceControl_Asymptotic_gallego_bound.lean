-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_gallego_bound
-- name    : BidPriceControl.Asymptotic.gallego_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:38:17.152992+00:00
-- url     : https://prove2.me/theorems/81b32bad-353b-44d3-a578-0dd7e7ca306c
-- title:
--   Gallego (1992) bound: E(Z − z)⁺ ≤ (√(σ² + (z − m)²) − (z − m))/2
-- statement:
--   Let $Z$ be a real random variable on a probability space with finite second moment, mean $m = \mathbb{E}Z$ and variance $\sigma^2 = \operatorname{Var} Z$. Then for every real $z$,
--   $$\mathbb{E}(Z - z)^+ \le \frac{\sqrt{\sigma^2 + (z - m)^2} - (z - m)}{2}.$$
--   The proof of Theorem 1 applies this bound to the number of seats an uncapacitated system sells on one leg, with $z$ the leg's scaled capacity, to control the expected overflow.
--
--   **Formalization Note.** "Finite variance" is `MemLp Z 2 P`. The paper writes the mean as $\mu$; here it is $m$, so that it is not confused with the bid prices.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1585, proof of Theorem 1 (bound due to Gallego (1992))

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Gallego's (1992) bound, as used in the proof of Theorem 1 (Talluri–van Ryzin 1998, p. 1585):
for a real random variable `Z` with mean `m = E Z` and finite variance `σ² = Var Z`, and any real
`z`, `E(Z − z)^+ ≤ (√(σ² + (z − m)²) − (z − m)) / 2`. -/
theorem gallego_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P) (z : ℝ) :
    ∫ ω, max (Z ω - z) 0 ∂P ≤
      (Real.sqrt (variance Z P + (z - ∫ ω, Z ω ∂P) ^ 2) - (z - ∫ ω, Z ω ∂P)) / 2 := by sorry

end BidPriceControl.Asymptotic
