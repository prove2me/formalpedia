-- Prove2me | Theorems.Thm_AzumaWeightedSums_Multiplicative_exp_series_summable
-- name    : AzumaWeightedSums.Multiplicative.exp_series_summable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:28:36.190206+00:00
-- url     : https://prove2.me/theorems/ed058bcb-7406-4dd6-a4f9-7e303b05ef7f
-- title:
--   Proof of Theorem 1: almost-sure summability of the exponential series
-- statement:
--   In the setting of Theorem 1, fix $\varepsilon>0$. With $T_n=\sum_{k=1}^{n}a_{nk}x_k$ and $B_n^2=\sum_{k=1}^{n}a_{nk}^2$, the nonnegative exponential series is finite almost surely:
--
--   $$
--   \sum_{n=1}^{\infty}
--   \exp\!\left(
--     \sqrt{\frac{2\log n}{B_n^2}}\,|T_n|-(2+\varepsilon)\log n
--   \right)<\infty\qquad\text{almost surely}.
--   $$
--
--   This is the displayed summability assertion at the start of page 360 and the direct input to the limit bound.
--
--   **Formalization Note** The Lean sequence assigns zero at index $0$, so summability over natural numbers represents the source sum over $n\ge1$. At $B_n=0$ its quotient follows the same harmless convention as the preceding estimate.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 360, §3, proof of Theorem 1, first display, https://doi.org/10.2748/tmj/1178243286

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
import Definitions.Def_AzumaWeightedSums_Multiplicative_WeightedSums

namespace AzumaWeightedSums.Multiplicative

open MeasureTheory

/-- Azuma (1967), p. 360, the almost-sure finite series at the start of the page.
The term at index zero is set to zero because the source series starts at one. -/
theorem exp_series_summable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, Summable (fun n : ℕ =>
      if 1 ≤ n then
        Real.exp
          (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
            |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ))
      else 0) := by sorry

end AzumaWeightedSums.Multiplicative
