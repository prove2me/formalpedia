-- Prove2me | Theorems.Thm_AzumaWeightedSums_Multiplicative_exp_bound
-- name    : AzumaWeightedSums.Multiplicative.exp_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:28:34.955143+00:00
-- url     : https://prove2.me/theorems/fda4df93-4510-462a-a655-2ebbe4cab2e2
-- title:
--   Proof of Theorem 1: exponential moment bound with factor 2
-- statement:
--   Let $(x_k)$ satisfy class [M] with unit bounds, let $(a_{nk})$ be an arbitrary real triangular array, and put $T_n=\sum_{k=1}^{n}a_{nk}x_k$ and $B_n^2=\sum_{k=1}^{n}a_{nk}^2$. For every $n\ge1$ and $\varepsilon>0$,
--
--   $$
--   E\exp\!\left(
--     \sqrt{\frac{2\log n}{B_n^2}}\,|T_n|-(2+\varepsilon)\log n
--   \right)
--   \le 2\left(\frac1n\right)^{1+\varepsilon}.
--   $$
--
--   The factor $2$ accounts for the two signs of $T_n$. This displayed estimate in the proof of Theorem 1 precedes the almost-sure summability statement.
--
--   **Formalization Note** When $B_n=0$, Lean takes the quotient in the square root to be zero; all weights in row $n$ vanish, and the resulting inequality remains true. No positive-norm assumption is imposed.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 359, §3, proof of Theorem 1, first display after (3.1), https://doi.org/10.2748/tmj/1178243286

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
import Definitions.Def_AzumaWeightedSums_Multiplicative_WeightedSums

namespace AzumaWeightedSums.Multiplicative

open MeasureTheory

/-- Azuma (1967), p. 359, first display in the proof of Theorem 1. -/
theorem exp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∫ ω, Real.exp
      (Real.sqrt ((2 * Real.log (n : ℝ)) / (weightNorm a n) ^ 2) *
        |weightedSum a x n ω| - (2 + ε) * Real.log (n : ℝ)) ∂μ ≤
      2 * ((1 / (n : ℝ)) ^ (1 + ε)) := by sorry

end AzumaWeightedSums.Multiplicative
