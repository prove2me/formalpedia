-- Prove2me | Theorems.Thm_AzumaWeightedSums_Multiplicative_weighted_sum_limsup_le_one
-- name    : AzumaWeightedSums.Multiplicative.weighted_sum_limsup_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:28:44.198759+00:00
-- url     : https://prove2.me/theorems/3f9e334c-9cf2-4117-b837-cd426dfb78ad
-- title:
--   Theorem 1: weighted sums of bounded multiplicative systems
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $(x_k)_{k\ge1}$ satisfy class [M] with $|x_k|\le1$ almost surely, and let $(a_{nk})_{1\le k\le n}$ be any real triangular array. With $T_n=\sum_{k=1}^{n}a_{nk}x_k$ and $B_n=(\sum_{k=1}^{n}a_{nk}^2)^{1/2}$, Azuma's Theorem 1 asserts
--
--   $$
--   \limsup_{n\to\infty}\frac{|T_n|}{\sqrt{2B_n^2\log n}}\le1
--   \qquad\text{almost surely}.
--   $$
--
--   The bound is uniform over arbitrary choices of the real weights; it requires neither independence of the variables nor a growth condition on $B_n$.
--
--   **Formalization Note** The Lean statement gives the limsup inequality as: for every $\varepsilon>0$, almost surely, eventually $|T_n|\le(1+\varepsilon)\sqrt{2B_n^2\log n}$. This formulation also handles rows with $B_n=0$, when $T_n=0$ almost surely.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 359, Theorem 1, (3.1), https://doi.org/10.2748/tmj/1178243286

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
import Definitions.Def_AzumaWeightedSums_Multiplicative_WeightedSums

namespace AzumaWeightedSums.Multiplicative

open MeasureTheory Filter

/-- Azuma (1967), p. 359, Theorem 1, (3.1). The limsup inequality is rendered
as an eventual bound for every positive excess, avoiding a real-valued limsup
outside its boundedness domain. -/
theorem weighted_sum_limsup_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (a : ℕ → ℕ → ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
        |weightedSum a x n ω| ≤
          (1 + ε) * Real.sqrt (2 * (weightNorm a n) ^ 2 * Real.log (n : ℝ)) := by sorry

end AzumaWeightedSums.Multiplicative
