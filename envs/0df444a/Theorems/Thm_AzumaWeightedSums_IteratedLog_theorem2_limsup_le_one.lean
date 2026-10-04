-- Prove2me | Theorems.Thm_AzumaWeightedSums_IteratedLog_theorem2_limsup_le_one
-- name    : AzumaWeightedSums.IteratedLog.theorem2_limsup_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:31:34.044692+00:00
-- url     : https://prove2.me/theorems/3c81eca2-6493-48b9-bc21-e055163fd287
-- title:
--   Theorem 2 — $\limsup |S_n|/\sqrt{2D_n^2\log\log D_n^2}\le 1$ a.s. for class [G]
-- statement:
--   Let $(x_n)_{n\ge1}$ be a sequence of random variables for which [G] holds with $\tau(x_n)\le1$ for all $n$: martingale differences with respect to a filtration $(\mathfrak A_n)$ with $E\{\exp(tx_n)\mid\mathfrak A_{n-1}\}\le\exp(t^2/2)$ a.s. for every real $t$. Let $(a_n)$ be a real sequence, and put $D_n^2=\sum_{j=1}^n a_j^2$ and $S_n=a_1x_1+\dots+a_nx_n$. If
--   $$
--   a_n^2/D_n^2\to0,\qquad D_n^2\to\infty\qquad(n\to\infty),
--   $$
--   then
--   $$
--   \limsup_{n\to\infty}\frac{|S_n|}{\sqrt{2D_n^2\log\log D_n^2}}\le1\quad\text{a.s.}
--   $$
--
--   This is the upper half of the law of the iterated logarithm for weighted sums of conditionally sub-Gaussian martingale differences, including bounded martingale differences with $|x_n|\le1$. The constant $1$ matches the classical Hartman–Wintner law for independent standard Gaussian increments, so it cannot be improved in general.
--
--   **Formalization Note** The lim sup is stated in its equivalent eventual form, avoiding Lean's real-valued `limsup` (which is $0$ on unbounded sequences): for every $\varepsilon>0$, almost surely, $|S_n|\le(1+\varepsilon)\sqrt{2D_n^2\log\log D_n^2}$ for all sufficiently large $n$. Since $D_n^2\to\infty$, $\log\log D_n^2>0$ for all large $n$, so only meaningful values of the iterated logarithm enter. Both parts of (4.1) are hypotheses. Indices start at $1$; the filtration's initial $\sigma$-field is arbitrary.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, p. 362, Theorem 2, displays (4.1)–(4.2)

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

open MeasureTheory ProbabilityTheory Filter Topology

namespace AzumaWeightedSums.IteratedLog

/-- Azuma 1967, Theorem 2, display (4.2), p. 362: if `(x_n)` satisfies [G] with
`τ(x_n) ≤ 1` for all `n`, and the real weights `(a_n)` satisfy (4.1),
`a_n²/D_n² → 0` and `D_n² → ∞`, then
`limsup_{n→∞} |S_n| / √(2 D_n² log log D_n²) ≤ 1` almost surely.
The lim sup is stated in its equivalent eventual form: for every `ε > 0`, almost surely,
`|S_n| ≤ (1 + ε) √(2 D_n² log log D_n²)` for all sufficiently large `n`. -/
theorem theorem2_limsup_le_one {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (a : ℕ → ℝ)
    (ha_ratio : Tendsto (fun n => a n ^ 2 / sqWeightSum a n) atTop (𝓝 0))
    (ha_div : Tendsto (fun n => sqWeightSum a n) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |weightedSum a x n ω|
        ≤ (1 + ε) * Real.sqrt (2 * sqWeightSum a n
            * Real.log (Real.log (sqWeightSum a n))) := by sorry

end AzumaWeightedSums.IteratedLog
