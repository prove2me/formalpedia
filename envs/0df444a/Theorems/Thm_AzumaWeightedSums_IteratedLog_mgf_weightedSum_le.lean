-- Prove2me | Theorems.Thm_AzumaWeightedSums_IteratedLog_mgf_weightedSum_le
-- name    : AzumaWeightedSums.IteratedLog.mgf_weightedSum_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:30:23.466912+00:00
-- url     : https://prove2.me/theorems/580ab33d-2602-453e-8a30-29411d1f2702
-- title:
--   (2.4) — $E\exp(t\sum b_kx_k)\le\exp(\tfrac{t^2}{2}\sum b_k^2)$ for class [G]
-- statement:
--   Let $(x_n)_{n\ge1}$ be a sequence of random variables on a probability space $(\Omega,\mathfrak A,P)$ with a filtration $(\mathfrak A_n)$, belonging to class [G] with $\tau(x_n)\le1$ for all $n$: martingale differences with $E\{\exp(tx_n)\mid\mathfrak A_{n-1}\}\le\exp(t^2/2)$ a.s. for every real $t$. Then for every $n\ge0$, every real sequence $(b_k)$ and every real $t$,
--   $$
--   E\Big\{\exp\Big(t\sum_{k=1}^n b_kx_k\Big)\Big\}\le\exp\Big(\frac{t^2}{2}\sum_{k=1}^n b_k^2\Big).
--   $$
--
--   This is the moment-generating-function form of the Azuma–Hoeffding inequality: a weighted sum of conditionally sub-Gaussian martingale differences is sub-Gaussian with variance proxy $\sum b_k^2$. It is the first step of the proof of Lemma 2.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral of $\exp(\cdot)$ with values in $[0,\infty]$, so the inequality also asserts that the left side is finite; a Bochner integral would be $0$ for a non-integrable integrand and make the bound trivially true.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, pp. 358–359, display (2.4) in the proof of Lemma 2

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

open MeasureTheory ProbabilityTheory Filter Topology

namespace AzumaWeightedSums.IteratedLog

/-- Azuma 1967, display (2.4) (proof of Lemma 2, pp. 358–359): under [G] with `τ(x_n) ≤ 1`,
`E exp(t Σ_{k=1}^n b_k x_k) ≤ exp((t²/2) Σ_{k=1}^n b_k²)` for every `n`, every real
sequence `(b_k)` and every real `t`. -/
theorem mgf_weightedSum_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * weightedSum b x n ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 / 2 * sqWeightSum b n)) := by sorry

end AzumaWeightedSums.IteratedLog
