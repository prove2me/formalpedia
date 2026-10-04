-- Prove2me | Theorems.Thm_AzumaWeightedSums_IteratedLog_doob_Lp_maximal
-- name    : AzumaWeightedSums.IteratedLog.doob_Lp_maximal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:06:59.879461+00:00
-- url     : https://prove2.me/theorems/3bfeeb14-c427-4166-83b5-23ad33d7e950
-- title:
--   Doob's $L^\alpha$ maximal inequality for nonnegative submartingales (cited on p. 359)
-- statement:
--   Let $(f_m)_{m\ge0}$ be a submartingale on a probability space with respect to a filtration $(\mathfrak A_m)$, and suppose $f_m(\omega)\ge0$ for all $m$ and $\omega$. Then for every $n\ge0$ and every real $\alpha>1$,
--   $$
--   E\Big\{\Big(\max_{0\le m\le n} f_m\Big)^{\alpha}\Big\}\le\Big(\frac{\alpha}{\alpha-1}\Big)^{\alpha}E\{f_n^{\alpha}\}.
--   $$
--
--   Azuma applies this inequality, citing Doob's *Stochastic Processes* (1953), p. 317, to the nonnegative submartingale $(|S_m|)$ of weighted sums of martingale differences, to compare the moments of the maximal sum $S_n^*$ with those of $S_n$. It is the classical $L^p$ form of Doob's maximal inequality.
--
--   **Formalization Note** Both expectations are lower Lebesgue integrals with values in $[0,\infty]$, so the statement is meaningful (and trivially true) when $E\{f_n^\alpha\}=\infty$. Powers are real powers of nonnegative reals.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, p. 359, proof of Lemma 2, citing J. L. Doob, Stochastic Processes, Wiley 1953, p. 317

import Mathlib

open MeasureTheory

namespace AzumaWeightedSums.IteratedLog

/-- Doob's `L^α` maximal inequality for nonnegative submartingales, as cited by Azuma 1967
(proof of Lemma 2, p. 359, from Doob, *Stochastic Processes*, p. 317): for a nonnegative
submartingale `(f_m)`, every `n` and every real `α > 1`,
`E{(max_{m ≤ n} f_m)^α} ≤ (α/(α−1))^α E{f_n^α}`. -/
theorem doob_Lp_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω) (n : ℕ) {α : ℝ} (hα : 1 < α) :
    ∫⁻ ω, ENNReal.ofReal
        (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ
      ≤ ENNReal.ofReal ((α / (α - 1)) ^ α) * ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by sorry

end AzumaWeightedSums.IteratedLog
