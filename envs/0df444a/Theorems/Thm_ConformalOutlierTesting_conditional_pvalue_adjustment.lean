-- Prove2me | Theorems.Thm_ConformalOutlierTesting_conditional_pvalue_adjustment
-- name    : ConformalOutlierTesting.conditional_pvalue_adjustment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:00:33.239674+00:00
-- url     : https://prove2.me/theorems/ff421f52-b8cd-45a0-b6da-6a1a5a1fcf95
-- title:
--   Theorem 4: conditional p-value adjustment
-- statement:
--   Let $U_1,\dots,U_n$ be i.i.d. uniform on $[0,1]$ with order statistics $U_{(1)}\le\dots\le U_{(n)}$, and fix $\delta\in(0,1)$. Let $0\le b_1\le\dots\le b_n\le1$ satisfy
--
--   $$\mathbb P\big[U_{(1)}\le b_1,\dots,U_{(n)}\le b_n\big]\ge1-\delta,$$
--
--   let $b_0=0$ and $b_{n+1}=1$, and let $h(t)=b_{\lceil(n+1)t\rceil}$ for $t\in[0,1]$. Let the calibration scores be i.i.d. with law $\mu$, and let $X_{2n+1}$ be an inlier whose score has law $\mu$ and is independent of $\mathcal D$. Then $\hat u^{(\mathrm{ccv})}=h\circ\hat u^{(\mathrm{marg})}$ is a calibration-conditionally valid p-value:
--
--   $$\mathbb P\Big[\ \mathbb P\big[\hat u^{(\mathrm{ccv})}(X_{2n+1})\le t\mid\mathcal D\big]\le t\ \text{ for all }t\in(0,1)\Big]\ge1-\delta.$$
--
--   Any simultaneous upper confidence band for uniform order statistics therefore yields p-values that are valid conditionally on the calibration data, with high probability.
--
--   **Formalization Note** The theorem does not assume continuous scores, and its proof treats a general score law, so $\mu$ is any probability law on $\mathbb R$. The inner conditional probability is the $\mu$-probability with the calibration scores held fixed.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 3.2, Theorem 4, eqs. (4), (10), (11), p. 9; proof in Appendix A.5, p. 46

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem conditional_pvalue_adjustment {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (b : ℕ → ℝ) (hb : IsCCVSequence n δ b) :
    ENNReal.ofReal (1 - δ) ≤ (Measure.pi fun _ : Fin n => μ)
      {s | ∀ t ∈ Ioo (0 : ℝ) 1, μ {x | adjFun b n (margPval s x) ≤ t} ≤ ENNReal.ofReal t} := by sorry

end ConformalOutlierTesting
