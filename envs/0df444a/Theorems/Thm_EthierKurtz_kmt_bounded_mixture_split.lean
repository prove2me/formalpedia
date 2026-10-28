-- Prove2me | Theorems.Thm_EthierKurtz_kmt_bounded_mixture_split
-- name    : EthierKurtz.kmt_bounded_mixture_split
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T23:29:18.768149+00:00
-- url     : https://prove2.me/theorems/e822776c-1c33-4b5d-b08b-82a44d8ba72c
-- title:
--   A law with exponential moments splits into a bounded part and a rest
-- statement:
--   Let $\mu$ be a probability law on $\mathbb R$ with mean $0$, variance $1$ and $\int e^{ax}\,d\mu<\infty$ for $|a|\le a_0$. Then $$\mu=pF_1+(1-p)F_2,\qquad 0<p<1,$$ with $F_1$ supported in some $[-K,K]$ and of positive variance, such that $\nu=p\,N(m_1,\sigma_1^2)+(1-p)F_2$ ($m_1,\sigma_1^2$ the mean and variance of $F_1$) again has mean $0$, variance $1$ and finite exponential moments near $0$.
--
--   Role: the first step of the proof of the general KMT theorem: it reduces it to a bounded law and to a law with a Gaussian component.
-- source:
--   Komlós, Major, Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, Section 2, proof of Theorem 1 from Theorems 1A and 1B, p. 37

import Mathlib
open MeasureTheory ProbabilityTheory

namespace EthierKurtz

theorem kmt_bounded_mixture_split (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hexp : (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) μ))
    (hmean : ∫ x : ℝ, x ∂μ = 0) (hvariance : variance (fun x : ℝ => x) μ = 1) :
    ∃ (p : ℝ) (F1 F2 : Measure ℝ) (_ : IsProbabilityMeasure F1) (_ : IsProbabilityMeasure F2),
      0 < p ∧ p < 1 ∧ (∃ K : ℝ, F1 (Set.Icc (-K) K) = 1) ∧
      0 < variance (fun x : ℝ => x) F1 ∧
      μ = ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2 ∧
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) (ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2)) ∧
      ∫ x, x ∂(ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2) = 0 ∧
      variance (fun x : ℝ => x) (ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2) = 1 := by sorry

end EthierKurtz
