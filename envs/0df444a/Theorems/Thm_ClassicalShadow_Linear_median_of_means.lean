-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_median_of_means
-- name    : ClassicalShadow.Linear.median_of_means
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:50.997888+00:00
-- url     : https://prove2.me/theorems/f7d3687b-1cf2-47e0-8f9d-f2f5684dc81b
-- title:
--   p. 13, proof of Theorem 1 — median of K means of size N ≥ 34σ²/ε² errs by ≥ ε w.p. ≤ 2e^{−K/2}
-- statement:
--   Let $X$ be a real random variable with finite variance $\sigma^2 = \operatorname{Var}[X]$ and mean $\mathbb E[X]$. Let $X_{k,j}$, $1 \le k \le K$, $1 \le j \le N$, be independent copies of $X$, where $N \ge 1$ is an integer with
--   $$N \ge \frac{34\,\sigma^2}{\epsilon^2}$$
--   for some $\epsilon > 0$. Form the $K$ sample means $\bar X_k = \frac1N\sum_{j=1}^N X_{k,j}$ and their median $\hat\mu(N,K) = \operatorname{median}\{\bar X_1,\dots,\bar X_K\}$. Then
--   $$\Pr\big[\,|\hat\mu(N,K) - \mathbb E[X]| \ge \epsilon\,\big] \le 2e^{-K/2}.$$
--
--   This is the median-of-means guarantee the paper invokes; it converts the variance bound of Lemma 1 into an exponentially small failure probability in the number of batches $K$.
--
--   **Formalization Note.** The statement is in Mathlib's measure-theoretic language: the $X_{k,j}$ are functions on a probability space, mutually independent (`iIndepFun`) and each identically distributed with $X$; $X \in L^2$. "Size $N = 34\sigma^2/\epsilon^2$" is read as an integer $N \ge 1$ at least that value. The median is the lower median of the Setting file (the $\lfloor (K-1)/2\rfloor$-th order statistic, 0-based); every order statistic between the two middle ones obeys the same bound.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 13, proof of Theorem 1

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem median_of_means {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : MeasureTheory.Measure Ω₀) [MeasureTheory.IsProbabilityMeasure P₀]
    (X : Ω₀ → ℝ) (hX : MeasureTheory.MemLp X 2 P₀)
    {K N : ℕ} (hN1 : 1 ≤ N) (Xs : Fin K → Fin N → Ω → ℝ)
    (hind : ProbabilityTheory.iIndepFun (fun p : Fin K × Fin N => Xs p.1 p.2) P)
    (hid : ∀ k j, ProbabilityTheory.IdentDistrib (Xs k j) X P P₀)
    (ε : ℝ) (hε : 0 < ε) (hN : 34 * ProbabilityTheory.variance X P₀ / ε ^ 2 ≤ N) :
    P.real {ω | ε ≤ |median (fun k => (1 / (N : ℝ)) * ∑ j, Xs k j ω) - ∫ x, X x ∂P₀|}
      ≤ 2 * Real.exp (-(K : ℝ) / 2) := by sorry
end ClassicalShadow.Linear
