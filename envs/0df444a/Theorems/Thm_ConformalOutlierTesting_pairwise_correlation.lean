-- Prove2me | Theorems.Thm_ConformalOutlierTesting_pairwise_correlation
-- name    : ConformalOutlierTesting.pairwise_correlation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:55:13.578596+00:00
-- url     : https://prove2.me/theorems/285064c4-b684-40b9-8909-68dc8911a7e1
-- title:
--   Lemma 1: null conformal p-values have pairwise correlation 1/(n+2)
-- statement:
--   Let the calibration scores be i.i.d. with a continuous (atomless) law $\mu$. Let test points $i\ne j$ be inliers, so their scores have law $\mu$, and let all test scores be independent of each other and of the calibration data. Let $G:[0,1]\to\mathbb R$ be finite-valued and not constant on the grid $\{1/(n+1),\dots,(n+1)/(n+1)\}$. Then
--
--   $$\mathrm{Cor}\big[G(\hat u^{(\mathrm{marg})}(X_{2n+i})),\,G(\hat u^{(\mathrm{marg})}(X_{2n+j}))\big]=\frac1{n+2}.$$
--
--   So null conformal p-values are positively correlated after any transformation. This makes the variance of a combination statistic larger than under independence.
--
--   **Formalization Note** The paper allows any finite-valued $G$. If $G$ is constant on the grid, both variances are $0$ and the correlation is undefined. The hypothesis that $G$ takes two different values on the grid is therefore added.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 2.1, Lemma 1, eq. (3), p. 6; proof in Appendix A.1, p. 32

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem pairwise_correlation {n m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (I : Finset (Fin m))
    (hI : ∀ j ∈ I, ν j = μ) (i j : Fin m) (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (G : ℝ → ℝ)
    (hG : ∃ k k' : ℕ, 1 ≤ k ∧ k ≤ n + 1 ∧ 1 ≤ k' ∧ k' ≤ n + 1 ∧
      G ((k : ℝ) / (n + 1)) ≠ G ((k' : ℝ) / (n + 1))) :
    corr (scoreLaw (n := n) μ ν) (fun ω => G (margPvals ω i)) (fun ω => G (margPvals ω j)) =
      1 / ((n : ℝ) + 2) := by sorry

end ConformalOutlierTesting
