-- Prove2me | Theorems.Thm_ConformalOutlierTesting_fpr_simultaneous_bound
-- name    : ConformalOutlierTesting.fpr_simultaneous_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:00:56.245794+00:00
-- url     : https://prove2.me/theorems/cbc4d02d-fe81-454a-b814-bd7dd0dd918e
-- title:
--   Proposition 3 (as proved): simultaneous confidence bound for the FPR
-- statement:
--   Let $Z_1,\dots,Z_n$ be i.i.d. with law $\mu$ on $\mathbb R$ and cumulative distribution function $F$. Let $b_0=0\le b_1\le\dots\le b_n\le b_{n+1}=1$ satisfy the band condition of Theorem 4 at level $\delta\in(0,1)$. Then
--
--   $$\mathbb P\Big[F(z)\le b_{|\{j:Z_j\le z\}|+1}\ \text{ for all }z\in\mathbb R\Big]\ge1-\delta.$$
--
--   Equivalently, $F(z)\le h(\hat F_n(z))$ wherever $\hat F_n(z)>0$, and $F(z)\le b_1$ for $z<Z_{(1)}$, where $h(t)=b_{\lceil(n+1)t\rceil}$ and $\hat F_n$ is the empirical distribution function. Applied to the scores of a one-class classifier, this gives a uniform upper confidence bound for its false positive rate as a function of the threshold.
--
--   **Formalization Note** The paper states $\mathbb P[F(z)\le h(\hat F_n(z))\ \forall z]\ge1-\delta$ with $h$ as in Theorem 4. Since $h(0)=b_0=0$, that would need $F(z)=0$ for every $z<Z_{(1)}$, which fails with probability one for continuous $F$. The proof uses $h(i/n)=b_{i+1}$, which holds for $i\ge1$ but not for $i=0$. What the proof establishes is the bound by $b_{n\hat F_n(z)+1}$ stated here. It holds for any law $\mu$, as the paper's "some distribution" allows.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 4.1, Proposition 3, eq. (21), p. 17; proof in Appendix A.6, p. 46

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem fpr_simultaneous_bound {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (b : ℕ → ℝ) (hb : IsCCVSequence n δ b) :
    ENNReal.ofReal (1 - δ) ≤ (Measure.pi fun _ : Fin n => μ)
      {z | ∀ x : ℝ, cdf μ x ≤ b ((Finset.univ.filter fun j => z j ≤ x).card + 1)} := by sorry

end ConformalOutlierTesting
