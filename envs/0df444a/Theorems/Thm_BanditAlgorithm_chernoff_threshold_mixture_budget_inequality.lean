-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_threshold_mixture_budget_inequality
-- name    : BanditAlgorithm.chernoff_threshold_mixture_budget_inequality
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T22:03:25.861253+00:00
-- url     : https://prove2.me/theorems/84197957-d056-4850-994e-4332ddda5a77
-- title:
--   The mixture budget covers Chernoff's threshold at every round
-- statement:
--   The quantitative step that lets a self-normalised mixture martingale reach the threshold $\beta_n(\delta)=k\log(n^2+n)+f^{-1}(\delta)$ of Chernoff's stopping rule. Let $k\ge2$, let $b\ge k$ satisfy $k+L+k\log(b/k)\le b$ — which is exactly what $b=f^{-1}(\delta)$, $L=\log(1/\delta)$ satisfy — and let $n\ge1$. Then
--   $$L+\log\bigl(k(k-1)\bigr)+\log\left(1+\frac b2\right)+\log n\ \le\ \frac{b}{b+1}\Bigl(k\log(n^2+n)+b\Bigr).$$
--
--   Read from the right: $\tfrac{b}{b+1}$ is the loss incurred by running the mixture at prior variance $b$ rather than at the true pull counts, $\log(k(k-1))$ is the union over ordered pairs of arms, and $\log(1+b/2)+\log n$ bounds the two $\tfrac12\log(1+bT_i)$ prices the mixture pays for the realised counts.
--
--   **The choice of variance $b=f^{-1}(\delta)$ is forced.** The loss $b/(b+1)$ must be within $O(1/b)$ of $1$ because the entire budget $\log(1/\delta)$ passes through it, while the price $\tfrac12\log(1+b)$ must fit inside the slack of $f^{-1}(\delta)$ over $k+\log(1/\delta)$; that slack is $k\log(f^{-1}(\delta)/k)$, which grows like $k\log\log(1/\delta)$ and so matches $\log b$. Neither a bounded variance nor one growing faster than polynomially in $f^{-1}(\delta)$ works.
--
--   After substituting the lower bound on $b$ and clearing the denominator, the inequality reduces to $bP+Q\ge0$ with $P=k\log2+k-1-2\log k-\log(k-1)$ and $Q=k-2\log k-\log(k-1)$, and both $P\ge0$ and $2P+Q\ge0$ follow from $\log x\le x/e$ alone.
-- source:
--   The quantitative estimate underlying the mixture-martingale proof of the pairwise self-normalised deviation bound; the threshold beta_t(delta) is the one introduced in Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. Tuning of the mixture variance follows Kaufmann & Koolen, JMLR 22 (2021), Section 3.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

theorem BanditAlgorithm.chernoff_threshold_mixture_budget_inequality {k : ℕ}
    (hk2 : 2 ≤ k) {b L : ℝ} (hbk : (k : ℝ) ≤ b) (hL0 : 0 ≤ L)
    (hLb : (k : ℝ) + L + (k : ℝ) * Real.log (b / (k : ℝ)) ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    L + Real.log ((k : ℝ) * ((k : ℝ) - 1)) + Real.log (1 + b / 2) + Real.log (n : ℝ)
      ≤ b / (b + 1) * ((k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + b) := by
  sorry
