-- Prove2me | Theorems.Thm_ConformalOutlierTesting_calibration_scores_given_pvalue
-- name    : ConformalOutlierTesting.calibration_scores_given_pvalue
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:57:08.332705+00:00
-- url     : https://prove2.me/theorems/f4432cc3-33ba-4bff-87b0-19b0130e2b36
-- title:
--   Lemma 5: a larger p-value means smaller calibration scores
-- statement:
--   Work in the setting of Theorem 2 with continuous scores. Let $i$ be an inlier, and let $Z=(S_{(1)},\dots,S_{(n)})$ be the order statistics of the calibration scores and $Y_i=\hat u^{(\mathrm{marg})}(X_{2n+i})$. Let $y\ge y'$ be two values that $Y_i$ takes, namely $y=k/(n+1)$ and $y'=k'/(n+1)$ with $1\le k'\le k\le n+1$. Then there exist random vectors
--
--   $$Z_1\sim\big(Z\mid Y_i=y\big),\qquad Z_2\sim\big(Z\mid Y_i=y'\big)\qquad\text{with}\qquad\mathbb P[Z_1\preceq Z_2]=1.$$
--
--   That is, a larger conformal p-value means stochastically smaller calibration scores. This is the key step in the proof of Theorem 2.
--
--   **Formalization Note** The coupling is a probability measure on pairs whose two marginals are the two conditional laws and which is concentrated on $\{z_1\le z_2\}$ coordinatewise. The values $y,y'$ are restricted to the grid $\{k/(n+1)\}$, the only values with positive probability. This makes both conditional laws well defined.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Appendix A.3, Lemma 5, p. 39; continuous-case proof p. 40

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem calibration_scores_given_pvalue {n m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (ν : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (I : Finset (Fin m))
    (hI : ∀ j ∈ I, ν j = μ) (i : Fin m) (hi : i ∈ I)
    (k k' : ℕ) (hk' : 1 ≤ k') (hkk : k' ≤ k) (hk : k ≤ n + 1) :
    ∃ κ : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = (ProbabilityTheory.cond (scoreLaw (n := n) μ ν) {ω | margPvals ω i = (k : ℝ) / (n + 1)}).map
        (fun ω => orderStat ω.1) ∧
      κ.map Prod.snd = (ProbabilityTheory.cond (scoreLaw (n := n) μ ν) {ω | margPvals ω i = (k' : ℝ) / (n + 1)}).map
        (fun ω => orderStat ω.1) ∧
      ∀ᵐ x ∂κ, x.1 ≤ x.2 := by sorry

end ConformalOutlierTesting
