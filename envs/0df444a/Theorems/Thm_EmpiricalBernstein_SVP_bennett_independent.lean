-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_bennett_independent
-- name    : EmpiricalBernstein.SVP.bennett_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:46.879823+00:00
-- url     : https://prove2.me/theorems/880893b1-8eac-4f09-bcd4-b6a53a171762
-- title:
--   Bennett's inequality for independent $[0,1]$ variables — $\mathbb EP_n \le P_n + \sqrt{2W\ln(1/\delta)/n} + \ln(1/\delta)/(3n)$
-- statement:
--   Let $n \ge 1$ and let $X = (X_1,\dots,X_n)$ be a vector of independent, not necessarily identically distributed, random variables with values in $[0,1]$. Let $W = \frac1n\sum_i \mathbb V X_i$ and let $P_n(X) = \frac1n\sum_i X_i$ be the sample mean. Then for every $\delta > 0$, with probability at least $1-\delta$,
--
--   $$
--   \mathbb E P_n(X) \le P_n(X) + \sqrt{\frac{2W\ln(1/\delta)}{n}} + \frac{\ln(1/\delta)}{3n}.
--   $$
--
--   This is the form of Bennett's inequality recalled in the proof of Theorem 11 (the paper cites McDiarmid's survey, its reference [8], for the non-identically distributed case); it is combined there with $W \le \mathbb EV_n$ and Theorem 10. The same statement applied to $1 - X_i$ gives the reverse direction used in Lemma 14.
--
--   **Formalization Note** $X_i \sim \mu_i$ independently, each $\mu_i$ a probability measure on $\mathbb R$ with $\mu_i(\mathbb R\setminus[0,1]) = 0$; the sample is the identity on `Fin n → ℝ` under $\prod_i\mu_i$, and "with probability at least $1-\delta$" is written as the product measure of the complementary (strict) event being at most $\delta$. $n \ge 1$ is added: at $n = 0$ Lean's $1/0 = 0$ would make the statement false.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, proof of Theorem 11, p. 4, display after 'Recall that Bennett's inequality'

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion

namespace EmpiricalBernstein.SVP

/-- Bennett's inequality for independent, not necessarily identically distributed, `[0,1]`-valued
variables, as used in the proof of Theorem 11 (arXiv:0907.3740v1, p. 4), with
`W = (1/n) ∑ 𝕍X_i`. -/
theorem bennett_independent {n : ℕ} (hn : 1 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
        > empMean x
          + Real.sqrt (2 * ((1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i))
              * Real.log (1 / δ) / n)
          + Real.log (1 / δ) / (3 * n)}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
