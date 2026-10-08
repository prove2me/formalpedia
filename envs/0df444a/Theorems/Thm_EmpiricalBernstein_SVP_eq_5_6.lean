-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_eq_5_6
-- name    : EmpiricalBernstein.SVP.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:50.244914+00:00
-- url     : https://prove2.me/theorems/ae6ad573-4044-4278-bf1f-34dfd107cafe
-- title:
--   Eqs. (5)–(6) — exponential tails of the sample variance $V_n$ around $\mathbb EV_n$
-- statement:
--   Let $n \ge 2$ and let $X = (X_1,\dots,X_n)$ be a vector of independent random variables with values in $[0,1]$, and write $\mathbb E V_n = \mathbb E_X V_n(X)$. Then for every $s > 0$,
--
--   $$
--   \Pr\{\mathbb E V_n - V_n(X) > s\} \le \exp\Big( \frac{-(n-1)s^2}{2\,\mathbb E V_n} \Big), \qquad (5)
--   $$
--
--   $$
--   \Pr\{V_n(X) - \mathbb E V_n > s\} \le \exp\Big( \frac{-(n-1)s^2}{2\,\mathbb E V_n + s} \Big). \qquad (6)
--   $$
--
--   These are the concentration inequalities for the sample variance of a bounded random variable that the paper singles out as being of independent interest; Theorem 10 follows from them by solving for $s$.
--
--   **Formalization Note** The hypotheses are those of Theorem 10, inside whose proof (5)–(6) are derived: $X_i \sim \mu_i$ independent, each $\mu_i$ a probability measure on $\mathbb R$ with $\mu_i(\mathbb R\setminus[0,1]) = 0$, and the sample is the identity on `Fin n → ℝ` under $\prod_i \mu_i$. If $\mathbb E V_n = 0$, Lean evaluates the exponent in (5) as $0$, so the bound reads $1$.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, eqs. (5)–(6), p. 4 (proof of Theorem 10)

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Eqs. (5)–(6) (arXiv:0907.3740v1, p. 4, proof of Theorem 10): tails of the sample variance of
independent `[0,1]`-valued variables, `n ≥ 2`. -/
theorem eq_5_6 {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (s : ℝ) (hs : 0 < s) :
    Measure.pi μs {x | (∫ z, sampleVar z ∂(Measure.pi μs)) - sampleVar x > s}
        ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * s ^ 2
            / (2 * ∫ z, sampleVar z ∂(Measure.pi μs)))) ∧
      Measure.pi μs {x | sampleVar x - (∫ z, sampleVar z ∂(Measure.pi μs)) > s}
        ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) - 1) * s ^ 2
            / (2 * (∫ z, sampleVar z ∂(Measure.pi μs)) + s))) := by sorry

end EmpiricalBernstein.SVP
