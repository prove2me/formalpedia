-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_10
-- name    : EmpiricalBernstein.SVP.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:48.912585+00:00
-- url     : https://prove2.me/theorems/ab0a8b3d-b1aa-43bd-a787-0e76329c53a1
-- title:
--   Theorem 10 — $\sqrt{\mathbb EV_n}$ and $\sqrt{V_n}$ differ by more than $\sqrt{2\ln(1/\delta)/(n-1)}$ with probability at most $\delta$
-- statement:
--   Let $n \ge 2$ and let $X = (X_1,\dots,X_n)$ be a vector of independent random variables with values in $[0,1]$. Write $\mathbb E V_n$ for $\mathbb E_X V_n(X)$, where $V_n$ is the sample variance. Then for every $\delta > 0$,
--
--   $$
--   \Pr\Big\{ \sqrt{\mathbb E V_n} > \sqrt{V_n(X)} + \sqrt{\frac{2\ln(1/\delta)}{n-1}} \Big\} \le \delta, \qquad (3)
--   $$
--
--   $$
--   \Pr\Big\{ \sqrt{V_n(X)} > \sqrt{\mathbb E V_n} + \sqrt{\frac{2\ln(1/\delta)}{n-1}} \Big\} \le \delta. \qquad (4)
--   $$
--
--   These are confidence bounds for the standard deviation in terms of the observable sample standard deviation; for i.i.d. variables $\mathbb EV_n$ is the true variance. They feed the empirical Bernstein bound (Theorem 11) and the excess-risk bound for sample variance penalization (Theorem 15).
--
--   **Formalization Note** $X_i \sim \mu_i$ independently, each $\mu_i$ a probability measure on $\mathbb R$ with $\mu_i(\mathbb R \setminus [0,1]) = 0$; the sample is the identity on `Fin n → ℝ` under $\prod_i\mu_i$, and $\mathbb E V_n$ is the integral of $V_n$ against it. "With probability at most $\delta$" is the product measure of the event being at most $\delta$. For $\delta \ge 1$ both statements are trivially true.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 10, eqs. (3)–(4), p. 4

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Theorem 10 (arXiv:0907.3740v1, p. 4): confidence bounds (3) and (4) for the standard deviation
of independent `[0,1]`-valued variables, `𝔼V_n = ∫ V_n d(∏ μ_i)`. -/
theorem theorem_10 {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi μs {x | Real.sqrt (∫ z, sampleVar z ∂(Measure.pi μs))
        > Real.sqrt (sampleVar x) + Real.sqrt (2 * Real.log (1 / δ) / ((n : ℝ) - 1))}
        ≤ ENNReal.ofReal δ ∧
      Measure.pi μs {x | Real.sqrt (sampleVar x)
        > Real.sqrt (∫ z, sampleVar z ∂(Measure.pi μs))
          + Real.sqrt (2 * Real.log (1 / δ) / ((n : ℝ) - 1))}
        ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
