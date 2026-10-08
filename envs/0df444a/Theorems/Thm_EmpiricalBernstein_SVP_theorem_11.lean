-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_11
-- name    : EmpiricalBernstein.SVP.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:03.367887+00:00
-- url     : https://prove2.me/theorems/2fa0b878-1885-40a5-b8f5-c2e4c80ac52c
-- title:
--   Theorem 11 — empirical Bernstein bound for independent $[0,1]$ variables
-- statement:
--   Let $n \ge 2$, let $X = (X_1,\dots,X_n)$ be a vector of independent random variables with values in $[0,1]$, and let $\delta > 0$. Then with probability at least $1-\delta$ in $X$,
--
--   $$
--   \mathbb E[P_n(X)] \le P_n(X) + \sqrt{\frac{2V_n(X)\ln(2/\delta)}{n}} + \frac{7\ln(2/\delta)}{3(n-1)},
--   $$
--
--   where $P_n(X)=\frac1n\sum_i X_i$ is the sample mean and $V_n(X)$ the sample variance.
--
--   This extends Theorem 4 to independent, not identically distributed variables; it is the form needed for the symmetrized double sample in the proof of Theorem 6 (Lemma 14).
--
--   **Formalization Note** $X_i \sim \mu_i$ independently, each $\mu_i$ a probability measure on $\mathbb R$ with $\mu_i(\mathbb R\setminus[0,1])=0$; the sample is the identity on `Fin n → ℝ` under $\prod_i\mu_i$, and $\mathbb E[P_n(X)]$ is the integral of $P_n$ against it. **Added hypothesis** $n\ge2$: the page omits it, and at $n=1$ Lean evaluates $V_1=0$ and $7\ln(2/\delta)/0 = 0$, so the bound would read $\mathbb EX_1 \le X_1$, which is false.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 11, p. 4

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

open MeasureTheory VarianceRegularization.Expansion

namespace EmpiricalBernstein.SVP

/-- Theorem 11, the empirical Bernstein bound for independent `[0,1]`-valued variables
(arXiv:0907.3740v1, p. 4), `n ≥ 2`. -/
theorem theorem_11 {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
        > empMean x + Real.sqrt (2 * sampleVar x * Real.log (2 / δ) / n)
          + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
