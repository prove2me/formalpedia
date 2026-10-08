-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_eq_7_9
-- name    : EmpiricalBernstein.SVP.eq_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:55.722048+00:00
-- url     : https://prove2.me/theorems/3d87133e-dd5d-4223-9de0-4fa3cb408a9e
-- title:
--   Eqs. (7)–(9) — $W = \frac1n\sum_i\mathbb VX_i \le \mathbb EV_n$ for independent variables
-- statement:
--   Let $n \ge 2$ and let $X_1,\dots,X_n$ be independent random variables with values in $[0,1]$. Write $W = \frac1n \sum_i \mathbb V X_i$ for the average variance. Then
--
--   $$
--   W \le \frac1n \sum_i \mathbb E(X_i - \mathbb E X_i)^2 + \frac{1}{2n(n-1)} \sum_{i \ne j} (\mathbb E X_i - \mathbb E X_j)^2 = \frac{1}{2n(n-1)}\sum_{i,j}\mathbb E(X_i - X_j)^2 = \mathbb E V_n .
--   $$
--
--   The statement asserts the inequality $W \le \mathbb E V_n$ and the identity between the sum of the terms (7)–(8) and $\mathbb E V_n$. For non-identically distributed variables, the expected sample variance overestimates the average variance by the spread of the means; this is what lets Bennett's inequality be combined with the variance bounds of Theorem 10.
--
--   **Formalization Note** $X_i \sim \mu_i$, each $\mu_i$ a probability measure on $\mathbb R$ with $\mu_i(\mathbb R\setminus[0,1]) = 0$; $\mathbb E V_n$ is the integral of $V_n$ against $\prod_i \mu_i$; $\mathbb V X_i$ is Mathlib's `variance` of the identity under $\mu_i$. The display sits inside the proof of Theorem 11, whose hypotheses ($[0,1]$-valued independent variables) are used here; $n\ge2$ is needed for $V_n$. The paper's indices are Lean's `Fin n`.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, eqs. (7)–(9), p. 4 (proof of Theorem 11)

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

open MeasureTheory ProbabilityTheory

namespace EmpiricalBernstein.SVP

/-- Eqs. (7)–(9) (arXiv:0907.3740v1, p. 4, proof of Theorem 11): for independent `[0,1]`-valued
`X_i ∼ μ_i` and `n ≥ 2`, `W = (1/n) ∑ 𝕍X_i ≤ 𝔼V_n`, with `(7) + (8) = 𝔼V_n`. -/
theorem eq_7_9 {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    (1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i)
        ≤ ∫ z, sampleVar z ∂(Measure.pi μs) ∧
      (1 / (n : ℝ)) * ∑ i, ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)
          + 1 / (2 * (n : ℝ) * ((n : ℝ) - 1))
            * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
                ((∫ w, w ∂(μs i)) - ∫ w, w ∂(μs j)) ^ 2
        = ∫ z, sampleVar z ∂(Measure.pi μs) := by sorry

end EmpiricalBernstein.SVP
