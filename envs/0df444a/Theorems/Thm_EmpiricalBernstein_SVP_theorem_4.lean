-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_4
-- name    : EmpiricalBernstein.SVP.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:55.003557+00:00
-- url     : https://prove2.me/theorems/f4000db6-aeaa-4ac8-82b5-6dbd93909aff
-- title:
--   Theorem 4 (empirical Bernstein bound) — $\mathbb EZ - \frac1n\sum Z_i \le \sqrt{2V_n(Z)\ln(2/\delta)/n} + 7\ln(2/\delta)/(3(n-1))$
-- statement:
--   Let $n \ge 2$, let $Z, Z_1, \dots, Z_n$ be i.i.d. random variables with values in $[0,1]$, and let $\delta > 0$. Then with probability at least $1 - \delta$ in the i.i.d. vector $\mathbf Z = (Z_1,\dots,Z_n)$,
--
--   $$
--   \mathbb E Z - \frac1n\sum_{i=1}^n Z_i \le \sqrt{\frac{2V_n(\mathbf Z)\ln(2/\delta)}{n}} + \frac{7\ln(2/\delta)}{3(n-1)},
--   $$
--
--   where $V_n(\mathbf Z) = \frac{1}{n(n-1)}\sum_{1\le i<j\le n}(Z_i - Z_j)^2$ is the sample variance.
--
--   This is the paper's headline result: a Bernstein-type confidence bound in which the unknown variance is replaced by an observable quantity, at the price of a slightly larger $1/n$ term.
--
--   **Formalization Note** $Z$ has law $\nu$, a probability measure on $\mathbb R$ with $\nu(\mathbb R \setminus [0,1]) = 0$; $\mathbf Z$ is the identity on `Fin n → ℝ` under $\nu^n$; $V_n$ is the definition `sampleVar`, whose double sum $\frac{1}{n(n-1)}\sum_{i,j}(Z_i-Z_j)^2/2$ equals the paper's sum over $i<j$. **Added hypothesis** $n \ge 2$: the page does not state it, and at $n = 1$ Lean evaluates $V_1 = 0$ and $7\ln(2/\delta)/0 = 0$, which would make the statement false.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 4, p. 2

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Theorem 4, the empirical Bernstein bound (arXiv:0907.3740v1, p. 2): `Z, Z_1, …, Z_n` i.i.d.
with law `ν` on `[0, 1]`, `n ≥ 2`. -/
theorem theorem_4 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => ν) {z | (∫ y, y ∂ν) - (1 / (n : ℝ)) * ∑ i, z i
        > Real.sqrt (2 * sampleVar z * Real.log (2 / δ) / n)
          + 7 * Real.log (2 / δ) / (3 * ((n : ℝ) - 1))}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
