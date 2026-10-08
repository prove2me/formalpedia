-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_3
-- name    : EmpiricalBernstein.SVP.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:37.320337+00:00
-- url     : https://prove2.me/theorems/9df523e8-d6da-419c-beda-30735b9cfe02
-- title:
--   Theorem 3 (Bennett's inequality) — $\mathbb EZ - \frac1n\sum Z_i \le \sqrt{2\mathbb VZ\ln(1/\delta)/n} + \ln(1/\delta)/(3n)$
-- statement:
--   Let $Z, Z_1, \dots, Z_n$ be i.i.d. random variables with values in $[0,1]$, and let $\delta > 0$. Then with probability at least $1 - \delta$,
--
--   $$
--   \mathbb E Z - \frac1n \sum_{i=1}^n Z_i \le \sqrt{\frac{2\,\mathbb V Z \ln(1/\delta)}{n}} + \frac{\ln(1/\delta)}{3n},
--   $$
--
--   where $\mathbb V Z = \mathbb E(Z - \mathbb E Z)^2$ is the variance.
--
--   This is the classical i.i.d. Bennett bound whose confidence interval scales with the unknown variance; the empirical Bernstein bound (Theorem 4) replaces $\mathbb VZ$ by the sample variance. It is used (in both directions, by symmetry) in the proof of Theorem 15.
--
--   **Formalization Note** $Z$ has law $\nu$, a probability measure on $\mathbb R$ with $\nu(\mathbb R\setminus[0,1]) = 0$; the sample $(Z_1,\dots,Z_n)$ is the identity on `Fin n → ℝ` under $\nu^n$; $\mathbb V Z$ is Mathlib's `variance` of the identity under $\nu$. $n \ge 1$ is added: the page leaves $n$ unrestricted, and at $n = 0$ Lean's $1/0 = 0$ makes the statement false.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 3, p. 2 (conditions of Theorem 1, p. 1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace EmpiricalBernstein.SVP

/-- Theorem 3, Bennett's inequality (arXiv:0907.3740v1, p. 2): `Z, Z_1, …, Z_n` i.i.d. with law `ν`
on `[0, 1]`; `(Z_1, …, Z_n)` is the identity on `Fin n → ℝ` under `ν^n`. -/
theorem theorem_3 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => ν) {z | (∫ y, y ∂ν) - (1 / (n : ℝ)) * ∑ i, z i
        > Real.sqrt (2 * variance (fun y : ℝ => y) ν * Real.log (1 / δ) / n)
          + Real.log (1 / δ) / (3 * n)}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
