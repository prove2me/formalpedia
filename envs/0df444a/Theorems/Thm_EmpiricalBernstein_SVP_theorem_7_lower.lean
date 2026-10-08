-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_7_lower
-- name    : EmpiricalBernstein.SVP.theorem_7_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:28.13522+00:00
-- url     : https://prove2.me/theorems/43dcdae5-a731-4849-8cb7-205296a8f729
-- title:
--   Theorem 7 (lower tail) — $\Pr\{\mathbb EZ - Z > t\} \le \exp(-t^2/(2a\mathbb EZ))$ for self-bounding $Z$
-- statement:
--   Let $X = (X_1,\dots,X_n)$ be a vector of independent random variables with values in a set $\mathcal X$, $X_i \sim \mu_i$. For $1 \le k \le n$ and $y \in \mathcal X$ let $X_{y,k}$ be the vector obtained from $X$ by replacing $X_k$ by $y$. Let $a \ge 1$ and let $Z = Z(X) \ge 0$ satisfy, almost surely,
--
--   $$
--   Z(X) - \inf_{y \in \mathcal X} Z(X_{y,k}) \le 1 \quad \forall k, \qquad (1)
--   $$
--
--   $$
--   \sum_{k=1}^n \Big( Z(X) - \inf_{y\in\mathcal X} Z(X_{y,k}) \Big)^2 \le a\, Z(X). \qquad (2)
--   $$
--
--   Then for every $t > 0$,
--
--   $$
--   \Pr\{\mathbb E Z - Z > t\} \le \exp\Big( \frac{-t^2}{2a\,\mathbb E Z} \Big).
--   $$
--
--   This is the paper's citation of Maurer (2006, Theorem 13), a concentration inequality for self-bounding functions obtained by the entropy method. With $Z = nV_n$ it gives the lower tail (5) of the sample variance.
--
--   **Formalization Note** The sample space is $\mathcal X^n$ (`Fin n → 𝒳`, index $k=1,\dots,n$ is `k : Fin n`) with the product measure $\prod_i \mu_i$; $X_{y,k}$ is `Function.update x k y`. Three hypotheses make the paper's standing convention "questions of measurability will be ignored" precise: $Z$ is measurable and integrable, $Z \ge 0$ everywhere (implied almost surely by (2), and needed so that the real infimum is a genuine infimum), and each $x \mapsto \inf_y Z(x_{y,k})$ is measurable. If $\mathbb E Z = 0$, Lean evaluates the exponent as $0$ and the bound as $1$. This is a cited result: the statement was transcribed from the paper, not from the cited source.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 7, p. 3 (citing Maurer 2006, Theorem 13)

import Mathlib

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Theorem 7, first part (arXiv:0907.3740v1, p. 3; Maurer 2006, Theorem 13): lower tail of a
nonnegative function `Z` of independent variables satisfying (1) and (2) almost surely.
`X_{y,k}` is `Function.update x k y`. -/
theorem theorem_7_lower {𝒳 : Type*} [MeasurableSpace 𝒳] {n : ℕ}
    (μs : Fin n → Measure 𝒳) [∀ i, IsProbabilityMeasure (μs i)]
    (Z : (Fin n → 𝒳) → ℝ) (hZm : Measurable Z) (hZi : Integrable Z (Measure.pi μs))
    (hZ0 : ∀ x, 0 ≤ Z x)
    (hinf : ∀ k, Measurable (fun x => ⨅ y : 𝒳, Z (Function.update x k y)))
    (a : ℝ) (ha : 1 ≤ a)
    (h1 : ∀ᵐ x ∂(Measure.pi μs), ∀ k, Z x - ⨅ y : 𝒳, Z (Function.update x k y) ≤ 1)
    (h2 : ∀ᵐ x ∂(Measure.pi μs),
      ∑ k, (Z x - ⨅ y : 𝒳, Z (Function.update x k y)) ^ 2 ≤ a * Z x)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μs {x | (∫ z, Z z ∂(Measure.pi μs)) - Z x > t}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * a * ∫ z, Z z ∂(Measure.pi μs)))) := by sorry

end EmpiricalBernstein.SVP
