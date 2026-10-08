-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_7_upper
-- name    : EmpiricalBernstein.SVP.theorem_7_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:33.143023+00:00
-- url     : https://prove2.me/theorems/eed9b28c-fa1a-4418-a98b-15c452182627
-- title:
--   Theorem 7 (upper tail) — $\Pr\{Z - \mathbb EZ > t\} \le \exp(-t^2/(2a\mathbb EZ + at))$ under (2) only
-- statement:
--   Let $X = (X_1,\dots,X_n)$ be a vector of independent random variables with values in a set $\mathcal X$, $X_i\sim\mu_i$, and let $X_{y,k}$ be $X$ with its $k$-th coordinate replaced by $y \in \mathcal X$. Let $a \ge 1$ and let $Z = Z(X) \ge 0$ satisfy, almost surely, only the self-boundedness condition
--
--   $$
--   \sum_{k=1}^n \Big( Z(X) - \inf_{y\in\mathcal X} Z(X_{y,k}) \Big)^2 \le a\, Z(X). \qquad (2)
--   $$
--
--   Then for every $t > 0$,
--
--   $$
--   \Pr\{Z - \mathbb E Z > t\} \le \exp\Big( \frac{-t^2}{2a\,\mathbb E Z + a t} \Big).
--   $$
--
--   This is the second half of the paper's citation of Maurer (2006, Theorem 13). With $Z = nV_n$ it gives the upper tail (6) of the sample variance.
--
--   **Formalization Note** As in the lower-tail item: sample space `Fin n → 𝒳` under $\prod_i\mu_i$, $X_{y,k}$ is `Function.update x k y`, and the added hypotheses ($Z$ measurable, integrable and nonnegative everywhere; each $x\mapsto \inf_y Z(x_{y,k})$ measurable) make the paper's convention of ignoring measurability precise. This is a cited result, transcribed from the paper.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 7, p. 3 (citing Maurer 2006, Theorem 13)

import Mathlib

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Theorem 7, second part (arXiv:0907.3740v1, p. 3; Maurer 2006, Theorem 13): upper tail of a
nonnegative function `Z` of independent variables satisfying only the self-boundedness condition
(2) almost surely. `X_{y,k}` is `Function.update x k y`. -/
theorem theorem_7_upper {𝒳 : Type*} [MeasurableSpace 𝒳] {n : ℕ}
    (μs : Fin n → Measure 𝒳) [∀ i, IsProbabilityMeasure (μs i)]
    (Z : (Fin n → 𝒳) → ℝ) (hZm : Measurable Z) (hZi : Integrable Z (Measure.pi μs))
    (hZ0 : ∀ x, 0 ≤ Z x)
    (hinf : ∀ k, Measurable (fun x => ⨅ y : 𝒳, Z (Function.update x k y)))
    (a : ℝ) (ha : 1 ≤ a)
    (h2 : ∀ᵐ x ∂(Measure.pi μs),
      ∑ k, (Z x - ⨅ y : 𝒳, Z (Function.update x k y)) ^ 2 ≤ a * Z x)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μs {x | Z x - (∫ z, Z z ∂(Measure.pi μs)) > t}
      ≤ ENNReal.ofReal
          (Real.exp (-t ^ 2 / (2 * a * (∫ z, Z z ∂(Measure.pi μs)) + a * t))) := by sorry

end EmpiricalBernstein.SVP
