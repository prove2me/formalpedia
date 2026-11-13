-- Prove2me | Theorems.Thm_DeepQOperator_cos_sq_density
-- name    : DeepQOperator.cos_sq_density
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:29.33647+00:00
-- url     : https://prove2.me/theorems/20b9f830-0704-4f4c-a23b-d7036f6adc01
-- title:
--   (92)–(93): the cosine-squared density, its score, and its moments
-- statement:
--   For $r>0$ let $f_r(x)=\frac1r\cos^2\!\big(\frac{\pi x}{2r}\big)\mathbf 1\{|x|\le r\}$. Then $f_r\ge0$ and $\int_{\mathbb R}f_r=1$; $f_r$ and its derivative vanish at $\pm r$; $f_r$ is continuously differentiable and compactly supported on $\mathbb R$; on $|x|<r$ it is positive and its score is
--   $$s_r(x)=\frac{f_r'(x)}{f_r(x)}=-\frac{\pi}{r}\tan\Big(\frac{\pi x}{2r}\Big).$$
--   For $X\sim f_r$,
--   $$\mathbb Es_r(X)=0,\qquad I_r:=\mathbb Es_r(X)^2=\frac{\pi^2}{r^2},\qquad\mathbb E[Xs_r(X)]=-1.\tag{93}$$
--
--   These are the densities of the common prior of Appendix D.4; (93) gives its finite score matrix.
--
--   **Formalization Note** The expectations are integrals over $(-r,r)$ against $f_r$. The statement is per radius, so products with different radii per coordinate are covered.
--
--   Differences from the source:
--   - encoding: E over X ∼ f_r → interval integrals over (−r, r) of the integrand times f_r; reason: f_r vanishes outside [−r, r]; the endpoints are null
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix N.1, eqs. (92)–(93), p.55 (PDF p.58)

import Mathlib
import Definitions.Def_DeepQOperator_ScoreMatrix

open MeasureTheory

namespace DeepQOperator

/-- **(92)–(93)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix N.1, p.55, PDF p.58).

For `r > 0`, the cosine-squared density `f_r(x) = (1/r) cos²(πx/(2r)) 1{|x| ≤ r}` is nonnegative and
integrates to one; it and its first derivative vanish at the endpoints `±r`, and extended by zero it
is a continuously differentiable compactly supported function on `ℝ`. On `|x| < r` it is positive and
its score is `s_r = f_r'/f_r = -(π/r) tan(πx/(2r))`. Moreover (93):
`E s_r(X) = 0`, `E s_r(X)² = π²/r²`, `E[X s_r(X)] = -1`.

**Formalization Note.** The expectations in (93) are integrals over `(-r, r)` against `f_r`
(interval integrals); outside `[-r, r]` the density vanishes. The statement is per radius, so products
with different radii per coordinate are covered. -/
theorem cos_sq_density (r : ℝ) (hr : 0 < r) :
    (∀ x, 0 ≤ cosSqDensity r x) ∧ ∫ x, cosSqDensity r x = 1 ∧
    cosSqDensity r r = 0 ∧ cosSqDensity r (-r) = 0 ∧
    deriv (cosSqDensity r) r = 0 ∧ deriv (cosSqDensity r) (-r) = 0 ∧
    ContDiff ℝ 1 (cosSqDensity r) ∧ HasCompactSupport (cosSqDensity r) ∧
    (∀ x, |x| < r → 0 < cosSqDensity r x ∧
      deriv (cosSqDensity r) x / cosSqDensity r x = cosSqScore r x) ∧
    ∫ x in (-r)..r, cosSqScore r x * cosSqDensity r x = 0 ∧
    ∫ x in (-r)..r, cosSqScore r x ^ 2 * cosSqDensity r x = Real.pi ^ 2 / r ^ 2 ∧
    ∫ x in (-r)..r, x * cosSqScore r x * cosSqDensity r x = -1 := by sorry

end DeepQOperator
