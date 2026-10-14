-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_distribution_le
-- name    : DbarRegularity.maximalFunction_distribution_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:40:01.193155+00:00
-- url     : https://prove2.me/theorems/a99c459f-87c5-49d6-8ebe-8f9b244a744f
-- title:
--   Distribution bound for the Hardy–Littlewood maximal function by the large values of f
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $m$ is Lebesgue measure. Then for every $f$ and every $\alpha>0$,
--   $$m\{x: Mf(x)>\alpha\}\le\frac{2\cdot5^d}{\alpha}\int_{\{y:\,|f(y)|>\alpha/2\}}|f(y)|\,dy.$$
--
--   This bounds the distribution function of $Mf$ at level $\alpha$ by the integral of $|f|$ over the set where $|f|$ exceeds $\alpha/2$, with a constant depending only on $d$. In this form it applies to every $f$, in particular to $f\in L^p$ with $p>1$, where $f$ need not be integrable.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) takes values in `ℝ≥0∞`; $\alpha$ is in `ℝ≥0`. The right side is the lower integral of `{y | α/2 < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ)`. No measurability or integrability is assumed on $f$. The case $d=0$ is included.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, inequality in the proof of Theorem 1 (c), p. 7

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- Distribution bound for the Hardy–Littlewood maximal function in terms of the large values of `f`:
`|{M f > α}| ≤ (2 · 5^d / α) ∫_{|f| > α/2} |f|` for every `f` and every `α > 0`. -/
theorem maximalFunction_distribution_le (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      2 * (5 : ℝ≥0∞) ^ d / α *
        ∫⁻ x, {y | (α : ℝ≥0∞) / 2 < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) x := by sorry

end DbarRegularity
