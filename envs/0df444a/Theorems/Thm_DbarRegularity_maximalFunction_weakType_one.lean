-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_weakType_one
-- name    : DbarRegularity.maximalFunction_weakType_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:24:43.612383+00:00
-- url     : https://prove2.me/theorems/d86ee034-b84a-4b77-8948-34dfc04e585d
-- title:
--   Weak type (1,1) bound for the Hardy–Littlewood maximal function with constant 5^d
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure $m$. Then for every $f$ and every $\alpha>0$,
--   $$m\{x: Mf(x)>\alpha\}\le\frac{5^d}{\alpha}\int_{\mathbb{R}^d}|f(y)|\,dy.$$
--
--   This is the weak type $(1,1)$ inequality of the Hardy–Littlewood maximal theorem, with an explicit constant depending only on the dimension.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) takes values in `ℝ≥0∞`, and $\alpha$ is in `ℝ≥0`. No measurability or integrability is assumed on $f$: the left side is the outer Lebesgue measure of the superlevel set, and the right side is the lower Lebesgue integral `∫⁻ x, ‖f x‖ₑ`, which is $+\infty$ when $f\notin L^1$ (the bound is then trivial). The case $d=0$ is included.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (b), p. 5, with the constant A = 5^d noted there

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- Weak type `(1,1)` bound for the Hardy–Littlewood maximal function on `ℝ^d` with the explicit
constant `5^d`: `|{M f > α}| ≤ (5^d / α) ∫ |f|` for every `f` and every `α > 0`. -/
theorem maximalFunction_weakType_one (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ x, ‖f x‖ₑ := by sorry

end DbarRegularity
