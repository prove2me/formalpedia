-- Prove2me | Theorems.Thm_BanditAlgorithm_integral_exp_quadratic
-- name    : BanditAlgorithm.integral_exp_quadratic
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:48:47.524092+00:00
-- url     : https://prove2.me/theorems/7377ac54-ce46-45da-a56c-437baa04a3ce
-- title:
--   Gaussian integral with a linear term
-- statement:
--   The Gaussian integral with a linear term: for $a>0$ and any $c\in\mathbb R$,
--   $$\int_{\mathbb R}e^{-ax^2+cx}\,dx=\sqrt{\frac{\pi}{a}}\;e^{c^2/(4a)}.$$
--
--   Mathlib has the pure Gaussian integral $\int e^{-bx^2}=\sqrt{\pi/b}$ but not this completed-square version, which is what every method-of-mixtures computation needs. The proof completes the square, $-ax^2+cx=-a\bigl(x-\tfrac{c}{2a}\bigr)^2+\tfrac{c^2}{4a}$, and uses translation invariance of Lebesgue measure.
-- source:
--   Standard: the Gaussian integral with a linear term, obtained from the pure Gaussian integral by completing the square. Absent from Mathlib.

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Real

theorem BanditAlgorithm.integral_exp_quadratic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2 + c * x)
      = Real.sqrt (Real.pi / a) * Real.exp (c ^ 2 / (4 * a)) := by
  sorry
