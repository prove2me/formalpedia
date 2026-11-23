-- Prove2me | Theorems.Thm_BroughanRH_baezDuarteConvolution
-- name    : BroughanRH.baezDuarteConvolution
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:40.4398+00:00
-- url     : https://prove2.me/theorems/55cb1f9d-6ef5-484c-876f-4f786c6aee66
-- title:
--   Báez-Duarte’s multiplicative-convolution bound
-- statement:
--   The multiplicative convolution of the weighted Möbius sum with a continuous test function is $O_\varepsilon(x^{-1/2+\varepsilon})$ under the stated integrability and nonvanishing Mellin conditions.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 2.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem baezDuarteConvolution :
    let g (t : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius n : ℝ) / n
    ∀ f : ℝ → ℂ, ContinuousOn f (Set.Ioi 0) →
      (∀ σ : ℝ, -(1/2) < σ → σ ≤ 0 → MeasureTheory.IntegrableOn (fun t : ℝ => t^(-σ-1)*‖f t‖) (Set.Ioi 0)) →
      (∀ s : ℂ, -(1/2) < s.re → s.re < 0 → (∫ t in Set.Ioi (0 : ℝ), (t : ℂ)^(-s-1)*f t) ≠ 0) →
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => ∫ t in Set.Ioi (0 : ℝ), ((g (x*t) / t : ℝ) : ℂ) * f (1/t))
        (fun x : ℝ => x^(-(1/2)+ε)) := by sorry

end BroughanRH
