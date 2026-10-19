-- Prove2me | Theorems.Thm_CauchyRiemannIndex_gaussian_poincare_rectangle
-- name    : CauchyRiemannIndex.gaussian_poincare_rectangle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T13:37:13.400774+00:00
-- url     : https://prove2.me/theorems/f06a6d66-9524-42fd-b303-ec8d7566527d
-- title:
--   Gaussian Poincaré inequality on a rectangle centred at the Gaussian's centre
-- statement:
--   Let $\sigma>0$, let $a,b\in\mathbb R$ and $L,M>0$, and let
--   $$Q=[a-L,a+L]\times[b-M,b+M]\subset\mathbb R^2,\qquad w(s,t)=e^{-\sigma\left((s-a)^2+(t-b)^2\right)}.$$
--   For every $C^1$ function $g:\mathbb R^2\to\mathbb R$ there is a constant $c\in\mathbb R$ such that
--   $$\int_Q (g-c)^2\,w\,ds\,dt\;\le\;\frac{8}{\sigma}\int_Q\big((\partial_s g)^2+(\partial_t g)^2\big)\,w\,ds\,dt .$$
--
--   This is a Poincaré inequality for the Gaussian weight restricted to a rectangle centred at the centre of the Gaussian, with a constant of order $1/\sigma$ that does not depend on the size of the rectangle. It controls the spectral gap of the two-dimensional harmonic oscillator $-\Delta+\sigma^2|z|^2$ above its ground state, for functions supported in a fixed rectangle.
--
--   **Formalization Note.** The rectangle is `Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M)` with Lebesgue measure on `ℝ × ℝ`; the partial derivatives are `fderiv ℝ g x (1, 0)` and `fderiv ℝ g x (0, 1)`, and `g` is assumed `ContDiff ℝ 1`.
-- source:
--   Classical Gaussian Poincaré inequality (cf. D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators, Springer 2014, §4.1), here on a rectangle with the weight centred at its centre; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 5, Lemma 5.22

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Set Real

/-- Gaussian Poincaré inequality on a rectangle. Let `σ > 0`, let
`Q = [a - L, a + L] × [b - M, b + M]` with `L, M > 0`, and let `w(s, t) = exp(-σ((s-a)² + (t-b)²))`
be the Gaussian weight centred at the centre of `Q`. Every `C¹` function `g` on `ℝ²` admits a
constant `c` with `∫_Q (g - c)² w ≤ (8/σ) ∫_Q |∇g|² w`. -/
theorem gaussian_poincare_rectangle (σ : ℝ) (hσ : 0 < σ) (a b L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ c : ℝ, ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        (g x - c) ^ 2 * exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) ≤
      8 / σ * ∫ x in Icc (a - L) (a + L) ×ˢ Icc (b - M) (b + M),
        ((fderiv ℝ g x (1, 0)) ^ 2 + (fderiv ℝ g x (0, 1)) ^ 2) *
          exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) := by
  sorry

end CauchyRiemannIndex
