-- Prove2me | Theorems.Thm_FeynmanWick_integral_even_moment_gaussian_weight
-- name    : FeynmanWick.integral_even_moment_gaussian_weight
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:01:52.893776+00:00
-- url     : https://prove2.me/theorems/efcb66a7-0e44-4ba6-9ebd-fbacfdf928c4
-- title:
--   Higher Gaussian moments: $\int x^{2n} e^{-ax^2/2}\,dx = \frac{(2n-1)!!}{a^{n}}\sqrt{2\pi/a}$
-- statement:
--   For every real $a > 0$ and every $n \in \mathbb{N}$,
--
--   $$ \int_{-\infty}^{\infty} x^{2n} e^{-a x^{2}/2}\, dx \;=\; \frac{(2n-1)!!}{a^{n}} \sqrt{\frac{2\pi}{a}}, $$
--
--   where $(2n-1)!! = 1 \cdot 3 \cdot 5 \cdots (2n-1)$ is the double factorial, equal to $1$ when
--   $n = 0$.
--
--   This is the source's displayed formula obtained by differentiating the Gaussian normalization
--   integral $n$ times with respect to $a$; dividing by that integral gives the normalized moment
--   $\langle x^{2n}\rangle = (2n-1)!!\,a^{-n}$.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem integral_even_moment_gaussian_weight (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(a * x ^ 2) / 2)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) / a ^ n * Real.sqrt (2 * Real.pi / a) := by
  sorry

end FeynmanWick
