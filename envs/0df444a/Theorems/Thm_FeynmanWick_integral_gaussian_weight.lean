-- Prove2me | Theorems.Thm_FeynmanWick_integral_gaussian_weight
-- name    : FeynmanWick.integral_gaussian_weight
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:00:42.72939+00:00
-- url     : https://prove2.me/theorems/3951d648-1252-4d8a-907e-097f6e694958
-- title:
--   Gaussian normalization: $\int e^{-ax^2/2}\,dx = \sqrt{2\pi/a}$
-- statement:
--   For every real $a > 0$ the Gaussian normalization integral is
--
--   $$ I \;=\; \int_{-\infty}^{\infty} e^{-a x^{2}/2}\, dx \;=\; \sqrt{\frac{2\pi}{a}}. $$
--
--   This is the partition function of a single free mode with quadratic action $a x^2/2$; the higher
--   moments of the source's "completing Wick's theorem" computation are obtained from it by
--   differentiating with respect to the parameter $a$.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem integral_gaussian_weight (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * x ^ 2) / 2) = Real.sqrt (2 * Real.pi / a) := by sorry

end FeynmanWick
