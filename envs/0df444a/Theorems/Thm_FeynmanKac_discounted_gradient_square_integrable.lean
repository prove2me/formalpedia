-- Prove2me | Theorems.Thm_FeynmanKac_discounted_gradient_square_integrable
-- name    : FeynmanKac.discounted_gradient_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:11:20.36756+00:00
-- url     : https://prove2.me/theorems/4d22bfa2-2859-464e-aab6-0f6c4a8ddc7b
-- title:
--   Square integrability of the discounted diffusion gradient
-- statement:
--   For a bounded clock-augmented diffusion with nonnegative discount rate and bounded volatility, a jointly C¹-in-time, C²-in-space candidate function whose spatial derivative is uniformly bounded on the finite horizon has a measurable discounted Brownian-gradient integrand with finite expected quadratic energy. The C¹,² hypothesis supplies joint continuity and hence the required measurability; a bounded derivative alone is insufficient for arbitrary time-dependent functions. The conclusion is the finite-energy predicate, not a martingale or stochastic-integral representation identity.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.discounted_gradient_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (huC12 : m.IsC12 u)
    (hu : m.BoundedSpatialGradient u) :
    m.SquareIntegrableDiscountedGradient u := by sorry
