-- Prove2me | Theorems.Thm_FeynmanKac_constant_discount_representation
-- name    : FeynmanKac.constant_discount_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:08:21.023836+00:00
-- url     : https://prove2.me/theorems/19d7dc5c-886f-45c8-8b76-d3b7e7ba6012
-- title:
--   Feynman–Kac with constant discount rate
-- statement:
--   When the potential \(V\) equals a nonnegative constant \(r\), pathwise discounting becomes deterministic: \(D_{t,s}=e^{-r(s-t)}\). The representation then gives the familiar discounted terminal payoff and discounted running cashflow formula. This is a useful bridge towards risk-neutral valuation and present-value calculations.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.constant_discount_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (r : ℝ) (hr : 0 ≤ r) (hV : ∀ x s, m.potential x s = r)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, (Real.exp (-(r * (m.terminalTime - m.initialTime))) *
          m.terminalPayoff (m.path m.terminalTime ω) +
        ∫ s in m.initialTime..m.terminalTime,
          Real.exp (-(r * (s - m.initialTime))) *
            m.runningSource (m.path s ω) s) ∂P := by sorry
