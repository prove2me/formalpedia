-- Prove2me | Theorems.Thm_FeynmanKac_heat_terminal_representation
-- name    : FeynmanKac.heat_terminal_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:00:26.684315+00:00
-- url     : https://prove2.me/theorems/2afd22f8-d0fd-432b-8a13-761258b7ef9d
-- title:
--   Heat equation as a Brownian expectation
-- statement:
--   For a genuine one-dimensional Brownian diffusion in the published model, suppose its drift vanishes everywhere, volatility equals one everywhere, potential is zero and the running source is zero. If u is a bounded classical solution of the resulting backward heat equation with the prescribed terminal payoff and its discounted Brownian-gradient term satisfies the model's finite-energy condition, then its initial value equals the expected terminal payoff under the diffusion's probability law. This is a specialisation of the intended full Feynman–Kac representation, not a stochastic identity inserted into the model.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.heat_terminal_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsClassicalPDESolution u)
    (hμ : ∀ x s, m.drift x s = 0)
    (hσ : ∀ x s, m.volatility x s = 1)
    (hV : ∀ x s, m.potential x s = 0)
    (hf : ∀ x s, m.runningSource x s = 0)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, m.terminalPayoff (m.path m.terminalTime ω) ∂P := by sorry
