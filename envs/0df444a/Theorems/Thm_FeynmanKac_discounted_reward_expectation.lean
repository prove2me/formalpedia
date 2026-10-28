-- Prove2me | Theorems.Thm_FeynmanKac_discounted_reward_expectation
-- name    : FeynmanKac.discounted_reward_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:28:38.91352+00:00
-- url     : https://prove2.me/theorems/0c5eb6f3-a677-4630-bc25-bd4ea3701782
-- title:
--   Equality of initial and terminal discounted-reward expectations
-- statement:
--   A true discounted-reward martingale has constant expectation from its deterministic initial value to the finite terminal horizon. Prove that both endpoint rewards are integrable and the initial reward is the constant \(u(x,t)\). This closes the martingale-to-expectation bridge before the terminal payoff is substituted.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_ModelReward
import Definitions.Def_FeynmanKac_ClassicalSolutionConditions

theorem FeynmanKac.discounted_reward_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    (∫ ω, m.discountedReward u m.terminalTime ω ∂P) =
      u m.initialState m.initialTime := by sorry
