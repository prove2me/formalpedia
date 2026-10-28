-- Prove2me | Theorems.Thm_FeynmanKac_discounted_reward_martingale
-- name    : FeynmanKac.discounted_reward_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T08:40:27.286039+00:00
-- url     : https://prove2.me/theorems/76edb6c9-ef7d-4a73-960d-ccb5541ce98f
-- title:
--   Discounted reward of a PDE solution is a true martingale
-- statement:
--   The discounted reward is a true martingale on the Brownian elapsed-time axis, stopped at the terminal horizon and constant for negative elapsed times. This is the correct time-indexed martingale claim: the original unstopped reward is not asserted to be a martingale outside the PDE's terminal interval. Prove it by identifying the reward with the actual discounted-gradient L² Brownian integral and invoking the upstream martingale theorem, including progressive measurability and finite quadratic energy.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Definitions.Def_FeynmanKac_ModelReward
import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.discounted_reward_martingale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u)
    (hdisc : m.AdmissibleDiscountedGradient u) :
    MeasureTheory.Martingale
      (fun r ω => m.discountedReward u
        (m.initialTime + min (max r 0) (m.terminalTime - m.initialTime)) ω)
      m.filtration P := by sorry
