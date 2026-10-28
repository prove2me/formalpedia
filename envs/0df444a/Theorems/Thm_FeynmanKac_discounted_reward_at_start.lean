-- Prove2me | Theorems.Thm_FeynmanKac_discounted_reward_at_start
-- name    : FeynmanKac.discounted_reward_at_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:52:38.194662+00:00
-- url     : https://prove2.me/theorems/1cb8b4b1-0531-410a-b922-fed5b968173b
-- title:
--   The discounted reward process equals the candidate solution at its starting time
-- statement:
--   At the initial time, the pathwise discount is one and the accumulated running-payment integral vanishes. Thus the discounted reward process starts at the deterministic candidate solution evaluated at the initial state. This identity is pathwise, requires no stochastic assumptions and is a direct endpoint input to the martingale-to-expectation implication.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Definitions.Def_FeynmanKac_PathDiscount
import Definitions.Def_FeynmanKac_DiscountedReward
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.discounted_reward_at_start
    {Ω : Type*} (X : ℝ → Ω → ℝ)
    (V u f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) :
    FeynmanKac.discountedReward X V u f t t ω = u (X t ω) t := by sorry
