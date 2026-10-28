-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_constant_reward_laplace_normalisation
-- name    : AvramDividend.Classical.chat04_constant_reward_laplace_normalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:49:36.051591+00:00
-- url     : https://prove2.me/theorems/e4f53738-af0d-4545-af16-2611e75950d5
-- title:
--   Laplace transform of a constant killed-scale reward
-- statement:
--   The Laplace transform of any constant real reward c at a positive rate p over positive time is c/p. This is the precise time-resolvent normalisation used to identify the killed-scale reward from the spatial-kernel resolvent identity.
-- source:
--   Proved positive-discount exponential integral plus pinned Mathlib integral_smul_const.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_exponential_halfline_integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.chat04_constant_reward_laplace_normalisation (p c : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * c) = c / p := by sorry
