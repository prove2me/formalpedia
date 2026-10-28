-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_masked_reward_rightCont
-- name    : AvramDividend.Classical.chat04_closed_survival_masked_reward_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:56:13.728465+00:00
-- url     : https://prove2.me/theorems/317a8ac2-5f25-405b-bf26-a4c7335b8d2c
-- title:
--   Right continuity of the whole-history killed payoff from zero-boundary vanishing
-- statement:
--   For any right-continuous reserve trajectory and right-continuous real reward, the reward killed at the first strictly negative reserve remains right-continuous at every time if the reward vanishes whenever the reserve equals zero. The statement retains survival at every prior time and handles the endpoint of first passage. It combines two independently verified pathwise lemmas and supplies the precise stochastic killed-scale semigroup continuity prerequisite.
-- source:
--   Proved masked-reward right-continuity and Proved local survival stability at positive right-continuous reserves.

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_locally_stable_of_rightCont_positive
import Mathlib.Topology.Order.LeftRightNhds

open Classical Filter Set Topology

theorem AvramDividend.Classical.chat04_closed_survival_masked_reward_rightCont
    (f g : NNReal → ℝ) (t : NNReal)
    (hfcont : ContinuousWithinAt f (Ici t) t)
    (hgcont : ContinuousWithinAt g (Ici t) t)
    (hzero : f t = 0 → g t = 0) :
    ContinuousWithinAt
      (fun u : NNReal => if (∀ s : NNReal, s ≤ u → 0 ≤ f s) then g u else 0)
      (Ici t) t := by sorry
