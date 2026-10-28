-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
-- name    : AvramDividend.Classical.chat04_rightContinuous_masked_reward_of_zero_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:31:35.6505+00:00
-- url     : https://prove2.me/theorems/da5b96c6-460e-4d59-bd39-ae189f5c35d1
-- title:
--   Right continuity of a killed reward at vanishing survival boundaries
-- statement:
--   A real-valued reward that is right-continuous at a given time remains right-continuous when multiplied by a Boolean survival mask, provided the mask is eventually stable whenever the reward at the time is nonzero. If the reward is zero, right-continuity holds without any mask stability. This isolates the zero-origin scale function argument needed for stopped killed-scale semigroup continuity.
-- source:
--   Mathlib Filter.Tendsto.if' and congr' with the right-neighbourhood filter; zero-boundary masking argument.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

open Filter Topology

theorem AvramDividend.Classical.chat04_rightContinuous_masked_reward_of_zero_boundary
    (g : NNReal → ℝ) (S : NNReal → Prop) [DecidablePred S] (t : NNReal)
    (hg : ContinuousWithinAt g (Set.Ici t) t)
    (hsafe : S t → g t ≠ 0 → ∀ᶠ s in 𝓝[Set.Ici t] t, S s)
    (hunsafe : ¬ S t → ∀ᶠ s in 𝓝[Set.Ici t] t, ¬ S s) :
    ContinuousWithinAt (fun s => if S s then g s else 0) (Set.Ici t) t := by sorry
