-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_ennreal_rightContinuous_killed_reward_of_zero_boundary
-- name    : AvramDividend.Classical.chat04_ennreal_rightContinuous_killed_reward_of_zero_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:48:58.612709+00:00
-- url     : https://prove2.me/theorems/59cb0117-f6c9-403b-9ca8-af35aa7a6fc8
-- title:
--   Extended-nonnegative killed rewards inherit right-continuity across zero-boundary killing
-- statement:
--   A right-continuous real reward, killed when the history-survival predicate fails, remains right-continuous after passing to the extended nonnegative payoff used in the Lebesgue expectation. The survival predicate is locally stable whenever its reward is nonzero, and its complement is locally stable after failure. This is the pointwise topological ingredient for dominated convergence of killed expectations.
-- source:
--   Accepted masked real reward continuity theorem 16064; Mathlib ENNReal.continuous_ofReal.

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.chat04_ennreal_rightContinuous_killed_reward_of_zero_boundary
    (g : NNReal → ℝ) (S : NNReal → Prop) [DecidablePred S] (t : NNReal)
    (hg : ContinuousWithinAt g (Set.Ici t) t)
    (hsafe : S t → g t ≠ 0 → ∀ᶠ s in 𝓝[Set.Ici t] t, S s)
    (hunsafe : ¬ S t → ∀ᶠ s in 𝓝[Set.Ici t] t, ¬ S s) :
    ContinuousWithinAt
      (fun s => ENNReal.ofReal (if S s then g s else 0))
      (Set.Ici t) t := by sorry
