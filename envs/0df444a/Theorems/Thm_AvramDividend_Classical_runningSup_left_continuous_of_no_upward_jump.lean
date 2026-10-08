-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump
-- name    : AvramDividend.Classical.runningSup_left_continuous_of_no_upward_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T23:24:48.491372+00:00
-- url     : https://prove2.me/theorems/cc07976a-d7ac-4c47-8059-656907abf229
-- title:
--   Monotone running supremum inherits left continuity from absence of upward jumps
-- statement:
--   Let M be a nondecreasing running supremum of a real-valued path f on nonnegative times, and assume f(u) is everywhere at most M(u). At a positive time t, if f has a finite left limit ℓ and f(t)≤ℓ (no upward jump), then M is continuous from the left at t. Earlier path values lie below the left limit of M by monotonicity; f(t) also does, by the left limit of f. Thus all terms of the running supremum are below the left limit, forcing equality and left continuity.
-- source:
--   General real-order lemma for the spectrally negative Levy barrier dividend strategy. Uses Mathlib Monotone.le_leftLim, leftLim_le and continuousWithinAt_Iio_iff_leftLim_eq. Independent of Prove2Me mission-specific imports.

import Mathlib

open Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_left_continuous_of_no_upward_jump (f M : ℝ≥0 → ℝ)
    (hM : Monotone M)
    (hdom : ∀ u, f u ≤ M u)
    (hrepr : ∀ t, M t =
      ⨆ u : Set.Icc (0 : ℝ≥0) t, f u.1)
    (t : ℝ≥0) (ht : 0 < t) (ℓ : ℝ)
    (hfLeft : Tendsto f (𝓝[<] t) (𝓝 ℓ))
    (hNoUp : f t ≤ ℓ) :
    ContinuousWithinAt M (Iio t) t := by
  sorry
