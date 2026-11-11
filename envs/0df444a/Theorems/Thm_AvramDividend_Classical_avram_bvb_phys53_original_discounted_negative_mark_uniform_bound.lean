-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
-- name    : AvramDividend.Classical.avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:31:35.135028+00:00
-- url     : https://prove2.me/theorems/cf0d73ae-ae85-43b2-a443-c5813db06cd3
-- title:
--   Discounted negative-mark reward is uniformly bounded below any finite cap
-- statement:
--   For a nonnegative discount rate, a continuous nonnegative-reserve reward function that vanishes below zero, and any finite reserve cap, all discounted negative jump reward differences from pre-states between zero and cap share a single finite absolute bound.
-- source:
--   Proved df040a51 gives compact-cap upper and lower payoff bound; positivity of the discount and the fact that a negative mark lowers pre-reserve yield a uniform bound. Required for Open 2dcecdd4 and 9a6793e4, then BV physical source 4f605d76.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t u z : ℝ), 0 ≤ t → 0 ≤ u → ENNReal.ofReal u ≤ C → z < 0 →
        |Real.exp (-(q * t)) * (w (u + z) - w u)| ≤ K := by sorry
