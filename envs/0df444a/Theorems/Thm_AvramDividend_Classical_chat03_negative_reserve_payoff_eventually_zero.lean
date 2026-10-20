-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_negative_reserve_payoff_eventually_zero
-- name    : AvramDividend.Classical.chat03_negative_reserve_payoff_eventually_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:46:33.598983+00:00
-- url     : https://prove2.me/theorems/2c3bf6a5-63cf-4c01-9d6a-48f685ff1685
-- title:
--   Discounted stopped scale payoffs eventually vanish at strictly negative right-limit reserves
-- statement:
--   If sampled times tend to a stopping time from the right and the limiting reserve is strictly below zero, the right-continuity of the Levy sample path forces sufficiently late sampled reserves to remain negative. Since the official q-scale function vanishes on negative reserves, the corresponding discounted scale payoffs are eventually identically zero regardless of the choice of discount. This handles the negative reserve branch without assuming continuity of W across zero.
-- source:
--   Derived directly from the official IsScaleFunction zero-left property and SpectrallyNegativeLevy right-continuity, using pinned Mathlib filter neighbourhood convergence. This is an independent pathwise bridge, not a killed martingale theorem.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_negative_reserve_payoff_eventually_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ)
    (hnegative : x + X.X τ ω < 0) :
    ∀ᶠ n : ℕ in atTop,
      discount (clock n) * W (x + X.X (clock n) ω) = 0 := by sorry
