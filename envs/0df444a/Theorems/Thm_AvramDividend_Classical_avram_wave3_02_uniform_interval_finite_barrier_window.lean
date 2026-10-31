-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_interval_finite_barrier_window
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_interval_finite_barrier_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:43:00.310988+00:00
-- url     : https://prove2.me/theorems/ea1cc10e-fd9f-4b85-ba01-bfee4de48aa5
-- title:
--   A single finite cap window determines best genuine barrier dividends across positive bounded capital ranges
-- statement:
--   For any fixed positive reserve lower bound delta and upper bound R, there is a single finite nonnegative payout barrier threshold A such that the supremum of actual source discounted Stieltjes dividends over every nonnegative constant barrier equals the supremum restricted to 0≤barrier≤A, simultaneously for every starting surplus x in [delta,R]. Uses the canonically Proved uniform high-barrier zero-cap dominance and complete-lattice supremum rules; it makes no claim of attainment or all-admissible-strategy optimality.
-- source:
--   Avram Palmowski Pistorius (2007), original constant-barrier dividend strategy, source-uniform high-barrier strict dominance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_capital_interval_high_barrier_dominated

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_interval_finite_barrier_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, δ ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by sorry
