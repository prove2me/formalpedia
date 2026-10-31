-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:50:54.20352+00:00
-- url     : https://prove2.me/theorems/cabd9048-3ed7-4b7a-8053-a93c3b11b093
-- title:
--   Uniform high-barrier dividend-value decay over every bounded set of nonnegative reserves
-- statement:
--   For each finite nonnegative reserve cap R, the supremum over all starting capital x in [0,R] of genuine expected discounted Stieltjes dividends under the constant-barrier strategy tends to zero as the payout barrier a tends to infinity, under the Standing hypotheses and positive discount. Monotonicity in starting capital bounds every value on [0,R] by the value at R+1>0, whose high-barrier limit is already Proved. This strengthens pointwise convergence to uniform convergence on bounded reserve intervals without global C1 regularity.
-- source:
--   Avram Palmowski Pistorius (2007), true constant-barrier stochastic value and monotonicity, original Lévy q-scale Esscher high-barrier decay.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_high_barrier_value_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun a : ℝ =>
      ⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a))
      atTop (𝓝 (0 : ENNReal)) := by sorry
